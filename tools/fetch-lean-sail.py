#!/usr/bin/env python3
# Copyright (c) 2026 Crocodile Labs Inc.
# SPDX-License-Identifier: Apache-2.0
"""Materialize the pinned runtime using source-coordinate edits."""
import argparse
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor/lean-sail"
REVISION = "c816ea7ad03cce98d51acee252540fd4215fede8"
TREE = "dec6a0e5c2f7025517cdaddf02bdf550e3acab04"
URL = "https://github.com/rems-project/lean-sail"


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def check_hash(data, expected, label):
    require(sha256(data).hexdigest() == expected, f"SHA256 mismatch: {label}")


def checked_path(path):
    require(re.fullmatch(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*", path)
            and all(part not in (".", "..") for part in path.split("/")),
            f"invalid path: {path}")
    return path


def read_file(path):
    require(not path.is_symlink() and path.is_file(), f"missing or invalid file: {path.name}")
    return path.read_bytes()


def safe_dir(path):
    require(not path.is_symlink() and path.is_dir(), f"invalid directory: {path}")


def inventory(expected):
    dirs = {part for name in expected for part in PurePosixPath(name).parents}
    found = set()
    for root, subdirs, filenames in os.walk(VENDOR):
        for name in subdirs[:]:
            entry = Path(root) / name
            safe_dir(entry)
            rel = PurePosixPath(entry.relative_to(VENDOR))
            if rel.as_posix() == ".lake":
                subdirs.remove(name)
            else:
                require(rel in dirs, f"unexpected directory: {rel}")
        for name in filenames:
            entry = Path(root) / name
            rel = entry.relative_to(VENDOR).as_posix()
            require(rel in expected, f"unexpected file: {rel}")
            require(not entry.is_symlink() and entry.is_file(), f"invalid file: {rel}")
            found.add(rel)
    return found


def git(repo, *args):
    return subprocess.check_output(
        ["git", "-C", str(repo), "-c", "core.hooksPath=/dev/null", *args]
    )


def fetch(mirror, stage, pins):
    clone = stage / "upstream"
    git(stage, "clone", "--quiet", "--no-checkout", "--", mirror, str(clone))
    try:
        tree = git(clone, "rev-parse", "--verify", REVISION + "^{tree}")
    except subprocess.CalledProcessError:
        git(clone, "fetch", "--no-tags", "origin", REVISION)
        tree = git(clone, "rev-parse", "--verify", REVISION + "^{tree}")
    require(tree.decode().strip() == TREE, "upstream Git tree differs from pin")
    original = {}
    for path, expected in pins.items():
        data = git(clone, "show", f"{REVISION}:{checked_path(path)}")
        check_hash(data, expected, path)
        original[path] = data
    return original


def copy_bytes(source, start, length):
    require(type(start) is int and type(length) is int
            and 0 <= start <= start + length <= len(source), "invalid copy range")
    return source[start:start + length]


def replacement(parts, old_slice, upstream):
    for part in parts:
        if isinstance(part, str):
            yield part.encode("utf-8")
        elif len(part) == 2:
            yield copy_bytes(old_slice, *part)
        else:
            path, start, length = part
            yield copy_bytes(upstream[path], start, length)


def apply_edits(tree, changes, upstream):
    for change in changes:
        path = checked_path(change["path"])
        before, after = change["before"], change["after"]
        if before is None:
            require(path not in tree, f"edit expects absent path: {path}")
            original = b""
        else:
            original = tree[path]
            check_hash(original, before, path)
        lines = original.splitlines(keepends=True)
        cursor = 0
        result = []
        for start, length, digest, parts in change["edits"]:
            require(type(start) is int and type(length) is int
                    and cursor <= start <= start + length <= len(lines),
                    f"invalid edit line range: {path}")
            old_slice = b"".join(lines[start:start + length])
            check_hash(old_slice, digest, f"{path} line {start + 1}")
            result.extend(lines[cursor:start])
            result.extend(replacement(parts, old_slice, upstream))
            cursor = start + length
        result.extend(lines[cursor:])
        updated = b"".join(result)
        if after is None:
            require(not updated, f"deleted file is nonempty: {path}")
            del tree[path]
        else:
            check_hash(updated, after, path)
            tree[path] = updated


def reconstruct(stage, mirror, manifest, edits, bootstrap, expected):
    pins = manifest["upstream_files"]
    upstream = fetch(mirror, stage, pins | manifest["reference_files"])
    tree = {path: upstream[path] for path in pins}
    stages = edits["stages"]
    require([entry["name"] for entry in stages] == ["0001", "0002", "v9"],
            "unexpected edit stages")
    for entry in stages:
        apply_edits(tree, entry["files"], upstream)
        if entry["name"] == "0002":
            legacy = manifest["legacy_output"]
            require(tree.keys() == legacy.keys(), "legacy output inventory mismatch")
            for path, digest in legacy.items():
                check_hash(tree[path], digest, f"legacy {path}")
    first_party = set(bootstrap) - tree.keys()
    require(first_party == set(manifest["new_first_party_files"]),
            "first-party runtime inventory mismatch")
    for path in first_party:
        tree[path] = read_file(VENDOR / path)
    require(tree.keys() == expected.keys(), "output inventory mismatch")
    for path, data in tree.items():
        check_hash(data, expected[path], path)
    return tree


def install(tree, bootstrap):
    created = []
    try:
        for path in sorted(tree.keys() - bootstrap):
            dest = VENDOR / path
            dest.parent.mkdir(parents=True, exist_ok=True)
            with dest.open("xb") as handle:
                created.append(dest)
                handle.write(tree[path])
    except BaseException:
        for dest in reversed(created):
            dest.unlink()
        tests = VENDOR / "SailTests"
        if tests.is_dir() and not any(tests.iterdir()):
            tests.rmdir()
        raise


def materialize(mirror, cache):
    manifest = json.loads(read_file(VENDOR / "UPSTREAM.json"))
    require(manifest["schema"] == "isawitness-runtime-edit-overlay-v3"
            and manifest["upstream"] == {"url": URL, "commit": REVISION, "tree": TREE},
            "unexpected runtime manifest schema or upstream pin")
    raw_edits = read_file(VENDOR / "edits.json")
    check_hash(raw_edits, manifest["edits_sha256"], "edits.json")
    edits = json.loads(raw_edits)
    require(edits["schema"] == "isawitness-source-edits-v1", "unexpected edit schema")

    entries = manifest["sources"] + manifest["configuration"]
    expected = {checked_path(entry["path"]): entry["sha256"] for entry in entries}
    require(len(expected) == len(entries), "duplicate output path")
    bootstrap = set(manifest["bootstrap_files"])
    metadata = {"UPSTREAM.json", "edits.json"}
    have = inventory(expected.keys() | metadata)
    for path in bootstrap:
        check_hash(read_file(VENDOR / path), expected[path], path)
    if have - bootstrap - metadata:
        require(have == expected.keys() | metadata, "incomplete existing runtime payload")
        for path, digest in expected.items():
            check_hash(read_file(VENDOR / path), digest, path)
        print("lean-sail: existing source payload is complete and SHA256 verified")
        return
    with tempfile.TemporaryDirectory(prefix="lean-sail-fetch-", dir=cache) as tmp:
        tree = reconstruct(Path(tmp), mirror, manifest, edits, bootstrap, expected)
        install(tree, bootstrap)
    print(f"lean-sail: verified upstream {REVISION}, both legacy edit stages and the v9 runtime")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", default=os.environ.get("ISAWITNESS_LEAN_SAIL_SOURCE", URL))
    args = parser.parse_args()
    try:
        safe_dir(VENDOR.parent)
        safe_dir(VENDOR)
        cache = ROOT / ".lake"
        cache.mkdir(exist_ok=True)
        safe_dir(cache)
        flags = os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW
        with os.fdopen(os.open(cache / "lean-sail-fetch.lock", flags, 0o600), "r+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            materialize(args.source, cache)
    except (KeyError, TypeError, ValueError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"fetch-lean-sail: {exc}\n")


if __name__ == "__main__":
    main()

#!/usr/bin/env bash
set -euo pipefail
PROVIDER_SOURCE_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PROVIDER_BUILD_UNIT="provider-cold-$(python3 -c 'import uuid; print(uuid.uuid4().hex)')"
[[ "$(systemctl --user show fleet.slice -p ActiveState --value)" == active ]]
[[ "$(systemctl --user show fleet.slice -p MemoryMax --value)" == 118111600640 ]]
[[ "$(systemctl --user show fleet.slice -p MemorySwapMax --value)" == 0 ]]
cleanup_provider_job() {
  systemctl --user stop "$PROVIDER_BUILD_UNIT" >/dev/null 2>&1 || true
}
trap cleanup_provider_job EXIT
trap 'exit 130' INT TERM
systemd-run --user --wait --collect --pipe \
  --unit "$PROVIDER_BUILD_UNIT" --slice fleet.slice \
  -p MemorySwapMax=0 -p Nice=19 -p RuntimeMaxSec=600 \
  --working-directory "$PROVIDER_SOURCE_DIR" \
  --setenv="PATH=$PATH" \
  --setenv="LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-40}" \
  --setenv=LAKE_ARTIFACT_CACHE=false \
  --setenv=LAKE_RESTORE_ARTIFACTS=false \
  python3 tools/check-complete-workspace.py "$@"

"""Position-preserving Lean source masking; interpolated expressions remain code."""
import re
_DELIM = re.compile(r"""--|/-|r#*"|"|'(?:[^'\\\n]|\\(?:u\{[0-9a-fA-F]+\}|[^\n]))'""")
_BLOCK = re.compile('/-|-/')

def mask_noncode(text):
    out = list(text)
    n = len(text)

    def blank(a, b):
        out[a:b] = ['\n' if c == '\n' else '\r' if c == '\r' else ' ' for c in text[a:b]]

    def string(i, opening, hashes=None, interpolated=False):
        blank(i, i + opening)
        i += opening
        while i < n:
            if hashes is not None:
                end = text.find('"' + '#' * hashes, i)
                if end < 0:
                    blank(i, n)
                    return n
                blank(i, end + 1 + hashes)
                return end + 1 + hashes
            c = text[i]
            if c == '\\':
                blank(i, min(n, i + 2))
                i += 2
                continue
            if c == '"':
                blank(i, i + 1)
                return i + 1
            if interpolated and c == '{':
                if text.startswith('{{', i):
                    blank(i, i + 2)
                    i += 2
                    continue
                blank(i, i + 1)
                i = code(i + 1, True)
                continue
            blank(i, i + 1)
            i += 1
        return i

    def code(i, close_brace=False):
        while i < n:
            if close_brace and text[i] == '}':
                blank(i, i + 1)
                return i + 1
            if close_brace and text[i] == '{':
                i = code(i + 1, True)
                continue
            m = _DELIM.search(text, i)
            # A closing interpolation brace may precede the next delimiter.
            if close_brace:
                b = text.find('}', i)
                a = text.find('{', i)
                choices = [v for v in [a, b] if v >= 0]
                if choices and (m is None or min(choices) < m.start()):
                    i = min(choices)
                    continue
            if m is None:
                return n
            i = m.start()
            token = m.group()
            if token == '--':
                end = text.find('\n', i)
                end = n if end < 0 else end
                blank(i, end)
                i = end
            elif token == '/-':
                start = i
                depth = 1
                i += 2
                while depth and i < n:
                    b = _BLOCK.search(text, i)
                    if b is None:
                        i = n
                        break
                    depth += 1 if b.group() == '/-' else -1
                    i = b.end()
                blank(start, i)
            elif token.startswith('r'):
                if i and (text[i - 1].isalnum() or text[i - 1] in "_'»"):
                    # An identifier's trailing r is not a raw-string prefix.
                    i = string(i + len(token) - 1, 1, interpolated=False)
                else:
                    i = string(i, len(token), hashes=len(token) - 2)
            elif token == '"':
                interpolated = i > 0 and text[i - 1] == '!'
                i = string(i, 1, interpolated=interpolated)
            else:
                # Apostrophes in identifiers such as state' remain code.
                if i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'»"):
                    blank(i, m.end())
                i = m.end()
        return i
    code(0)
    return ''.join(out)

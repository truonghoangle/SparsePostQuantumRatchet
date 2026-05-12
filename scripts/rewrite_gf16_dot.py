#!/usr/bin/env python3
"""Rewrite `GF16.toGF216 X` to `X.toGF216` (Lean dot-notation), except where
the identifier is referenced as a function name in `simp [...]`/`unfold` lemma
lists.
"""
import sys


def find_arg(text, start):
    i = start
    n = len(text)
    if i >= n:
        return None
    if text[i] == '(':
        depth = 1
        i += 1
        while i < n and depth > 0:
            c = text[i]
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            i += 1
        # trailing .field
        while i < n and text[i] == '.':
            j = i + 1
            if j < n and (text[j].isalpha() or text[j] == '_' or text[j].isdigit()):
                i = j
                while i < n and (text[i].isalnum() or text[i] in "_'"):
                    i += 1
            else:
                break
        return (i, text[start:i])
    elif text[i].isalpha() or text[i] == '_':
        while i < n:
            c = text[i]
            if c.isalnum() or c in "_'":
                i += 1
            elif c == '.' and i + 1 < n and (text[i+1].isalpha() or text[i+1] == '_' or text[i+1].isdigit()):
                i += 1
            else:
                break
        # optional indexing: [...]! possibly followed by .field, repeatable
        while i < n and text[i] == '[':
            depth = 1
            i += 1
            while i < n and depth > 0:
                c = text[i]
                if c == '[':
                    depth += 1
                elif c == ']':
                    depth -= 1
                i += 1
            if i < n and text[i] == '!':
                i += 1
            while i < n and text[i] == '.':
                j = i + 1
                if j < n and (text[j].isalpha() or text[j] == '_' or text[j].isdigit()):
                    i = j
                    while i < n and (text[i].isalnum() or text[i] in "_'"):
                        i += 1
                else:
                    break
        return (i, text[start:i])
    else:
        return None


def process_text(text):
    needle = "GF16.toGF216 "
    out = []
    i = 0
    n = len(text)
    while i < n:
        idx = text.find(needle, i)
        if idx == -1:
            out.append(text[i:])
            break

        line_start = text.rfind('\n', 0, idx) + 1
        line_prefix = text[line_start:idx]
        stripped = line_prefix.strip()
        skip = False
        # tactic `unfold GF16.toGF216 ...`
        if stripped == 'unfold' or stripped.endswith(' unfold') or ' unfold ' in (' ' + stripped + ' ') or stripped.startswith('unfold '):
            # Actually we already consumed `GF16.toGF216 ` with trailing space. If it's part of
            # an unfold list, line_prefix ends with `unfold ` or `unfold X ... `.
            # Safer: check the token just before idx.
            pass
        # The needle has trailing space. So preceding char is "GF16.toGF216" + space already consumed.
        # We need to check what's before "GF16.toGF216" on the line.
        # Determine if this occurrence is inside a `[...]` list on the same line.
        depth_b = 0
        for c in line_prefix:
            if c == '[':
                depth_b += 1
            elif c == ']':
                if depth_b > 0:
                    depth_b -= 1
        if depth_b > 0:
            skip = True

        # Check if preceded by `unfold ` (with possibly more identifiers)
        # i.e. tokens on this line, leftmost token is `unfold`
        tokens = stripped.split()
        if tokens and tokens[0] == 'unfold':
            # `unfold a b GF16.toGF216 ...` - identifier is a lemma reference
            skip = True

        out.append(text[i:idx])
        if skip:
            out.append(needle)
            i = idx + len(needle)
            continue

        arg_start = idx + len(needle)
        res = find_arg(text, arg_start)
        if res is None:
            out.append(needle)
            i = arg_start
            continue
        end, arg = res
        if not arg:
            out.append(needle)
            i = arg_start
            continue
        out.append(arg + ".toGF216")
        i = end
    return ''.join(out)


def main(files):
    for path in files:
        with open(path, 'r', encoding='utf-8') as f:
            original = f.read()
        new = process_text(original)
        if new != original:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(new)
            print(f"updated {path}")


if __name__ == "__main__":
    main(sys.argv[1:])

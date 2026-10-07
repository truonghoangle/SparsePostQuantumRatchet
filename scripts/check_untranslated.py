#!/usr/bin/env python3
"""Cross-check Rust fns in src/ + generated/ against translation.json coverage."""
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

d = json.load(open(os.path.join(ROOT, 'translation.json')))
trans_names = set()
for cat in ['functions', 'types', 'globals', 'trait_decls', 'trait_impls']:
    for item in d.get(cat, []):
        trans_names.add(item['rust_name'])

# Names appearing as last path segment of any translated item
last_segments = set()
for t in trans_names:
    seg = t.split('::')[-1]
    last_segments.add(seg)

missing = []
for base in ['src', 'generated']:
    for dirpath, dirs, files in os.walk(os.path.join(ROOT, base)):
        if os.path.basename(dirpath) == 'test':
            continue
        for fn in files:
            if not fn.endswith('.rs') or fn == 'test.rs':
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            in_test_mod = False
            for i, line in enumerate(open(path), 1):
                if '#[cfg(test)]' in line:
                    in_test_mod = True
                m = re.match(r'\s*(?:pub(?:\(crate\))?\s+)?(?:const\s+)?(?:unsafe\s+)?fn\s+(\w+)', line)
                if m and not in_test_mod:
                    name = m.group(1)
                    if name not in last_segments:
                        missing.append((rel, i, name))

for rel, i, name in missing:
    print(f'UNTRACKED: {rel}:{i}  fn {name}')
print(f'total Rust fns with no matching translated atom: {len(missing)}')

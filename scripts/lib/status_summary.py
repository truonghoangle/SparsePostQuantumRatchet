#!/usr/bin/env python3
"""Summarise status.json (output of `lake exe status`) for the report plan.

Usage: python3 scripts/lib/status_summary.py [/path/to/status.json]
"""
import collections
import json
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "status.json"
d = json.load(open(path))
print("total crate-local verifiable entries", len(d))
nt = [f for f in d if "/test" not in f["source"]]
print("non-test", len(nt))
art = [f for f in nt if f["is_extraction_artifact"]]
print("loop artifacts", len(art))
spec = [f for f in nt if f["has_spec"]]
ver = [f for f in spec if f.get("verified_modulo_specs")]
print("has_spec", len(spec), "verified_modulo_specs", len(ver))
ax = collections.Counter()
for f in spec:
    for a in f.get("axioms", []):
        ax[a] += 1
print("axioms used by specs:")
for a, c in ax.most_common():
    print("  ", c, a)
by = collections.defaultdict(lambda: [0, 0, 0])
for f in nt:
    by[f["source"]][0] += 1
    if f["has_spec"]:
        by[f["source"]][1] += 1
    if f.get("verified_modulo_specs"):
        by[f["source"]][2] += 1
for s in sorted(by):
    t, sp, v = by[s]
    print(f"{s:45s} total={t:3d} spec={sp:3d} verified={v:3d}")
print("--- unspecified in polynomial/gf/chain/encoding/serialize:")
for f in nt:
    if not f["has_spec"] and any(
        k in f["source"] for k in ["polynomial.rs", "gf.rs", "chain.rs", "encoding.rs", "serialize.rs"]
    ):
        print("  ", f["source"], f["rust_name"])

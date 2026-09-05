#!/usr/bin/env python3
"""Weekly growth of verified Rust functions.

For every Rust function that currently has a spec theorem (per status.json from
`lake exe status`), locate the Lean file that declares the theorem and take the
date of the first commit that touched that file. Aggregate per ISO week.

Usage: python3 scripts/lib/verified_over_time.py [status.json] [out.json]
"""
import collections
import datetime
import glob
import json
import re
import subprocess
import sys

status_path = sys.argv[1] if len(sys.argv) > 1 else "status.json"
out_path = sys.argv[2] if len(sys.argv) > 2 else None

d = json.load(open(status_path))
spec = [f for f in d if f["has_spec"]]
files = glob.glob("Spqr/**/*.lean", recursive=True)
content = {f: open(f).read() for f in files}


def find_file(full_name: str):
    """Locate the file declaring `theorem <name>`; the declared name may carry a
    dotted prefix (e.g. `theorem SecretOutput.has_secret_spec` inside `namespace spqr`)."""
    parts = full_name.split(".")
    short = parts[-1]
    pat = re.compile(r"^\s*theorem\s+((?:[A-Za-z0-9_']+\.)*)" + re.escape(short) + r"\b", re.M)
    cands = [f for f, c in content.items() if pat.search(c)]
    if len(cands) <= 1:
        return cands[0] if cands else None
    # Disambiguate by matching namespace components against the file path.
    ns_parts = [p.lower() for p in parts[1:-1]]

    def score(f: str) -> int:
        fl = f.lower().replace("_", "")
        return sum(1 for p in ns_parts if p.replace("_", "") in fl)

    return max(cands, key=score)


def first_commit_date(path: str):
    # No --follow: renames would chase back into unrelated early scratch files.
    out = subprocess.run(
        ["git", "log", "--reverse", "--format=%ad", "--date=short", "--", path],
        capture_output=True, text=True,
    ).stdout.split()
    return out[0] if out else None


dates = {}
missing = []
for f in spec:
    fl = find_file(f["spec_name"])
    if fl is None:
        missing.append(f["spec_name"])
        continue
    dates[f["spec_name"]] = (first_commit_date(fl), fl)

if missing:
    print("no file found for:", missing, file=sys.stderr)

weekly = collections.Counter()
per_week_names = collections.defaultdict(list)
for name, (dt, fl) in dates.items():
    if dt is None:
        continue
    y, w, _ = datetime.date.fromisoformat(dt).isocalendar()
    key = f"{y}-W{w:02d}"
    weekly[key] += 1
    per_week_names[key].append(name)

cum = 0
for k in sorted(weekly):
    cum += weekly[k]
    print(f"{k}  +{weekly[k]:3d}  cumulative {cum:3d}")

if out_path:
    json.dump({"weekly": dict(sorted(weekly.items())), "names": per_week_names}, open(out_path, "w"), indent=1)

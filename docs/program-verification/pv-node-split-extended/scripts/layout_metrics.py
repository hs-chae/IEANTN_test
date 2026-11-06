"""Structural cost of one layout: files and lines a commit range adds, split into hand-written and generated,
plus graph deltas from two census files.

usage: python layout_metrics.py <worktree> <base-ref> <head-ref> <path-prefix>... [--census-base X.json --census-head Y.json]
"""
import json, subprocess, sys

args = sys.argv[1:]
cb = ch = None
if "--census-base" in args:
    i = args.index("--census-base"); cb = json.load(open(args[i + 1])); del args[i:i + 2]
if "--census-head" in args:
    i = args.index("--census-head"); ch = json.load(open(args[i + 1])); del args[i:i + 2]
wt, base, head, *prefixes = args
GENERATED = ("Challenge.lean", "fingerprints.json", "lake-manifest.json", "IEANTN/Nodes.lean", "IEANTN/Bridges.lean")
rows = subprocess.run(["git", "-C", wt, "diff", "--numstat", base, head, "--", *prefixes], capture_output=True, text=True).stdout
out = {"files": 0, "added": 0, "deleted": 0, "hand_files": 0, "hand_lines": 0, "generated_files": 0, "generated_lines": 0,
       "modified_existing": [], "per_file": []}
created = set(subprocess.run(["git", "-C", wt, "diff", "--name-only", "--diff-filter=A", base, head, "--", *prefixes],
                             capture_output=True, text=True).stdout.split())
for line in rows.splitlines():
    a, d, f = line.split("\t")
    a, d = int(a), int(d)
    gen = f.endswith(GENERATED) or f in GENERATED
    out["files"] += 1; out["added"] += a; out["deleted"] += d
    out["generated_files" if gen else "hand_files"] += 1
    out["generated_lines" if gen else "hand_lines"] += a
    if f not in created: out["modified_existing"].append(f)
    out["per_file"].append({"file": f, "added": a, "deleted": d, "generated": gen})
if cb and ch:
    out["graph_delta"] = {k: ch[k] - cb[k] for k in ("nodes", "conclusions", "distinct_fingerprints", "duplicate_group_count",
                                                       "import_edges", "solution_dirs_with_Solution_lean", "computation_node_count")}
print(json.dumps(out, indent=1))

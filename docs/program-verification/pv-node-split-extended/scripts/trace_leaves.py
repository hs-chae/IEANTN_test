"""Transitive unproved leaves (upstream 466b41b `graph_leaves`) and the designated chain of chosen conclusions at a
commit, plus the full import closure with each node's designated kind. Read-only (git show through `state_at`).
usage (from a worktree root holding scripts/ieantn_upstream.py): python trace_leaves.py <commit> <out.json> <conclusion>..."""
import json, sys
sys.path.insert(0, "scripts")
import ieantn_upstream as U
commit, out, keys = sys.argv[1], sys.argv[2], sys.argv[3:]
st = U.state_at(commit)
C = st["conclusions"]


def closure(k, seen=None):
    seen = set() if seen is None else seen
    if k in seen or k not in C: return seen
    seen.add(k)
    for s in (C[k].get("from") or []) + (C[k].get("imports") or []): closure(s, seen)
    return seen


res = {}
for k in keys:
    cl = sorted(closure(k))
    res[k] = {"designated_kind": C.get(k, {}).get("kind"), "leaves": sorted(set(U.graph_leaves(C, k))),
              "closure_size": len(cl), "closure": {c: C[c].get("kind") for c in cl}}
    print(f"{k}: designated {res[k]['designated_kind']}; closure {len(cl)} conclusions; leaves {len(res[k]['leaves'])}: {res[k]['leaves']}")
json.dump({"commit": commit, "results": res}, open(out, "w"), indent=1)

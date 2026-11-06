"""Leaf sets (upstream's graph_leaves, teorth/IEANTN 466b41b) of chosen conclusions at several graph states.
Run from a worktree whose scripts/ieantn_upstream.py is upstream's tool. Read-only."""
import sys, json
sys.path.insert(0, "scripts")
import ieantn_upstream as U
keys = ["RosserSchoenfeld.v1.zero_free_region", "RosserSchoenfeld.v1.zero_free_region_classical",
        "FKS.v2.psi_bound_all_x", "FKS.v2.psi_classical_bound"]
out = {}
for label, ref in [("ef21db9 (upstream base of the PoC)", "ef21db9"), ("6af2f7a^", "6af2f7a^"), ("6af2f7a", "6af2f7a"),
                   ("3280a3c (qrh-2pv_B)", "3280a3c"), ("upstream 466b41b", "466b41b"), ("working tree", None)]:
    st = U.state_at(ref)
    out[label] = {}
    for k in keys:
        e = st["conclusions"].get(k, {})
        out[label][k] = {"designated_kind": e.get("kind"), "from": e.get("from"), "leaves": sorted(set(U.graph_leaves(st["conclusions"], k)))}
for label, v in out.items():
    print("==", label)
    for k, e in v.items(): print(f"  {k}: {e['designated_kind']} from={e['from']} leaves={e['leaves']}")
json.dump(out, open(sys.argv[1], "w"), indent=1)

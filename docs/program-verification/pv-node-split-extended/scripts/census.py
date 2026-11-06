"""Census of an IEANTN graph at a git ref, read with `git show` only (no checkout, no writes).

usage: python census.py <repo-dir> <ref> <out.json>

Records, per ref: nodes by kind/status, conclusions, designated justification kinds, fingerprints and
duplicate-statement groups (with import-set comparison), receipts, solution projects, Tables importers,
and for every computation node its direct and transitive consumers grouped by node family.
"""
import collections, json, subprocess, sys
import yaml

repo, ref, out = sys.argv[1], sys.argv[2], sys.argv[3]


def git(*a):
    return subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True, check=True).stdout


def batch_show(paths):
    """Contents of many blobs at `ref` via one `git cat-file --batch` call."""
    p = subprocess.run(["git", "-C", repo, "cat-file", "--batch"], input="".join(f"{ref}:{x}\n" for x in paths).encode(),
                       capture_output=True, check=True)
    data, res, i = p.stdout, {}, 0
    for x in paths:
        nl = data.index(b"\n", i)
        head = data[i:nl].decode().split()
        if head[-1] == "missing":
            res[x] = None; i = nl + 1; continue
        size = int(head[2]); res[x] = data[nl + 1:nl + 1 + size].decode(); i = nl + 1 + size + 1
    return res


sha = git("rev-parse", ref).strip()
files = git("ls-tree", "-r", "--name-only", ref).split("\n")
files = [f for f in files if f]
ymls = [f for f in files if f.startswith("IEANTN/Nodes/") and f.endswith("/formalization.yaml")]
fps = [f for f in files if f.startswith("IEANTN/Nodes/") and f.endswith("/fingerprints.json")]
concl = [f for f in files if f.startswith("IEANTN/Nodes/") and f.endswith("/Conclusions.lean")]
tables = [f for f in files if f.startswith("IEANTN/Nodes/") and f.endswith("/Tables.lean")]
blobs = batch_show(ymls + fps + concl + tables)

nodes = {}
for y in ymls:
    d = yaml.safe_load(blobs[y]); nodes[d["node"]["id"]] = d
fp = {}
for f in fps:
    raw = json.loads(blobs[f] or "{}")
    # two layouts seen in the wild: {"Node.c": "hash"} or {"conclusions": {...}}; normalise
    if isinstance(raw, dict) and "conclusions" in raw and isinstance(raw["conclusions"], dict):
        raw = raw["conclusions"]
    for k, v in raw.items():
        fp[k] = v if isinstance(v, str) else (v.get("fingerprint") or v.get("hash") or json.dumps(v, sort_keys=True))


def designated_kind(c):
    js = {j["id"]: j for j in c.get("justifications") or []}
    return js.get(c.get("designated"), {}).get("kind")


family = lambda nid: nid.rsplit(".", 1)[0]
kinds = collections.Counter(d["node"].get("kind") for d in nodes.values())
status = collections.Counter(d["node"].get("status") for d in nodes.values())
dk = collections.Counter(); all_jk = collections.Counter(); istat = collections.Counter()
imports = {}            # "Node.concl" -> list of "Node.concl"
cdes = {}               # "Node.concl" -> designated kind
for nid, d in nodes.items():
    for c in d.get("conclusions") or []:
        key = f"{nid}.{c['id']}"
        imports[key] = [f"{i['node']}.{i['conclusion']}" for i in c.get("imports") or []]
        cdes[key] = designated_kind(c); dk[cdes[key]] += 1
        for j in c.get("justifications") or []: all_jk[j.get("kind")] += 1
        istat[c.get("imports_status", "undetermined")] += 1

# duplicate-statement groups: same fingerprint, more than one conclusion key
byfp = collections.defaultdict(list)
for k in imports:
    if k in fp: byfp[fp[k]].append(k)
dups = []
for h, ks in sorted(byfp.items(), key=lambda t: sorted(t[1])):
    if len(ks) > 1:
        imps = {k: sorted(imports[k]) for k in ks}
        dups.append({"fingerprint": h[:16], "members": sorted(ks),
                     "same_imports": len({tuple(v) for v in imps.values()}) == 1,
                     "imports": imps, "designated": {k: cdes[k] for k in ks},
                     "same_node_family": len({family(k.rsplit('.', 1)[0]) for k in ks}) == 1})
missing_fp = sorted(k for k in imports if k not in fp)

# consumer graph at conclusion level, and node level
rev = collections.defaultdict(set)
for k, imps in imports.items():
    for i in imps: rev[i].add(k)


def transitive_consumers(start_keys):
    seen, stack = set(), list(start_keys)
    while stack:
        x = stack.pop()
        for y in rev.get(x, ()):
            if y not in seen: seen.add(y); stack.append(y)
    return seen


comp = {}
for nid, d in sorted(nodes.items()):
    if d["node"].get("kind") != "computation": continue
    keys = [f"{nid}.{c['id']}" for c in d.get("conclusions") or []]
    direct = {y for k in keys for y in rev.get(k, ())}
    trans = transitive_consumers(keys)
    dn = sorted({y.rsplit(".", 1)[0] for y in direct}); tn = sorted({y.rsplit(".", 1)[0] for y in trans})
    comp[nid] = {"status": d["node"].get("status"), "conclusions": keys,
                 "designated": {k: cdes[k] for k in keys},
                 "imports": sorted({i for k in keys for i in imports[k]}),
                 "direct_consumer_nodes": dn, "direct_consumer_families": sorted({family(n) for n in dn} - {family(nid)}),
                 "direct_same_family_consumers": sorted(n for n in dn if family(n) == family(nid)),
                 "transitive_consumer_nodes": tn,
                 "transitive_consumer_families": sorted({family(n) for n in tn} - {family(nid)}),
                 "direct_import_edges": sum(1 for k in keys for _ in rev.get(k, ()))}

# Tables importers (Conclusions or Tables files importing some node's Tables module)
timp = collections.defaultdict(set)
for f in concl + tables:
    for line in (blobs[f] or "").split("\n"):
        s = line.strip()
        if s.startswith("import IEANTN.Nodes.") and s.endswith(".Tables"):
            timp[s.split()[1]].add("/".join(f.split("/")[2:4]))

sol_dirs = sorted({f.split("/")[1] for f in files if f.startswith("Solutions/") and f.count("/") >= 2})
sol_with_solution = sorted({f.split("/")[1] for f in files if f.startswith("Solutions/") and f.endswith("/Solution.lean") and f.count("/") == 2})
receipts = sorted(f for f in files if f.startswith("receipts/") and f.endswith(".json"))

res = {"repo": repo, "ref": ref, "sha": sha, "commit_date": git("log", "-1", "--format=%cI", sha).strip(),
       "nodes": len(nodes), "node_kinds": dict(kinds), "node_status": dict(status),
       "conclusions": len(imports), "distinct_fingerprints": len(set(fp[k] for k in imports if k in fp)),
       "conclusions_without_fingerprint": missing_fp,
       "designated_kinds": dict(dk), "all_justification_kinds": dict(all_jk), "imports_status": dict(istat),
       "import_edges": sum(len(v) for v in imports.values()),
       "duplicate_groups": dups, "duplicate_group_count": len(dups),
       "duplicate_groups_same_imports": sum(1 for g in dups if g["same_imports"]),
       "duplicate_conclusions": sum(len(g["members"]) for g in dups),
       "receipts": len(receipts), "solution_dirs": len(sol_dirs), "solution_dirs_with_Solution_lean": len(sol_with_solution),
       "solution_dir_names": sol_dirs, "tables": sorted(tables), "table_importers": {k: sorted(v) for k, v in timp.items()},
       "computation_nodes": comp, "computation_node_count": len(comp)}
json.dump(res, open(out, "w"), indent=1, sort_keys=False)
print(f"{ref} {sha[:7]}: nodes {len(nodes)} conclusions {len(imports)} distinct_fp {res['distinct_fingerprints']} "
      f"dup_groups {len(dups)} (same imports {res['duplicate_groups_same_imports']}) computation {len(comp)} "
      f"receipts {len(receipts)} solution_dirs {len(sol_dirs)} (with Solution.lean {len(sol_with_solution)}) edges {res['import_edges']}")

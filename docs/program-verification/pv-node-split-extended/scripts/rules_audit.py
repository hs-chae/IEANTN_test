"""Re-derive the promotion criteria for every computation node (and every node whose name says it is a numerical
provider) at a ref, from evidence rather than from metadata alone. Read-only (git show).

usage: python rules_audit.py <repo-dir> <ref> <census.json> <out.json> [<checked-axioms.json>]

Per provider conclusion and per direct consumer conclusion it records the strongest evidence class available:
  receipt        an official Comparator receipt exists (receipts/<C>.json) -> standard axioms by policy
  attested:<n>   a local native-assisted attestation exists (pv-evidence/<C>.native-assisted.local.json), n native facts
  checked:<n>    `#print axioms` run for this study (optional 5th argument), n native facts
  solution       Solutions/<Node>/Solution.lean exists, axioms not checked here
  none           no Lean proof in the repository
Criteria (both conventions are reported, nothing is merged silently):
  R0  no conclusion of the provider has an in-repository proof (cited/asserted, or none-yet without a solution)
  R1d >= 2 direct consumer families;  R1t >= 2 transitive consumer families
  R2m the first study's metadata proxy;  R2f provider evidence weaker than Comparator AND some direct consumer step is
      Lean-checked native-free (receipt, or attested with 0 native facts)
  R3m the first study's proxy (provider designates literature or numerical)
"""
import collections, json, subprocess, sys
import yaml

repo, ref, census_path, out = sys.argv[1:5]
checked = {k: v for k, v in json.load(open(sys.argv[5])).items() if not k.startswith("_")} if len(sys.argv) > 5 else {}
census = json.load(open(census_path))


def git(*a):
    return subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True).stdout


files = set(git("ls-tree", "-r", "--name-only", ref).split("\n"))
nodes = {}
for f in files:
    if f.startswith("IEANTN/Nodes/") and f.endswith("/formalization.yaml"):
        d = yaml.safe_load(git("show", f"{ref}:{f}")); nodes[d["node"]["id"]] = d


def des(c):
    js = {j["id"]: j for j in c.get("justifications") or []}; return js.get(c.get("designated"), {}).get("kind")


concl = {}
for nid, d in nodes.items():
    for c in d.get("conclusions") or []:
        concl[f"{nid}.{c['id']}"] = {"node": nid, "kind": des(c), "imports": [f"{i['node']}.{i['conclusion']}" for i in c.get("imports") or []]}
rev = collections.defaultdict(set)
for k, v in concl.items():
    for i in v["imports"]: rev[i].add(k)


def evidence(key):
    nid = concl[key]["node"]
    if f"receipts/{key}.json" in files: return "receipt"
    if key in checked: return checked[key]
    att = f"pv-evidence/{key}.native-assisted.local.json"
    if att in files:
        a = json.loads(git("show", f"{ref}:{att}"))
        return f"attested:{a['axioms']['native_fact_count']}" + ("" if a.get("status") == "passed" else f"({a.get('status')})")
    if f"Solutions/{nid}/Solution.lean" in files: return "solution"
    return "none"


family = lambda nid: nid.rsplit(".", 1)[0]
providers = sorted(set(census["computation_nodes"]) | {n for n in nodes if "Numerics" in n})
rows = []
LEAF = {"numerical", "literature", "asserted", "lean-noncompliant"}
for nid in providers:
    d = nodes[nid]; keys = [f"{nid}.{c['id']}" for c in d.get("conclusions") or []]
    pkinds = {concl[k]["kind"] for k in keys}
    pev = {k: evidence(k) for k in keys}
    cons = sorted({y for k in keys for y in rev.get(k, ())})
    cev = {c: (concl[c]["kind"], evidence(c)) for c in cons}
    fams = sorted({family(concl[c]["node"]) for c in cons} - {family(nid)})
    tfam = census["computation_nodes"].get(nid, {}).get("transitive_consumer_families")
    has_solution = f"Solutions/{nid}/Solution.lean" in files
    cited = lambda k: k in ("numerical", "literature", "asserted") or (k == "none-yet" and not has_solution)
    r0 = all(cited(concl[k]["kind"]) for k in keys)   # every conclusion's evidence lies outside the repository
    r1d = len(fams) >= 2
    r1t = None if tfam is None else len(tfam) >= 2
    r2m = bool(pkinds & LEAF) and any(k == "lean-comparator" or e == "solution" or e.startswith(("attested", "checked")) or e == "receipt"
                                      for k, e in cev.values())
    # "weaker than Comparator": cited or asserted evidence; a designated native-assisted proof; or a none-yet
    # conclusion whose solution has not been shown native-free. A provider proof checked native-free here
    # (`checked:0` / `attested:0`) is not weaker, whatever its designation.
    def weak(k, e):
        kind = concl[k]["kind"]
        if e in ("checked:0", "attested:0") or e.startswith("attested:0"): return False
        if kind in ("numerical", "literature", "asserted"): return True
        if kind == "lean-noncompliant": return True
        if kind == "none-yet": return True
        return False
    weaker = any(weak(k, e) for k, e in pev.items())
    consumer_clean = [c for c, (k, e) in cev.items() if e == "receipt" or e.startswith("attested:0") or e == "checked:0"]
    r2f = weaker and bool(consumer_clean)
    r3m = bool(pkinds & {"literature", "numerical"})
    rows.append({"node": nid, "kind": d["node"].get("kind"), "status": d["node"].get("status"),
                 "provider_designated": sorted(map(str, pkinds)), "provider_evidence": pev,
                 "direct_consumers": {c: list(v) for c, v in cev.items()}, "direct_families": fams,
                 "transitive_families": tfam, "R0_no_in_repo_proof": r0, "R1_direct": r1d, "R1_transitive": r1t,
                 "R2_metadata_proxy": r2m, "R2_from_evidence": r2f, "R2_clean_consumers": consumer_clean,
                 "R3_metadata_proxy": r3m})
json.dump({"ref": ref, "sha": git("rev-parse", ref).strip(), "rows": rows}, open(out, "w"), indent=1)
hdr = f"{'provider':24s} {'kind':11s} {'designated':28s} R0 R1d R1t R2m R2f R3m  consumers(kind/evidence)"
print(hdr)
for r in rows:
    yn = lambda b: "Y" if b else ("." if b is not None else "?")
    cs = "; ".join(f"{c.split('.',2)[0]}.{c.split('.',2)[1]}.{c.split('.',2)[2][:18]}={k}/{e}" for c, (k, e) in r["direct_consumers"].items())
    print(f"{r['node']:24s} {r['kind'][:11]:11s} {','.join(r['provider_designated'])[:28]:28s} {yn(r['R0_no_in_repo_proof']):2s} "
          f"{yn(r['R1_direct']):3s} {yn(r['R1_transitive']):3s} {yn(r['R2_metadata_proxy']):3s} {yn(r['R2_from_evidence']):3s} "
          f"{yn(r['R3_metadata_proxy']):3s}  {cs[:230]}")
c = collections.Counter()
for r in rows:
    for k in ("R0_no_in_repo_proof", "R1_direct", "R1_transitive", "R2_metadata_proxy", "R2_from_evidence", "R3_metadata_proxy"):
        c[k] += bool(r[k])
print("providers:", len(rows), dict(c))

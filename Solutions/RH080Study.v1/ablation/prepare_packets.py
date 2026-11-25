#!/usr/bin/env python3
"""Freeze the predeclared matched trial inputs; no model call is made here."""
import hashlib
import json
from pathlib import Path
import random
import shutil

HERE = Path(__file__).resolve().parent
S = HERE.parent
R = S.parents[1]
DATA = Path("/data/ivy-rh-080-20261125")
OLD = R / "Solutions/RHOnePrimeEvolution.v1"


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


COMMON = """# Common mathematical background

Ordinary RH concerns the Riemann zeta function, not all Dirichlet L-functions.
Primes start with p_0=2. All cube counts in this task count actual primes with
both endpoints excluded. A finite x calculation is not a proof for every real x.

Inherited source-conditional octic family: for all real x>=exp(24),1.03<=C<=16,
N(x,x+C*sqrt(x)*log(x))>((8/9)*C-0.91015+4.2/log(x))*sqrt(x).
Its named analytic source package consists of RH, a general Green explicit
formula, Nicolas spectral information and BPT zero counting. The inherited
cube consumer proves N(n^3,(n+1)^3)>0.7*n^2/log(n) for all real n>=exp(8).
Changing its assumption package must be disclosed; this is not a literature
record or a theorem from RH alone inside Mathlib.

The inherited polynomial-Gaussian pair has degree24 and thirteen rational
parameters, an actual Fourier identity, whole norm<=0.74899, positive exterior
leakage<=0.031152 and F(0)>=0.999999999. Under the general CMS analytic gap
reduction and RH it proves eventual normalized gap<=0.834021+epsilon for every
epsilon>0. There is no explicit numerical onset for this asymptotic conclusion.
The CMS functional C^+(A) is the supremum of (F(0)-A*positive exterior Fourier
leakage)/integral(abs(F)); all hypotheses and Fourier convention must follow
the original primary sources. The positive-denominator quotient is its inverse.
One may not lower A without proving that the corresponding prime reduction
remains applicable. The original source papers and rational supplement are in
/corpus/literature. They are the same bytes in every condition.

The compact20step dual and actual C grid candidate are also common numerical
information in that directory. They are not unverified premises available for
use as a theorem. A compiled output alone proves neither its real meaning nor
the formal source correctness. V0 can prove ordinary kernel/certificate facts;
only a completed actual-source-to-semantics chain may be called source-first PV.

Use tiers A(RH+ordinary foundations),B(named general source predicates),
C(source-first program verification),D(kernel numeric certificates),
E(independently checked written proof),F(numerical/search candidate),G(open).
No new axioms or sorry in accepted proof closures. Do not work on Ramanujan.
"""

TASKS = {
    "cube": """Find a rigorously stronger explicit count of primes between consecutive
real cubes than the inherited0.7*n^2/log(n), especially on the entire n>=exp(8)
ray. Investigate onset/coefficient tradeoffs, actual positive slack, endpoint
removal, direct pointwise estimates and source-accurate combination of bounds.
Report negative comparisons too. Numerical sampling is not whole-real coverage.
Supply the best complete proof you can, not only a proposal or literature list.
""",
    "functional": """Determine whether an ordinary-RH asymptotic normalized prime-gap
coefficient below0.8 is attainable within the fixed CMS functional and valid
source package. Check actual rational primal and dual witnesses and their full
continuum validity. Pursue a genuinely different valid approach if obstructed.
Distinguish a functional obstruction from a universal obstruction to prime gaps.
Find the strongest defensible bound you can; explicit onset is a separate goal.
Supply actual derivations, finite computations, proof/code and failed attempts.
""",
}


def main():
    protocol = json.loads((HERE / "PROTOCOL.json").read_text())
    corpus = json.loads((HERE / "CORPUS_MANIFEST.json").read_text())
    corpus_root = Path(corpus["root"])
    for row in corpus["files"]:
        need(sha(corpus_root / row["path"]) == row["sha256"], "Corpus changed")
    root = DATA / "ablation-representations-v1"
    need(not root.exists(), "Fresh representation export required")
    root.mkdir()
    module_sources = {}
    for packet in (OLD / "portable", OLD / "gaussian_gap/portable"):
        manifest = json.loads((packet / "SOURCE_MANIFEST.json").read_text())
        for row in manifest["modules"]:
            p = packet / row["path"]
            need(sha(p) == row["sha256"], "Frozen baseline source changed")
            if row["module"] in module_sources:
                need(p.read_bytes() == module_sources[row["module"]].read_bytes(), "Duplicate module differs")
            module_sources[row["module"]] = p
    need(not any("ramanujan" in n.lower() for n in module_sources), "Excluded source in packet")
    mapping = []
    for module, path in sorted(module_sources.items()):
        original = path.read_text()
        plain = original.replace("IEANTN", "Standalone")
        e2 = root / "E2/source" / (module.replace(".", "/") + ".lean")
        m1 = module.replace("IEANTN", "Standalone")
        e1 = root / "E1/source" / (m1.replace(".", "/") + ".lean")
        for p, text in ((e1, plain), (e2, original)):
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        mapping.append(dict(original_module=module, standalone_module=m1,
                            source_sha256=sha(path), e1_sha256=sha(e1), e2_sha256=sha(e2),
                            transformation="Literal IEANTN->Standalone renaming only; inverse recovers original bytes"))
        need(plain.replace("Standalone", "IEANTN") == original,
             "Renaming not invertible: source already contains Standalone")
        if module.startswith("IEANTN.Nodes.") and module.endswith(".Conclusions"):
            node = module.split(".")
            directory = R / "IEANTN/Nodes" / node[2] / node[3]
            for name in ("formalization.yaml", "fingerprints.json"):
                src = directory / name
                if src.is_file():
                    dest = root / "E2/network_metadata" / node[2] / node[3] / name
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(src, dest)
    (root / "E0").mkdir()
    (root / "E0/READING.md").write_text("Natural-language source corpus, common mathematical facts and goals are provided in /task and /corpus/literature. No application Lean proof source is exposed in this representation. Generic Mathlib sources/compiler remain available equally.\n")
    (root / "E1/READING.md").write_text("Standalone isomorphic Lean application library in source/. Its mathematical source and proof terms agree with E2 after the declared literal namespace/module renaming; network metadata and node index are omitted. This is a standalone Lean representation, not a claim of upstream PNT+ provenance or an erasure of all implicit logical dependency.\n")
    (root / "E2/READING.md").write_text("Exact343-source baseline closure (deduplicated), source/ plus original canonical node metadata in network_metadata/. No new coordinator discoveries or trial outcomes are included. Sources and logical dependencies are the same as E1 under its invertible renaming; explicit network metadata and canonical identities are additional representation.\n")
    write_json(HERE / "REPRESENTATION_EQUIVALENCE.json", dict(
        status="EXACT_INVERTIBLE_SOURCE_RENAMING_E1_E2_WITH_METADATA_DIFFERENCE",
        baseline_commit="25eb9bfe385be6f86c4280f92bd5f851ffe637a5",
        module_count=len(mapping), modules=mapping,
        limitation="E0 receives all primary papers and common mathematical facts but no application proof implementation. E1 versus E2 tests explicit canonical metadata/naming; it does not erase the logical dependencies intrinsic to a Lean proof library. These contrasts must not be conflated."))
    trials = []
    base = DATA / "ablation-packets-v1"
    need(not base.exists(), "Fresh packet export required")
    for rep in protocol["replicates"]:
        for task in protocol["tasks"]:
            for condition in protocol["conditions"]:
                name = f"{task['id']}-{condition['id']}-r{rep}"
                packet = base / name
                packet.mkdir(parents=True)
                l2 = condition["literature"] == "L2"
                package = ("In addition to the common inherited CMS/Octic package, the exact general Schoenfeld6.1 and canonical Büthe finite theta source statements in SECONDARY_SOURCE_FACTS.json are allowed explicit B predicates. They remain source propositions, not newly established RH-only Mathlib proofs."
                           if l2 else "Only the inherited RH+CMS/Octic named source package is available as unformalized analytic B premises. Additional secondary theorems may be read for comparison, but using them as extra unproved source predicates changes the source package and must be reported outside this condition's accepted same-premise score.")
                computation = ("V1: source-first proof artifacts will be mounted at /source_pv only after actual independent acceptance. Same numerical input/output information is supplied to V0; do not claim a causal numerical advantage from a secret stronger value."
                               if condition["computation"] == "V1" else "V0: no new source-first proof artifact is supplied. Ordinary rigorous Lean/certificate proofs and numerical search are allowed. The same candidate numerical inputs/outputs are provided to V1.")
                (packet / "TASK.md").write_text("# Assigned research task\n\n" + TASKS[task["id"]] + "\n\n" + package + "\n\n" + computation + "\n\nYour representation materials are at /representation. Primary papers and the exact rational supplement are at /corpus/literature. Use only your assigned tools/mounts; never access other arms, evaluator or host context.\n\nFixed budget:1200seconds,18000outputtokens,180executoroperations,96responses,4CPUs,64GiB RAM,12GiB scratch. Preserve a consistent final flat /work/submission/LOCK.json naming source/proof/result files and their SHA256; make supported conclusions, failed attempts, assumptions and incomplete steps clear. Do not include private reasoning transcripts.\n")
                (packet / "COMMON_FACTS.md").write_text(COMMON)
                (packet / "SECONDARY_SOURCE_FACTS.json").write_bytes((corpus_root / "SECONDARY_SOURCE_FACTS.json").read_bytes())
                manifest = dict(root=str(packet), files={p.name: sha(p) for p in packet.iterdir()})
                mp = DATA / "ablation-controller/packets" / (name + ".json")
                write_json(mp, manifest)
                trials.append(dict(id=name, condition=condition["id"], task=task["id"], replicate=rep,
                                   representation=condition["representation"], literature=condition["literature"],
                                   computation=condition["computation"], packet_manifest=str(mp),
                                   packet_manifest_sha256=sha(mp), representation_root=str(root / condition["representation"])))
    random.Random(protocol["randomization"]["seed"]).shuffle(trials)
    write_json(HERE / "TRIAL_ORDER.json", dict(status="ORDER_FROZEN_BEFORE_EXPERIMENTAL_INFERENCE",
               protocol_sha256=sha(HERE / "PROTOCOL.json"), corpus_sha256=sha(HERE / "CORPUS_MANIFEST.json"),
               trials=trials))
    print(json.dumps({"status": "INPUT_PACKETS_AND_ORDER_WRITTEN_NO_INFERENCE", "modules": len(mapping), "trials": len(trials)}))


if __name__ == "__main__":
    main()

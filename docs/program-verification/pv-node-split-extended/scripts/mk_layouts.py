"""Write the hypothetical nodes and thin solutions of the matched A/B experiments into a disposable worktree.

usage: python mk_layouts.py <worktree> <A|B> <pair>      pair in {T4, RAM, SHR}

Every file is marked HYPOTHETICAL. Nothing here is meant for the repository: the worktrees are local
branches agentB/pv8-A / agentB/pv8-B at qrh-2pv_B 3280a3c and are never pushed.

After this script: run `scripts/ieantn.py gen-challenges` (writes Challenge.lean and IEANTN/Nodes.lean),
`lake build` (core), `scripts/ieantn.py fingerprint` (writes fingerprints.json).
"""
import json, pathlib, shutil, sys

W = pathlib.Path(sys.argv[1]); WORLD = sys.argv[2]; PAIR = sys.argv[3]
HDR = "/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Agent B (Claude)\n-/\n"
STD = ["propext", "Quot.sound", "Classical.choice"]

# ---------------------------------------------------------------------------------------------------
# statements (copied verbatim from the existing nodes they mirror)
T4_PI = "HasNumericalBound Eπ ((5:ℝ)/10^16) (exp 330)"                       # = FKS2Numerics.v7.qrh_pi
T4_ABS = "∀ x ≥ exp 330,\n  |primeCounting x-Li x| ≤ ((5:ℝ)/10^16)*(x/log x)"  # = FKS2.v9.qrh_absolute_pi
RAM_CAL = ("∀ x > exp 9400,\n  DudekPlatt.v3.mainTerm x + (599543 / 5000) * x / log x ^ 6 < primeCounting x ∧\n"
           "    primeCounting x < DudekPlatt.v3.mainTerm x + (600457 / 5000) * x / log x ^ 6")
RAM_GAP = "∀ x > exp 9401,\n  (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < RamanujanGap.v1.gap x"
PSI = ("QRHCH2.v5", "psi_refined_bound"); ANCHOR = ("FKS2.v6", "table4_anchor_300")

# node specs: id -> (kind, conclusion id, statement, docstring, Conclusions imports, yaml imports, solution spec)
NODES = {
 ("A", "T4"): {"PVMatchT4A.v1": ("pipeline", "qrh_absolute_pi", T4_ABS,
     "Layout A of matched experiment M1: the consumer statement of `FKS2.v9.qrh_absolute_pi`, proved in one solution\n"
     "from the QRH `ψ` profile and the Table 4 anchor; the C program and its certificate stay in the solution.",
     ["IEANTN.Vocabulary.ErrorTerms"], [PSI, ANCHOR], "T4A")},
 ("B", "T4"): {
   "PVMatchT4P.v1": ("computation", "qrh_pi", T4_PI,
     "Layout B of matched experiment M1, provider: the statement of `FKS2Numerics.v7.qrh_pi`.",
     ["IEANTN.Vocabulary.ErrorTerms"], [PSI, ANCHOR], "T4P"),
   "PVMatchT4C.v1": ("pipeline", "qrh_absolute_pi", T4_ABS,
     "Layout B of matched experiment M1, consumer: the statement of `FKS2.v9.qrh_absolute_pi`, from the provider.",
     ["IEANTN.Vocabulary.ErrorTerms"], [("PVMatchT4P.v1", "qrh_pi")], "T4C")},
 ("A", "RAM"): {"PVMatchRamA.v1": ("pipeline", "gap_9401", RAM_GAP,
     "Layout A of matched experiment M2: the A→B′ chain's final statement, proved in one solution from the QRH `ψ`\n"
     "profile; both programs (calibration A, budget B′) and the composition stay in the solution.",
     ["IEANTN.Nodes.RamanujanGap.v1.Conclusions"], [PSI], "RAMA")},
 ("B", "RAM"): {
   "PVMatchRamP.v1": ("computation", "pi_calibrated_9400", RAM_CAL,
     "Layout B of matched experiment M2, provider: the calibrated `π` expansion that program A certifies\n"
     "(`Δ = 457/5000`), stated with `DudekPlatt.v3.mainTerm` like `DudekPlattNumerics.v5.pi_two_sided_qrh`.",
     ["IEANTN.Vocabulary.PrimeCounting", "IEANTN.Nodes.DudekPlatt.v3.Conclusions"], [PSI], "RAMP"),
   "PVMatchRamC.v1": ("pipeline", "gap_9401", RAM_GAP,
     "Layout B of matched experiment M2, consumer: the chain's final statement from the provider and program B′.",
     ["IEANTN.Nodes.RamanujanGap.v1.Conclusions"], [("PVMatchRamP.v1", "pi_calibrated_9400")], "RAMC")},
 ("A", "SHR"): {
   "PVMatchShrR.v1": ("pipeline", "gap_lower_bound",
     "∀ x>exp 401,\n  (1-RamanujanNumerics.v3.allowance/log x)*x^2/log x^6<RamanujanGap.v1.gap x",
     "Layout A of matched experiment M3 (shared result), consumer 1: the statement of\n"
     "`RamanujanGap.v3.gap_lower_bound`, with `DudekPlattNumerics.v5`'s π expansion proved inside the solution.",
     ["IEANTN.Nodes.RamanujanGap.v1.Conclusions", "IEANTN.Nodes.RamanujanNumerics.v3.Conclusions"],
     [PSI, ("RamanujanNumerics.v3", "epsilon_budget")], "SHRR"),
   "PVMatchShrD.v1": ("pipeline", "ramanujan_401",
     "∀ x : ℝ, exp 401 < x →\n  primeCounting x ^ 2 < exp 1 * x / log x * primeCounting (x / exp 1)",
     "Layout A of matched experiment M3 (shared result), consumer 2: the statement of `DudekPlatt.v5.ramanujan_401`,\n"
     "with `DudekPlattNumerics.v5`'s π expansion proved inside the solution instead of imported.",
     ["IEANTN.Vocabulary.PrimeCounting", "Mathlib.Analysis.SpecialFunctions.Log.Basic"],
     [PSI, ("DudekPlatt.v3", "criterion")], "SHRD")},
}

# solution specs: requires (name, relative path), imports, body
ABS_LEMMA = """namespace PVMatchStep
/-- Copy of `FKS2Pair.absolute_of_normalized` (Solutions/FKS2Numerics.v7/FKS2PairConsumers.lean), so that
layouts A and B run the identical consumer step without requiring the FKS2Numerics.v7 package. -/
theorem absolute_of_normalized {C : ℝ}
    (h : HasNumericalBound Eπ C (exp 330)) :
    ∀ x ≥ exp 330, |primeCounting x-Li x| ≤ C*(x/log x) := by
  intro x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  have hlog : 0<log x := by
    have ht := log_le_log (exp_pos (330:ℝ)) hx
    rw [log_exp] at ht
    linarith
  exact (div_le_iff₀ (div_pos hx0 hlog)).mp (h x hx)
end PVMatchStep
"""
T4 = ("solution_Table4Evolution_v1", "../Table4Evolution.v1")
PVR = ("agentB_pv_replay", "../../pilots/pv-replay")
DPN = ("solution_DudekPlattNumerics_v5", "../DudekPlattNumerics.v5")
RG3 = ("solution_RamanujanGap_v3", "../RamanujanGap.v3")
SOL = {
 "T4A": ([T4], ["IEANTN.Nodes.FKS2.v6.Conclusions", "IEANTN.Nodes.QRHCH2.v5.Conclusions",
                "IEANTN.Nodes.PVMatchT4A.v1.Conclusions", "Table4Evolution.KernelOnly"],
   ABS_LEMMA + """
/-- The challenge, through the kernel-only route (2-cell `qrh_trunc2.c`, no native fact). -/
theorem PVMatchT4A.v1.challenge_qrh_absolute_pi
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (fks2_v6_table4_anchor_300 : FKS2.v6.table4_anchor_300) :
    PVMatchT4A.v1.qrh_absolute_pi :=
  PVMatchStep.absolute_of_normalized
    (Table4Evolution.QRHTrunc.Kernel.qrh_pi qrhch2_v5_psi_refined_bound fks2_v6_table4_anchor_300)

/-- The same statement through the native-assisted route of the same C program (one native fact). -/
theorem PVMatchT4A.v1.qrh_absolute_pi_native_route
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (fks2_v6_table4_anchor_300 : FKS2.v6.table4_anchor_300) :
    PVMatchT4A.v1.qrh_absolute_pi :=
  PVMatchStep.absolute_of_normalized
    (Table4Evolution.QRHTrunc.qrh_pi qrhch2_v5_psi_refined_bound fks2_v6_table4_anchor_300)
"""),
 "T4P": ([T4], ["IEANTN.Nodes.FKS2.v6.Conclusions", "IEANTN.Nodes.QRHCH2.v5.Conclusions",
                "IEANTN.Nodes.PVMatchT4P.v1.Conclusions", "Table4Evolution.KernelOnly"],
   """
/-- The challenge, through the kernel-only route (2-cell `qrh_trunc2.c`, no native fact). -/
theorem PVMatchT4P.v1.challenge_qrh_pi
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (fks2_v6_table4_anchor_300 : FKS2.v6.table4_anchor_300) :
    PVMatchT4P.v1.qrh_pi :=
  Table4Evolution.QRHTrunc.Kernel.qrh_pi qrhch2_v5_psi_refined_bound fks2_v6_table4_anchor_300

/-- The same statement through the native-assisted route of the same C program (one native fact). -/
theorem PVMatchT4P.v1.qrh_pi_native_route
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (fks2_v6_table4_anchor_300 : FKS2.v6.table4_anchor_300) :
    PVMatchT4P.v1.qrh_pi :=
  Table4Evolution.QRHTrunc.qrh_pi qrhch2_v5_psi_refined_bound fks2_v6_table4_anchor_300
"""),
 "T4C": ([], ["IEANTN.Nodes.PVMatchT4P.v1.Conclusions", "IEANTN.Nodes.PVMatchT4C.v1.Conclusions"],
   ABS_LEMMA + """
/-- The challenge: the consumer step only; the provider's statement is a hypothesis. -/
theorem PVMatchT4C.v1.challenge_qrh_absolute_pi
    (pvmatcht4p_v1_qrh_pi : PVMatchT4P.v1.qrh_pi) :
    PVMatchT4C.v1.qrh_absolute_pi :=
  PVMatchStep.absolute_of_normalized pvmatcht4p_v1_qrh_pi
"""),
 "RAMA": ([PVR], ["IEANTN.Nodes.QRHCH2.v5.Conclusions", "IEANTN.Nodes.PVMatchRamA.v1.Conclusions",
                  "PVReplay.KernelOnly"],
   """
/-- The challenge: the existing kernel-only composition `PVPilot.KernelOnly.gap_exceeds_leading`
(programs A and B′, data link `M = 120 + Δ`, no native fact). `ForwardRamanujan.gap` and
`RamanujanGap.v1.gap` are the same expression. -/
theorem PVMatchRamA.v1.challenge_gap_9401
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound) :
    PVMatchRamA.v1.gap_9401 :=
  PVPilot.KernelOnly.gap_exceeds_leading qrhch2_v5_psi_refined_bound

/-- The same statement through the native-assisted composition (two native facts, one per program). -/
theorem PVMatchRamA.v1.gap_9401_native_route
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound) :
    PVMatchRamA.v1.gap_9401 :=
  PVPilot.Updated.gap_exceeds_leading qrhch2_v5_psi_refined_bound
"""),
 "RAMP": ([PVR], ["IEANTN.Nodes.QRHCH2.v5.Conclusions", "IEANTN.Nodes.PVMatchRamP.v1.Conclusions",
                  "PVReplay.KernelOnly"],
   """
open Real CalibrationPilot PVPilot.Updated

/-- Program A's certificate gives the calibrated expansion at the contract value `Δ = 457/5000`.
The contract is an inequality: any certified `NewA.bound ≤ 457/5000` proves the same statement. -/
theorem PVMatchRam.calibrated_of (hA : CertA) (hpsi : QRHCH2.v5.psi_refined_bound) :
    PVMatchRamP.v1.pi_calibrated_9400 := by
  have hle : NewChain.Δ ≤ 457 / 5000 := by simp only [NewChain.Δ, NewA.bound]; norm_num
  have h := calibrated_pi (Δ := 457 / 5000) DudekPlattNumerics.v4.Numerics.hlog2_proof (le_refl _)
    (by norm_num) (NewInput.point hpsi) (NewInput.tail hpsi) ((deviation_of hA).trans_le hle)
  intro x hx
  have hx' := h x hx
  have e1 : (120 - (457 / 5000 : ℝ)) = 599543 / 5000 := by norm_num
  have e2 : (120 + (457 / 5000 : ℝ)) = 600457 / 5000 := by norm_num
  rw [e1, e2] at hx'
  exact hx'

/-- The challenge, through program A's kernel-only certificate. -/
theorem PVMatchRamP.v1.challenge_pi_calibrated_9400
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound) :
    PVMatchRamP.v1.pi_calibrated_9400 :=
  PVMatchRam.calibrated_of PVPilot.KernelOnly.certificateA qrhch2_v5_psi_refined_bound

/-- The same statement through program A's native-assisted certificate (one native fact). -/
theorem PVMatchRamP.v1.pi_calibrated_9400_native_route
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound) :
    PVMatchRamP.v1.pi_calibrated_9400 :=
  PVMatchRam.calibrated_of PVPilot.Updated.certificateA qrhch2_v5_psi_refined_bound
"""),
 "RAMC": ([PVR], ["IEANTN.Nodes.PVMatchRamP.v1.Conclusions", "IEANTN.Nodes.PVMatchRamC.v1.Conclusions",
                  "PVReplay.KernelOnly"],
   """
open Real CalibrationPilot PVPilot.Updated

/-- Program B′'s certificate and the provider's statement give the gap bound. The same steps as
`PVPilot.Updated.gap_of`, but stated with B′'s own constants and the provider's numbers only: nothing
here refers to program A's constants (`NewA`, `NewChain.Δ`). -/
theorem PVMatchRam.gap_of_calibrated (hB : CertB) (hcal : PVMatchRamP.v1.pi_calibrated_9400) :
    PVMatchRamC.v1.gap_9401 := by
  have e1 : (120 - (457 / 5000 : ℝ)) = 599543 / 5000 := by norm_num
  have e2 : (120 + (457 / 5000 : ℝ)) = 600457 / 5000 := by norm_num
  have hpi : ForwardRamanujan.PiInput (599543 / 5000) (600457 / 5000) 9400 := by
    have h := piInput_of_calibrated (L₀ := 9400) (Δ := 457 / 5000) (by
      intro x hx
      rw [e1, e2]
      exact hcal x hx)
    rwa [e1, e2] at h
  intro x hx
  have hY : ((NewB.Y : ℚ) : ℝ) = 9401 := by simp only [NewB.Y]; norm_num
  have hM : ((NewB.M : ℚ) : ℝ) = 600457 / 5000 := by simp only [NewB.M]; norm_num
  have hm0 : ((NewB.m : ℚ) : ℝ) = 0 := by simp only [NewB.m]; norm_num
  have hA : ((NewB.A : ℚ) : ℝ) = 9400 := by simp only [NewB.A]; norm_num
  have hbd : ((NewB.bound : ℚ) : ℝ) = 66389 / 625 := by simp only [NewB.bound]; norm_num
  have hb := stageB_of hB x (by rw [hY]; exact hx)
  rw [hM, hm0, hA, hbd] at hb
  have hs := epsilon_shift_nonneg (m := 599543 / 5000) (by norm_num) hb
  have hg := ForwardRamanujan.gap_from_budget (by norm_num) (by norm_num) hpi hx hs
  have hL : 0 < log x := by
    have := log_lt_log (exp_pos _) hx
    rw [log_exp] at this
    linarith
  have hC : (66389 / 625 : ℝ) - 599543 / 5000 = -(68431 / 5000) := by norm_num
  rw [hC] at hg
  show (1 + (68431 / 5000) / log x) * x ^ 2 / log x ^ 6 < ForwardRamanujan.gap x
  convert hg using 1
  field_simp
  ring

/-- The challenge, through program B′'s kernel-only certificate. -/
theorem PVMatchRamC.v1.challenge_gap_9401
    (pvmatchramp_v1_pi_calibrated_9400 : PVMatchRamP.v1.pi_calibrated_9400) :
    PVMatchRamC.v1.gap_9401 :=
  PVMatchRam.gap_of_calibrated PVPilot.KernelOnly.certificateB pvmatchramp_v1_pi_calibrated_9400

/-- The same statement through program B′'s native-assisted certificate (one native fact). -/
theorem PVMatchRamC.v1.gap_9401_native_route
    (pvmatchramp_v1_pi_calibrated_9400 : PVMatchRamP.v1.pi_calibrated_9400) :
    PVMatchRamC.v1.gap_9401 :=
  PVMatchRam.gap_of_calibrated PVPilot.Updated.certificateB pvmatchramp_v1_pi_calibrated_9400
"""),
 "SHRR": ([RG3], ["IEANTN.Nodes.QRHCH2.v5.Conclusions", "IEANTN.Nodes.PVMatchShrR.v1.Conclusions",
                  "RamanujanGapV3.Consumer", "DDExpansionSolution"],
   """
/-- The challenge: `DudekPlattNumerics.v5`'s solution theorem (the π expansion from the QRH ψ profile)
composed with `RamanujanGap.v3`'s own consumer step. Same proof artifacts as layout B, one solution. -/
theorem PVMatchShrR.v1.challenge_gap_lower_bound
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (ramanujannumerics_v3_epsilon_budget : RamanujanNumerics.v3.epsilon_budget) :
    PVMatchShrR.v1.gap_lower_bound :=
  RamanujanGap.v3.challenge_gap_lower_bound
    (DudekPlattNumerics.v5.challenge_pi_two_sided_qrh qrhch2_v5_psi_refined_bound)
    ramanujannumerics_v3_epsilon_budget
"""),
 "SHRD": ([DPN], ["IEANTN.Nodes.QRHCH2.v5.Conclusions", "IEANTN.Nodes.PVMatchShrD.v1.Conclusions",
                  "IEANTN.Nodes.DudekPlatt.v3.Conclusions", "IEANTN.Bridges.DudekPlatt.QRH", "DDExpansionSolution"],
   """
/-- The challenge: `DudekPlattNumerics.v5`'s solution theorem composed with the core bridge
`DudekPlattQRH.ramanujan_401` that justifies `DudekPlatt.v5.ramanujan_401` in layout B. -/
theorem PVMatchShrD.v1.challenge_ramanujan_401
    (qrhch2_v5_psi_refined_bound : QRHCH2.v5.psi_refined_bound)
    (dudekplatt_v3_criterion : DudekPlatt.v3.criterion) :
    PVMatchShrD.v1.ramanujan_401 :=
  DudekPlattQRH.ramanujan_401
    (DudekPlattNumerics.v5.challenge_pi_two_sided_qrh qrhch2_v5_psi_refined_bound)
    dudekplatt_v3_criterion
""")
}


def conclusions_lean(nid, kind, cid, stmt, doc, imps):
    fam, ver = nid.split(".")
    return (HDR + "".join(f"import {i}\n" for i in imps) +
            f"\n/-!\n# Node `{nid}` (HYPOTHETICAL)\n\nDisposable experiment for the PV node-split study (matched A/B layouts).\n"
            f"Local branch only; never pushed.\n-/\n\nnamespace {nid}\nopen Real IEANTN\n\n"
            f"/-- {doc} -/\ndef {cid} : Prop :=\n  {stmt}\n\nend {nid}\n")


def yaml_text(nid, kind, cid, imps, sol_key):
    fam, ver = nid.split(".")
    route = {"SHRR": "the π expansion of DudekPlattNumerics.v5's solution composed with RamanujanGap.v3's consumer step",
             "SHRD": "the π expansion of DudekPlattNumerics.v5's solution composed with the core bridge DudekPlattQRH.ramanujan_401",
             "T4A": "the kernel-only Table 4 route composed with the absolute-bound step",
             "T4P": "the kernel-only Table 4 route",
             "T4C": "the absolute-bound step applied to the provider's statement",
             "RAMA": "the kernel-only A→B′ composition (programs A and B′)",
             "RAMP": "program A's kernel-only certificate and the calibration step",
             "RAMC": "program B′'s kernel-only certificate and the budget-to-gap step"}[sol_key]
    imp = "".join(f"      - node: {n}\n        conclusion: {c}\n" for n, c in imps)
    return f"""# Node metadata for `{nid}`.  See docs/NODES.md.
# HYPOTHETICAL: disposable experiment worktree for the PV node-split study; never pushed.
version: "v0.4"

node:
  id: {nid}
  family: {fam}
  version: {ver}
  kind: {kind}
  status: awaiting-verification

project:
  name: "Matched A/B experiment node {nid} (hypothetical)"
  description: >-
    Registered only in a disposable worktree to measure one layout of a matched A/B comparison.
  authors: ["Agent B (Claude)"]
  license: "Apache-2.0"
  responsible_maintainers: ["Agent B (Claude)"]

repository:
  role: substantive-development

classification:
  arxiv: [math.NT]
  msc2020: ["11N05", "11Y35"]

conclusions:
  - id: {cid}
    declaration: {nid}.{cid}
    challenge: {nid}.challenge_{cid}
    imports:
{imp}    imports_status: identified
    justifications:
      - id: solution
        kind: none-yet
        note: >-
          Experiment. Solutions/{nid} proves the challenge by {route}. Standard axioms
          expected; no Comparator run and no receipt, so designated none-yet.
    designated: solution
    progress:
      solution: Solutions/{nid}/
      state: in-progress
      remaining_holes: 0

sources:
  - title: "Agent B PV node-split study, matched experiments"
    authors: ["Agent B (Claude)"]
    type: "original-proof"
    id: "pv8-matched-{sol_key}"
    relationship: independently-proves
    note: >-
      Hypothetical registration for measurement only.

automation:
  methods:
    - method: manual
      role: >-
        Statement copied from an existing node; proof reused from existing solution code.

review:
  status: self-assessed
  reviewers: ["Agent B (Claude)"]

limitations:
  - >-
    Hypothetical node in a disposable worktree; not a contribution.
"""


def solution_files(nid, cid, imps, sol_key):
    reqs, limps, body = SOL[sol_key]
    d = W / "Solutions" / nid; d.mkdir(parents=True, exist_ok=True)
    lf = f'name = "solution_{nid.replace(".", "_")}"\ndefaultTargets = ["Solution"]\n\n'
    lf += '[[require]]\nname = "IEANTN"\npath = "../.."\n\n'
    for n, p in reqs: lf += f'[[require]]\nname = "{n}"\npath = "{p}"\n\n'
    lf += '[[lean_lib]]\nname = "Solution"\nroots = ["Solution"]\n'
    (d / "lakefile.toml").write_text(lf)
    (d / "lean-toolchain").write_text((W / "lean-toolchain").read_text())
    src = HDR + "".join(f"import {i}\n" for i in limps) + "\nopen Real IEANTN\n" + body
    (d / "Solution.lean").write_text(src)
    names = [f"{nid}.challenge_{cid}"]
    (d / "comparator.json").write_text(json.dumps({"challenge_module": f"IEANTN.Nodes.{nid}.Challenge",
        "solution_module": "Solution", "theorem_names": names, "permitted_axioms": STD, "enable_nanoda": True}, indent=2) + "\n")
    # manifest: reuse the manifest of the package whose closure is required (paths rebased), or the core's
    if reqs:
        n0, p0 = reqs[0]
        src_m = json.loads((W / "Solutions" / nid / p0 / "lake-manifest.json").read_text())
        pk = [{"type": "path", "scope": "", "name": n0, "manifestFile": "lake-manifest.json", "inherited": False,
               "dir": p0, "configFile": "lakefile.toml"}]
        pk[0:0] = [{"type": "path", "scope": "", "name": "IEANTN", "manifestFile": "lake-manifest.json",
                    "inherited": False, "dir": "../..", "configFile": "lakefile.toml"}]
        for p in src_m["packages"]:
            q = dict(p); q["inherited"] = True
            if q["type"] == "path":
                if q["name"] == "IEANTN": continue
                q["dir"] = str(pathlib.PurePosixPath(p0) / q["dir"])
            pk.append(q)
        m = {"version": src_m["version"], "packagesDir": ".lake/packages", "packages": pk,
             "name": f"solution_{nid.replace('.', '_')}", "lakeDir": ".lake"}
    else:
        core = json.loads((W / "lake-manifest.json").read_text())
        pk = [{"type": "path", "scope": "", "name": "IEANTN", "manifestFile": "lake-manifest.json", "inherited": False,
               "dir": "../..", "configFile": "lakefile.toml"}] + [dict(p, inherited=True) for p in core["packages"]]
        m = {"version": core["version"], "packagesDir": ".lake/packages", "packages": pk,
             "name": f"solution_{nid.replace('.', '_')}", "lakeDir": ".lake"}
    (d / "lake-manifest.json").write_text(json.dumps(m, indent=1) + "\n")
    (d / ".lake").mkdir(exist_ok=True)
    pk_link = d / ".lake" / "packages"
    if not pk_link.exists():
        pk_link.symlink_to("/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/network/.lake/packages")


for nid, (kind, cid, stmt, doc, cimps, yimps, sk) in NODES[(WORLD, PAIR)].items():
    fam, ver = nid.split(".")
    nd = W / "IEANTN" / "Nodes" / fam / ver
    if not nd.exists():
        sys.exit(f"scaffold {nid} first: python scripts/ieantn.py new-node {fam} --kind {kind}")
    (nd / "Conclusions.lean").write_text(conclusions_lean(nid, kind, cid, stmt, doc, cimps))
    (nd / "formalization.yaml").write_text(yaml_text(nid, kind, cid, yimps, sk))
    solution_files(nid, cid, yimps, sk)
    print("wrote", nid)

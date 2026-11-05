/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.SumAffine
import PVCore.Bridge

/-!
# Chunked sums: any number of entries, with the same frozen loop

The proved loop bound `SumStability.c_sum_forward_error` covers one call of the frozen `sum` over
1–64 entries. A longer sum is written as several calls, one per chunk of at most 64 entries, whose
results the wrapper adds:

    double s = sum(inputs0, n0); s = (s + sum(inputs1, n1)); …
    double r = (s * scale); r = (r ± c₁); …; return r;

Each call is an execution of the frozen loop on its own chunk, so the loop theorem applies per
chunk, unchanged. Each addition in the wrapper is one binary64 rounding, certified exactly
(`FKS2Table4.additionCheck`), like the suffix. Every value is concrete, so no new error analysis is
needed: the exact total is at most `Σⱼ sⱼ/(1 − γ_{nⱼ−1})` (and at least `Σⱼ sⱼ/(1 + γ_{nⱼ−1})`),
and the wrapper's roundings enter through the computed total itself.
-/

namespace PVCore

open SumStability (RN64 ValidInputs gamma CState ExecC selectedSumProgram)
open FKS2Scalar (round64)

/-- A selected program summing several arrays with the frozen `sum`, then scaling and applying
signed constants. -/
structure ChunkedProgram where
  fnName : String
  chunks : List (List String)
  scale : String
  ops : List (Sign × String)
  deriving DecidableEq, Repr

/-- The array holding chunk `j`. -/
def chunkName (j : ℕ) : String := "inputs" ++ toString j

def chunkCall (c : List String) (j : ℕ) : String :=
  "sum(" ++ chunkName j ++ "," ++ toString c.length ++ ")"

/-- The C text: the frozen `sum`, one array per chunk, and the wrapper. -/
def renderChunked (p : ChunkedProgram) : String :=
  let indexed := p.chunks.zipIdx
  (SumStability.render SumStability.selectedSumProgram).getD "" ++
  String.join (indexed.map fun cj =>
    "static const double " ++ chunkName cj.2 ++ "[" ++ toString cj.1.length ++ "] = {" ++
      String.intercalate "," cj.1 ++ "};") ++
  "double " ++ p.fnName ++ "(void) { double s = " ++
  (match indexed with
   | [] => "0.0"
   | cj :: _ => chunkCall cj.1 cj.2) ++ ";" ++
  String.join ((indexed.drop 1).map fun cj => "s = (s + " ++ chunkCall cj.1 cj.2 ++ ");") ++
  " double r = (s * " ++ p.scale ++ ");" ++
  String.join (p.ops.map fun o => "r = (r " ++ o.1.text ++ " " ++ o.2 ++ ");") ++
  "return r; }"

/-- The actual file `src` is the chunked program `p`, token for token. -/
def sourceMatchesChunked (src : String) (p : ChunkedProgram) : Bool :=
  let ts := tokens src
  ts.isSome && ts == tokens (renderChunked p)

def loadChunks (p : ChunkedProgram) : Option (List (List ℚ)) :=
  p.chunks.mapM (·.mapM loadLiteral)

def loadOpsC (p : ChunkedProgram) : Option (List (Sign × ℚ)) :=
  p.ops.mapM fun o => (loadLiteral o.2).map fun c => (o.1, c)

/-- Evaluator of the wrapper's additions, starting from `t`. -/
def runCombine : ℚ → List ℚ → Option ℚ
  | t, [] => some t
  | t, s :: ss => do let t' ← round64 (t + s); runCombine t' ss

/-! ## Operational semantics -/

/-- The wrapper's additions under IEEE round-to-nearest-even, one rounding per addition. -/
inductive CombineIEEE : ℚ → List ℚ → ℚ → Prop
  | nil (t : ℚ) : CombineIEEE t [] t
  | cons {t s t' out : ℚ} {ss : List ℚ} :
      RN64 (t + s) t' → CombineIEEE t' ss out → CombineIEEE t (s :: ss) out

/-- One chunk: the frozen loop over its loaded entries returns `s`. -/
def ChunkRun (xs : List ℚ) (s : ℚ) : Prop :=
  1 ≤ xs.length ∧ xs.length ≤ 64 ∧ ValidInputs xs ∧ runSum xs 0 = some s ∧
    ∃ final, ExecC selectedSumProgram (initialFor xs) final s

/-- Running the selected file `src` as the chunked program `p` returns `out`. -/
def ExecChunked (src : String) (p : ChunkedProgram) (out : ℚ) : Prop :=
  sourceMatchesChunked src p = true ∧
  ∃ (pairs : List (List ℚ × ℚ)) (total scale r0 : ℚ) (ops : List (Sign × ℚ)),
    loadChunks p = some (pairs.map Prod.fst) ∧ (∀ pr ∈ pairs, ChunkRun pr.1 pr.2) ∧
    (match pairs with
     | [] => False
     | pr :: rest => CombineIEEE pr.2 (rest.map Prod.snd) total) ∧
    loadLiteral p.scale = some scale ∧ loadOpsC p = some ops ∧
    RN64 (total * scale) r0 ∧ OpsIEEE ops r0 out

/-! ## Executable certificate -/

/-- Each wrapper addition rounds correctly. -/
def combineCheck : ℚ → List ℚ → ℚ → Bool
  | t, [], out => t == out
  | t, s :: ss, out =>
    match round64 (t + s) with
    | none => false
    | some t' => FKS2Table4.additionCheck (t + s) t' && combineCheck t' ss out

theorem combine_sound (ss : List ℚ) (t out : ℚ) (h : combineCheck t ss out = true) :
    CombineIEEE t ss out := by
  induction ss generalizing t with
  | nil =>
    have he : t = out := by simpa [combineCheck] using h
    subst out
    exact .nil _
  | cons s ss ih =>
    unfold combineCheck at h
    split at h
    · contradiction
    · rename_i t' _
      simp only [Bool.and_eq_true] at h
      exact .cons (FKS2Table4.additionCheck_sound h.1) (ih t' h.2)

structure ChunkedValues where
  pairs : List (List ℚ × ℚ)
  total : ℚ
  scale : ℚ
  ops : List (Sign × ℚ)
  r0 : ℚ
  out : ℚ
  deriving Inhabited

def chunkedValues? (p : ChunkedProgram) : Option ChunkedValues := do
  let xss ← loadChunks p
  let pairs ← xss.mapM fun xs => (runSum xs 0).map fun s => (xs, s)
  let total ← (match pairs with
    | [] => none
    | pr :: rest => runCombine pr.2 (rest.map Prod.snd))
  let scale ← loadLiteral p.scale
  let ops ← loadOpsC p
  let r0 ← round64 (total * scale)
  let out ← runOps ops r0
  return ⟨pairs, total, scale, ops, r0, out⟩

def chunkedValuesOf (p : ChunkedProgram) : ChunkedValues := (chunkedValues? p).getD default

/-- Upper bound for the exact total from the chunk results. -/
def chunkedUpper (pairs : List (List ℚ × ℚ)) : ℚ :=
  (pairs.map fun pr => pr.2 / (1 - gamma (pr.1.length - 1))).sum

/-- Lower bound for the exact total from the chunk results. -/
def chunkedLower (pairs : List (List ℚ × ℚ)) : ℚ :=
  (pairs.map fun pr => pr.2 / (1 + gamma (pr.1.length - 1))).sum

/-- The exact total of every entry. -/
def exactTotal (pairs : List (List ℚ × ℚ)) : ℚ := (pairs.map fun pr => pr.1.sum).sum

/-- **Instance certificate** for a chunked program. -/
def checkChunked (src : String) (p : ChunkedProgram) (eps : ℚ) : Bool :=
  match chunkedValues? p with
  | none => false
  | some v =>
    sourceMatchesChunked src p &&
    v.pairs.all (fun pr => decide (1 ≤ pr.1.length) && decide (pr.1.length ≤ 64) &&
      pr.1.all FKS2SumBridge.inputCheck && chainCheck pr.1 0 pr.2) &&
    (match v.pairs with
     | [] => false
     | pr :: rest => combineCheck pr.2 (rest.map Prod.snd) v.total) &&
    FKS2Table4.additionCheck (v.total * v.scale) v.r0 && opsCheck v.ops v.r0 v.out &&
    decide (0 ≤ v.scale) && decide (|v.out - exactValue v.scale v.ops v.total| ≤ eps)

theorem mapM_pairs : ∀ {xss : List (List ℚ)} {pairs : List (List ℚ × ℚ)},
    xss.mapM (fun xs => (runSum xs 0).map fun s => (xs, s)) = some pairs →
      pairs.map Prod.fst = xss ∧ ∀ pr ∈ pairs, runSum pr.1 0 = some pr.2
  | [], pairs, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp
  | xs :: xss, pairs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Option.map_eq_some_iff] at h
    obtain ⟨pr, ⟨s, hs, rfl⟩, rest, hrest, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_pairs hrest
    refine ⟨by simp [h1], ?_⟩
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hs
    · exact h2 q hq

/-- **Soundness of the chunked certificate.** An execution of the actual file, and the error
bounds of the exact total against the computed output. -/
theorem certifiedChunked {src : String} {p : ChunkedProgram} {eps : ℚ}
    (h : checkChunked src p eps = true) :
    let v := chunkedValuesOf p
    ExecChunked src p v.out ∧ 0 ≤ v.scale ∧
    exactValue v.scale v.ops (exactTotal v.pairs) ≤
      v.out + v.scale * (chunkedUpper v.pairs - v.total) + eps ∧
    v.out - v.scale * (v.total - chunkedLower v.pairs) - eps ≤
      exactValue v.scale v.ops (exactTotal v.pairs) := by
  unfold checkChunked at h
  split at h
  · contradiction
  rename_i v hv
  have hvo : chunkedValuesOf p = v := by simp [chunkedValuesOf, hv]
  simp only [hvo]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hsrc, hchunks⟩, hcomb⟩, hscale⟩, hops⟩, h0⟩, hf⟩ := h
  simp only [chunkedValues?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hv
  obtain ⟨xss, hxss, pairs, hpairs, total, htotal, scale, hsc, os, hos, r0, hr0, out, hout,
    hvv⟩ := hv
  subst hvv
  simp only at hsrc hchunks hcomb hscale hops h0 hf ⊢
  obtain ⟨hfst, hruns⟩ := mapM_pairs hpairs
  -- each chunk is a run of the frozen loop
  have hrun : ∀ pr ∈ pairs, ChunkRun pr.1 pr.2 := by
    intro pr hpr
    obtain ⟨⟨⟨hn1, hn2⟩, hdom⟩, hchain⟩ := hchunks pr hpr
    have hd : ValidInputs pr.1 := fun r hr => FKS2SumBridge.inputCheck_sound (hdom r hr)
    exact ⟨hn1, hn2, hd, hruns pr hpr, kernel_from_chain hchain hn2⟩
  have hopsS := ops_sound os r0 out hops
  have hexec : ExecChunked src p out := by
    refine ⟨hsrc, pairs, total, scale, r0, os, by rw [hfst]; exact hxss, hrun, ?_, hsc, hos,
      FKS2Table4.additionCheck_sound hscale, hopsS.1⟩
    cases pairs with
    | nil => simp at hcomb
    | cons pr rest => exact combine_sound _ _ _ hcomb
  -- the exact total against the chunk results
  have hup : exactTotal pairs ≤ chunkedUpper pairs := by
    unfold exactTotal chunkedUpper
    apply List.sum_le_sum
    intro pr hpr
    obtain ⟨hn1, hn2, hd, -, final, hk⟩ := hrun pr hpr
    exact sum_le_of_exec ⟨hn1, hn2⟩ hd (represents_initial hn2) hk
  have hlo : chunkedLower pairs ≤ exactTotal pairs := by
    unfold exactTotal chunkedLower
    apply List.sum_le_sum
    intro pr hpr
    obtain ⟨hn1, hn2, hd, -, final, hk⟩ := hrun pr hpr
    exact sum_ge_of_exec ⟨hn1, hn2⟩ hd (represents_initial hn2) hk
  have hm1 := mul_le_mul_of_nonneg_left hup h0
  have hm2 := mul_le_mul_of_nonneg_left hlo h0
  have hf1 := (abs_le.mp hf).1
  have hf2 := (abs_le.mp hf).2
  simp only [exactValue, opsValue_eq] at hf1 hf2 ⊢
  exact ⟨hexec, h0, by linarith, by linarith⟩

/-- Certificate for an upper-bound application of a chunked program. -/
def upperCheckChunked (src : String) (p : ChunkedProgram) (eps bound : ℚ) : Bool :=
  checkChunked src p eps &&
    decide ((chunkedValuesOf p).out + (chunkedValuesOf p).scale *
      (chunkedUpper (chunkedValuesOf p).pairs - (chunkedValuesOf p).total) + eps ≤ bound)

/-- **Application bridge (upper), chunked.** -/
theorem le_bound_of_checkChunked {src : String} {p : ChunkedProgram} {eps bound : ℚ}
    (h : upperCheckChunked src p eps bound = true) {T : ℝ}
    (hT : T ≤ ((chunkedValuesOf p).scale : ℝ) * ((exactTotal (chunkedValuesOf p).pairs : ℚ) : ℝ) +
      (opsConst (chunkedValuesOf p).ops : ℝ)) : T ≤ bound := by
  simp only [upperCheckChunked, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hb⟩ := h
  obtain ⟨-, -, hup, -⟩ := certifiedChunked hc
  simp only [exactValue, opsValue_eq] at hup
  have hq : (chunkedValuesOf p).scale * exactTotal (chunkedValuesOf p).pairs +
      opsConst (chunkedValuesOf p).ops ≤ bound := by linarith
  calc T ≤ _ := hT
    _ ≤ (bound : ℝ) := by exact_mod_cast hq

end PVCore

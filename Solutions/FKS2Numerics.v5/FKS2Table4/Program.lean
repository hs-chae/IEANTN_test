/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Certificates
import FKS2Table4.Rounding

namespace FKS2Table4
open FKS2Scalar SumStability

/-- Restricted constructor for the dedicated array/call/scaling/addition wrapper.
This extends the donor syntax with a static array and one exact selected-sum call. -/
structure TransportProgram where
  inputs : List String
  scale : String
  anchor : String
  point : String
  tail : String
  deriving DecidableEq, Repr

def selected : TransportProgram :=
  ⟨arrayLiterals,scaleLiteral,anchorLiteral,pointLiteral,tailLiteral⟩
def renderTransport (p : TransportProgram) : String :=
  (SumStability.render selectedSumProgram).getD "" ++
  "static const double inputs[30] = {" ++ String.intercalate "," p.inputs ++ "};" ++
  "double fks2_table4_transport(void) { double s = sum(inputs, 30);" ++
  "double r = (s * " ++ p.scale ++ ");" ++
  "r = (r + " ++ p.anchor ++ "); r = (r + " ++ p.point ++ ");" ++
  "r = (r + " ++ p.tail ++ "); return r; }"
def selectedSource : String := include_str ".."/"c"/"fks2_table4_transport.c"
def sourceChecked (p : TransportProgram) : Bool :=
  let ts := SumStability.tokens selectedSource
  ts.isSome && ts == SumStability.tokens (renderTransport p)

def loadLiteral (s : String) : Option ℚ := (decimal s).bind round64

def runSum : List ℚ → ℚ → Option ℚ
  | [],s => some s
  | x::xs,s => do let r ← round64 (s+x); runSum xs r

def runSuffix (p : TransportProgram) (s : ℚ) : Option ℚ := do
  let scale ← loadLiteral p.scale
  let anchor ← loadLiteral p.anchor
  let point ← loadLiteral p.point
  let tail ← loadLiteral p.tail
  let r ← round64 (s*scale)
  let r ← round64 (r+anchor)
  let r ← round64 (r+point)
  round64 (r+tail)

def initial : CState := FKS2SumBridge.sumInitial inputValues

/-- Actual guarded source interpretation. The kernel uses its original indexed-array semantics;
round64 interprets each new suffix operation. There is no numerical accuracy field. -/
def ExecTransport (p : TransportProgram) (out : ℚ) : Prop :=
  sourceChecked p = true ∧ p = selected ∧
  ∃ xs s final,
    p.inputs.mapM loadLiteral = some xs ∧
    RepresentsInput initial xs ∧ runSum xs 0 = some s ∧
    SumStability.ExecC selectedSumProgram initial final s ∧
    runSuffix p s = some out

def qsum : ℚ := (runSum inputValues 0).getD 0
def outputBits : ℕ := 0x3cc0fd404ee3d945
def q : ℚ := decodeBits outputBits

def chainCheck : List ℚ → ℚ → ℚ → Bool
  | [],s,out => s==out
  | x::xs,s,out =>
    match round64 (s+x) with
    | none => false
    | some r => additionCheck (s+x) r && chainCheck xs r out

theorem source_checked : sourceChecked selected = true := by native_decide

theorem execution_checks :
    selected.inputs.mapM loadLiteral = some inputValues ∧
    RepresentsInput initial inputValues ∧ runSum inputValues 0 = some qsum ∧
    chainCheck inputValues 0 qsum = true ∧
    (∀ r ∈ inputValues, FKS2SumBridge.inputCheck r = true) ∧
    runSuffix selected qsum = some q ∧ finiteBits outputBits = true ∧
    encodePositiveNormal q = some outputBits := by
  unfold RepresentsInput
  native_decide

theorem chain_sound (xs : List ℚ) (s out : ℚ) (h : chainCheck xs s out = true) :
    FKS2SumBridge.SumRun xs s out := by
  induction xs generalizing s with
  | nil =>
    have he : s=out := by simpa [chainCheck] using h
    subst out
    exact .nil _
  | cons x xs ih =>
    unfold chainCheck at h
    split at h
    · contradiction
    · rename_i r he
      simp only [Bool.and_eq_true] at h
      exact .cons (additionCheck_sound h.1) (ih _ h.2)

theorem kernel_execution : ∃ final,
    SumStability.ExecC selectedSumProgram initial final qsum := by
  have hrun := chain_sound inputValues 0 qsum execution_checks.2.2.2.1
  have hn : inputValues.length ≤ 64 := by rw [input_certificate.1];omega
  obtain ⟨last,hl,hout⟩ := FKS2SumBridge.run_to_for hrun initial rfl
    (by simp [initial,FKS2SumBridge.sumInitial]) rfl (by simp [initial,FKS2SumBridge.sumInitial]) hn
  refine ⟨{last with returned := some last.acc},rfl,last,?_,rfl,hout.symm⟩
  simpa [initialized,initial,FKS2SumBridge.sumInitial] using hl

theorem concrete_execution : ExecTransport selected q := by
  obtain ⟨final,hkernel⟩ := kernel_execution
  exact ⟨source_checked,rfl,inputValues,qsum,final,execution_checks.1,
    execution_checks.2.1,execution_checks.2.2.1,hkernel,execution_checks.2.2.2.2.2.1⟩

theorem output_unique {out : ℚ} (h : ExecTransport selected out) : out=q := by
  obtain ⟨hs,hp,xs,s,final,hload,hrep,hrun,hkernel,hsuffix⟩ := h
  have hxs : xs=inputValues := Option.some.inj (hload.symm.trans execution_checks.1)
  subst xs
  have hsum : s=qsum := Option.some.inj (hrun.symm.trans execution_checks.2.2.1)
  subst s
  exact Option.some.inj (hsuffix.symm.trans execution_checks.2.2.2.2.2.1)

theorem kernel_stability :
    |(qsum:ℝ)-(inputValues.sum:ℚ)| ≤
      (gamma 29:ℝ)*((inputValues.map abs).sum:ℚ) := by
  obtain ⟨final,he⟩ := kernel_execution
  have hd : ValidInputs inputValues := by
    intro r hr
    exact FKS2SumBridge.inputCheck_sound (execution_checks.2.2.2.2.1 r hr)
  simpa [input_certificate.1,exactSum,sumAbs] using
    c_sum_forward_error_real inputValues initial final qsum
      (by rw [input_certificate.1];norm_num) hd execution_checks.2.1 he

end FKS2Table4

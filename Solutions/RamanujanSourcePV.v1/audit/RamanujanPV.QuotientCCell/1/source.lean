/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCFunction
import RamanujanPV.AnalyticGlue

/-! Actual optimized C source outputs consumed by the actual IEANTN real-prime
Ramanujan theorem. A particular completed execution remains explicit until its
numerical execution evidence is supplied. No native return value is accepted
merely because a compiler or an ordinary certificate checker printed it. The
separate exponential/log enclosures retain their existing precise contracts. -/
namespace RamanujanPV.QuotientCCell
open QuotientCMachine
set_option autoImplicit false

/-- A completed modeled execution of the byte-linked optimized C source,
including all source-call applicability conditions. This definition is not a
claim that any concrete execution transcript has already been accepted. -/
def SourceExecution (N output : Nat) : Prop :=
  ∃ capacity sb lb heap final,
    2 ≤ N ∧ N ≤ 2000000000000 ∧ N.sqrt < capacity ∧ capacity < modulus ∧
    Owned heap ∧ QuotientCInit.Buffers heap sb lb N.sqrt ∧
    Run QuotientSqrtExecute.service QuotientCSourceV2.countFunction.body
      (QuotientCFunctionPrefix.input N capacity sb lb heap) (.returned final (.u64 output))

theorem source_execution_count {N output : Nat} (execution : SourceExecution N output) :
    Nat.primeCounting N=output := by
  obtain ⟨capacity,sb,lb,heap,final,hN2,hN,hcap,hcapWord,owned,buffers,run⟩ := execution
  have result := QuotientCFunction.completed_execution_correct hN2 hN hcap hcapWord owned buffers run
  exact (Value.u64.inj result.1).symm

/-- The selected actual real theorem consumes the two actual source-program
outputs directly. Neither prime-count equality nor the desired gap is assumed. -/
theorem source_cell_sound (c : Cell)
    (runP : SourceExecution c.m c.P) (runQ : SourceExecution c.j c.Q)
    (predicate : c.FixedPredicate) (enclosures : c.Enclosures)
    {x : ℝ} (hn : (c.n : ℝ) ≤ x) (hm : x < (c.m : ℝ)+1) : Holds x :=
  fixed_cell_sound c predicate ⟨source_execution_count runP,source_execution_count runQ⟩ enclosures hn hm

/-- Every original seven-word row is consumed by the unchanged network
certificate. This theorem cannot complete the finite range without the actual
source-execution evidence for ALL its P/Q outputs and all numerical enclosures. -/
theorem complete_certificate_from_source {start stop eLo eHi : Nat} {rows : List RawFactoredCell}
    (chain : RawCellChain start stop rows)
    (checked : ∀ r ∈ rows, r.n < r.next ∧ 0 < r.Lu ∧ r.j*eHi ≤ r.n*2^60 ∧
      r.A*r.Lu ≤ r.n*eLo ∧ 2^20*r.P^2 < r.A*r.Q)
    (executions : ∀ r ∈ rows, SourceExecution (r.next-1) r.P ∧ SourceExecution r.j r.Q)
    (heLo : (eLo : ℝ) ≤ Real.exp 1*(2 : ℝ)^60)
    (heHi : Real.exp 1*(2 : ℝ)^60 ≤ (eHi : ℝ))
    (logs : ∀ r ∈ rows, Real.exp 1 ≤ (r.n : ℝ) ∧
      Real.log (r.n : ℝ)*(2 : ℝ)^40 ≤ (r.Lu : ℝ)) :
    CompleteCertificate start stop (rows.map (fun r => r.toCell eLo eHi)) :=
  complete_certificate_from_raw chain checked
    (fun r hr => ⟨source_execution_count (executions r hr).1,source_execution_count (executions r hr).2⟩)
    heLo heHi logs

#print axioms source_execution_count
#print axioms source_cell_sound
#print axioms complete_certificate_from_source
end RamanujanPV.QuotientCCell

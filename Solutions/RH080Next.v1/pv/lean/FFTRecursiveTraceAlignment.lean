/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursivePinned
import FFTExecutionTraceTransfer
import FFTTwiddleCertificateBridge
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- Pointwise physical global-table agreement and exact decimation chains
suffice for every recursive stage entry. No literal table is unrolled. -/
theorem source_stage_entries (S : Nat) (positive : 0<S) (table : Nat → Nat)
    (fullTable : List FFT.IntegerModel.CInt) (kernelStages : Nat → List FFT.IntegerModel.CInt)
    (tableMatches : ∀k,k<2^(S-1) → cell table k=fullTable.getD k (0,0))
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1)) fullTable (kernelStages (t+1))) :
    ∀t,t<S → ∀j,j<2^t →
      (stages table (2^S) (t+1)).getD j (0,0)=(kernelStages (t+1)).getD j (0,0) := by
  intro t ht j hj
  have stride : 2^S/2^(t+1)=2^(S-(t+1)) := by
    have exponent : S=S-(t+1)+(t+1) := by omega
    have factored : 2^S=2^(S-(t+1))*2^(t+1) := by rw [←Nat.pow_add,←exponent]
    rw [factored,Nat.mul_div_left _ (by positivity)]
  have halves : 2^t*2^(S-(t+1))=2^(S-1) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have inside : j*2^(S-(t+1))<2^(S-1) := by
    rw [←halves]
    exact Nat.mul_lt_mul_of_pos_right hj (by positivity)
  rw [stage_getD table (2^S) t j hj,stride,tableMatches _ inside,(chains t ht).getD]
  simp only [Nat.mul_comm]

/-- Consume the actual completed source table-loop invariant and the literal
kernel TwiddleTrace, obtaining all source/certificate stage entry equalities. -/
theorem source_table_stage_entries {F : Type} {state : State F}
    {tableObject workObject owner S : Nat} {ids : TwiddleSource.Var → Nat}
    {tableData workData : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (h : TwiddleSource.View state tableObject workObject (2^S) ids owner ((2^S)/2) tableData workData seed)
    (positive : 0<S) {rest : List FFT.IntegerModel.CInt}
    (trace : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=(2^S)/2)
    (kernelStages : Nat → List FFT.IntegerModel.CInt)
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1))
      ((FFT.IntegerModel.unit,0)::rest) (kernelStages (t+1))) :
    ∀t,t<S → ∀j,j<2^t →
      (stages tableData (2^S) (t+1)).getD j (0,0)=(kernelStages (t+1)).getD j (0,0) := by
  have halfPower : (2:Nat)^S/2=2^(S-1) := by
    have exponent : S=S-1+1 := by omega
    have power : (2:Nat)^S=2^(S-1)*2 := by rw [←Nat.pow_succ];congr 1 <;> omega
    rw [power]
    omega
  apply source_stage_entries S positive tableData _ kernelStages _ chains
  intro k hk
  have actual:=TwiddleSource.source_table_matches_trace h trace length k (by rwa [halfPower])
  simpa only [cell,ComplexSource.pair,Nat.mul_comm] using actual

/-- A real source root execution and the independent kernel certificate have
identical integer output lists, using only domain-index input equality and the
actual table construction/decimation chain. This avoids evaluating huge lists. -/
theorem CallPost.output_eq_certificate {F G : Type} {total : Nat} {buffers : Buffers total}
    {S : Nat} {input table oldOutput oldWork output work : Nat → Nat} {before after : State F}
    (post : CallPost buffers S 0 0 1 input table oldOutput oldWork before after output work)
    (totalPower : total=2^S) (positive : 0<S)
    {tableState : State G} {tableObject workObject owner : Nat} {ids : TwiddleSource.Var → Nat}
    {tableWork : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (tableView : TwiddleSource.View tableState tableObject workObject (2^S) ids owner ((2^S)/2) table tableWork seed)
    {rest : List FFT.IntegerModel.CInt}
    (twiddles : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=(2^S)/2)
    {kernelStages : Nat → List FFT.IntegerModel.CInt} {kernelInput : Nat → FFT.IntegerModel.CInt}
    {kernelOutput : List FFT.IntegerModel.CInt}
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1))
      ((FFT.IntegerModel.unit,0)::rest) (kernelStages (t+1)))
    (kernelTrace : FFT.IntegerModel.ExecutionTrace kernelStages kernelInput S 0 1 kernelOutput)
    (inputEq : ∀j,j<2^S → cell input j=kernelInput j) : cells output 0 (2^S)=kernelOutput := by
  have sourceTrace:=post.trace
  rw [totalPower] at sourceTrace
  exact sourceTrace.root_outputs_eq kernelTrace inputEq
    (source_table_stage_entries tableView positive twiddles length kernelStages chains)

/-- A terminating actual source root Call, its full word/frame contract and
its independently certified integer output are obtained together. Source
success or a preexisting source Call is not an assumption. -/
theorem source_call_certificate_total {F G : Type} (context : Context F)
    {total : Nat} {buffers : Buffers total} {S : Nat} {input table : Nat → Nat}
    (contract : StrongContract context buffers input table S 0 0 1)
    (totalPower : total=2^S) (positive : 0<S)
    {tableState : State G} {tableObject workObject owner : Nat} {ids : TwiddleSource.Var → Nat}
    {tableWork : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (tableView : TwiddleSource.View tableState tableObject workObject (2^S) ids owner ((2^S)/2) table tableWork seed)
    {rest : List FFT.IntegerModel.CInt}
    (twiddles : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=(2^S)/2)
    {kernelStages : Nat → List FFT.IntegerModel.CInt} {kernelInput : Nat → FFT.IntegerModel.CInt}
    {kernelOutput : List FFT.IntegerModel.CInt}
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1))
      ((FFT.IntegerModel.unit,0)::rest) (kernelStages (t+1)))
    (kernelTrace : FFT.IntegerModel.ExecutionTrace kernelStages kernelInput S 0 1 kernelOutput)
    (inputEq : ∀j,j<2^S → cell input j=kernelInput j)
    (before : State F) (oldOutput oldWork : Nat → Nat) (well : SourceLocals.WellScoped before)
    (arrays : ∀r,WordArrayRep before (buffers.object r) (buffers.length r) (bufferData input table oldOutput oldWork r)) :
    ∃after output work,Call context "fft_recursive"
        (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
          (buffers.object .work) 0 0 1 (2^S) total) before (.value (.integer (integer64 0))) after ∧
      CallPost buffers S 0 0 1 input table oldOutput oldWork before after output work ∧
      cells output 0 (2^S)=kernelOutput ∧
      ∀other result,Call context "fft_recursive"
        (arguments (buffers.object .output) (buffers.object .input) (buffers.object .twiddle)
          (buffers.object .work) 0 0 1 (2^S) total) before result other →
        result=.value (.integer (integer64 0)) ∧ other=after := by
  obtain ⟨after,output,work,called,post,every⟩:=contract before oldOutput oldWork well arrays
  exact ⟨after,output,work,called,post,post.output_eq_certificate totalPower positive tableView
    twiddles length chains kernelTrace inputEq,every⟩

#print axioms source_stage_entries
#print axioms source_table_stage_entries
#print axioms CallPost.output_eq_certificate
#print axioms source_call_certificate_total
end RH080Next.FFTPV.RecursiveSource

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveCertificateContract
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- The complete recursion component: actual input/table mathematical
premises establish all source primitive domains, an actual terminating C Call
exists, every C Call agrees, and its true output words equal the independently
verified certificate output. Main initialization and final ANT consumption
remain separate components of the full application theorem. -/
theorem source_certificate_recursive_total {F G : Type} (context : Context F) (helpers : Helpers context)
    {total S : Nat} (buffers : Buffers total) (input table : Nat → Nat)
    (totalPower : total=2^S) (positive : 0<S) (stageLimit : S≤24)
    (inputNormalized : ∀k,k<total → NormalizedCell input k)
    {tableState : State G} {tableObject workObject owner : Nat} {ids : TwiddleSource.Var → Nat}
    {tableWork : Nat → Nat} {seed : FFT.IntegerModel.CInt}
    (tableView : TwiddleSource.View tableState tableObject workObject (2^S) ids owner ((2^S)/2) table tableWork seed)
    {rest : List FFT.IntegerModel.CInt}
    (twiddles : FFT.IntegerModel.TwiddleTrace seed (FFT.IntegerModel.unit,0) rest)
    (length : ((FFT.IntegerModel.unit,0)::rest).length=(2^S)/2)
    (kernelStages : Nat → List FFT.IntegerModel.CInt) (kernelInput : Nat → FFT.IntegerModel.CInt)
    (chains : ∀t,t<S → FFT.IntegerModel.DecimationTrace (S-(t+1))
      ((FFT.IntegerModel.unit,0)::rest) (kernelStages (t+1)))
    (inputEq : ∀j,j<2^S → cell input j=kernelInput j)
    (mass : FFT.coefficientMass (2^S) (fun j=>FFT.IntegerModel.decode (kernelInput j))≤362)
    (kernelError : ∀t,t<S → ∀j,j<2^t →
      ‖FFT.IntegerModel.decode ((kernelStages (t+1)).getD j (0,0))-FFT.negativeRoot (2*2^t)^j‖≤
        (1/10000000000000000000:ℝ))
    (kernelOutput : List FFT.IntegerModel.CInt)
    (kernelTrace : FFT.IntegerModel.ExecutionTrace kernelStages kernelInput S 0 1 kernelOutput)
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
  have contract:=recursive_contract_of_certificate context helpers buffers input table totalPower positive stageLimit
    inputNormalized tableView twiddles length kernelStages kernelInput chains inputEq mass kernelError
  exact source_call_certificate_total context contract totalPower positive tableView twiddles length chains kernelTrace
    inputEq before oldOutput oldWork well arrays

#print axioms source_certificate_recursive_total
end RH080Next.FFTPV.RecursiveSource

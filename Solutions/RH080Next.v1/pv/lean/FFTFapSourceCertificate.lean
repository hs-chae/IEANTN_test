/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainCertificateBase
import FapFFTNorm
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
namespace RH080Next.FFTPV.MainCertificate
open FFT FFT.IntegerModel

theorem fap_seed_eq : root 131072=FapForest17.seed := by decide +kernel

/-- Literal accepted N17 trace, supplied to the actual source execution proof.
There is no assumed C answer, observed scalar cap or execution axiom. -/
def fapCertificate : Certificate .fap where
  rest:=FapForest17.w17.tail
  stages:=FapForest17.stages
  output:=FapForest17.output
  twiddles:=by
    change TwiddleTrace (root 131072) (unit,0) FapForest17.w17.tail
    rw [fap_seed_eq]
    exact FapForest17.global_twiddle_trace
  length:=by
    change ((unit,0)::FapForest17.w17.tail).length=65536
    rw [←FapForest17.top_table_shape]
    exact FapForest17.top_table_length
  chains:=by
    intro t ht
    change DecimationTrace (17-(t+1)) ((unit,0)::FapForest17.w17.tail) (FapForest17.stages (t+1))
    rw [←FapForest17.top_table_shape]
    exact FapForest17.all_stage_chains t ht
  mass:=by
    have h:=RH080Next.Primal.FapFFTKernel.input_mass_le 131072 (by norm_num)
    exact h.trans (by norm_num)
  stageError:=by
    have h:=stage17_bounds FapForest17.seed FapForest17.w17.tail FapForest17.stages
      (by rw [←FapForest17.top_table_shape];exact FapForest17.top_table_length)
      FapForest17.seed_exact FapForest17.global_twiddle_trace
      (by intro t ht;rw [←FapForest17.top_table_shape];exact FapForest17.all_stage_chains t ht)
    intro t ht j hj
    exact (h t ht j hj).trans (by norm_num)
  trace:=FapForest17.complete_execution

theorem fap_certificate_sum : absSum fapCertificate.output=102468342420806369668447945569060309170116 := by
  have folded := fold_absSum FapForest17.output 0
  simp only [Nat.zero_add] at folded
  exact folded.symm.trans FapForest17.total_checked

#print axioms fapCertificate
#print axioms fap_certificate_sum
#print axioms FapForest17.complete_execution
end RH080Next.FFTPV.MainCertificate

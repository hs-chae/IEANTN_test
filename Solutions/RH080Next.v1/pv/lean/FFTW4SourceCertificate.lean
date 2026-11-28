/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainCertificateBase
import W4FFTCertifiedNorm
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
noncomputable section
namespace RH080Next.FFTPV.MainCertificate
open FFT FFT.IntegerModel

theorem w4_seed_eq : root 16777216=W4DAG24.seed := by decide +kernel

/-- Original literal N24 witness; no observed C output or norm is a field. -/
def w4Certificate : Certificate .w4 where
  rest:=W4DAG24.topTail
  stages:=W4DAG24.stages
  output:=W4DAG24.output
  twiddles:=by
    change TwiddleTrace (root 16777216) (unit,0) W4DAG24.topTail
    rw [w4_seed_eq]
    simpa only [W4DAG24.top_shape,List.tail_cons] using W4DAG24.global_twiddle_trace
  length:=by
    change ((unit,0)::W4DAG24.topTail).length=8388608
    rw [←W4DAG24.top_shape]
    exact W4DAG24.length_w24
  chains:=by
    intro t ht
    change DecimationTrace (24-(t+1)) ((unit,0)::W4DAG24.topTail) (W4DAG24.stages (t+1))
    rw [←W4DAG24.top_shape]
    exact W4DAG24.all_stage_chains t ht
  mass:=by
    exact RH080Next.Primal.W4FFTKernel.input_mass_le 16777216 (by norm_num)
  stageError:=by
    apply stage24_bounds W4DAG24.seed W4DAG24.topTail W4DAG24.stages
      (by rw [←W4DAG24.top_shape];exact W4DAG24.length_w24)
      W4DAG24.decoded_seed_exact
      (by simpa only [W4DAG24.top_shape,List.tail_cons] using W4DAG24.global_twiddle_trace)
      (by intro t ht;rw [←W4DAG24.top_shape];exact W4DAG24.all_stage_chains t ht)
  trace:=W4DAG24.complete_execution

theorem w4_certificate_sum : absSum w4Certificate.output=13108990146528710930483896317271209147027400 :=
  W4DAG24.total_checked

end RH080Next.FFTPV.MainCertificate

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open InputLoader

def rawModel : Profile → Nat
  | .fap=>(List.range 400).foldl (fun a j=> a+20*j*j*(FFT.IntegerModel.coefficient j).natAbs) 0
  | .w4=> FFT.IntegerModel.W4.quad

def scaledModel (p : Profile) : Nat:=if p=.fap then 100*rawModel p else rawModel p

theorem fap_term (j : Nat) : term .fap j=20*j*j*(FFT.IntegerModel.coefficient j).natAbs:=by
  rw [term,abs_coefficient,InputLoader.fap_coefficient]
  rfl

theorem w4_term (j : Nat) : term .w4 j=20*j*j*(FFT.IntegerModel.W4.coefficient j).natAbs:=by
  rw [term,abs_coefficient]
  rfl

theorem raw_quad_model (p : Profile) : partialQuad p p.count=rawModel p:=by
  have fold:=fold_partial p p.count 0
  simp only [Nat.zero_add] at fold
  rw [←fold]
  cases p with
  | fap=>
    have same : (fun sum j=> sum+term .fap j)=(fun sum j=> sum+20*j*j*(FFT.IntegerModel.coefficient j).natAbs):=by
      funext sum j;rw [fap_term]
    rw [same]
    rfl
  | w4=>
    have same : (fun sum j=> sum+term .w4 j)=(fun sum j=> sum+20*j*j*(FFT.IntegerModel.W4.coefficient j).natAbs):=by
      funext sum j;rw [w4_term]
    rw [same]
    rfl

#print axioms raw_quad_model
end RH080Next.FFTPV.QuadSource

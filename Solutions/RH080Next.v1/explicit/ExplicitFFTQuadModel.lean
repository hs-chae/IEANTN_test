/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderSource
import ExplicitFFTMagnitudeIntoSource
import ExplicitFFTAddMagnitudeSource
import FFTMultiplySmallFrame
import FFTMultiplySmallSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect
open InputLoader

def base : Nat:=1000000000
def factor (j : Nat) : Nat:=(20*j)*j
def coefficientAbs (profile : Profile) (j : Nat) : Nat:=InputCell.magnitudeValue (profile.encoded j)
def term (profile : Profile) (j : Nat) : Nat:=factor j*coefficientAbs profile j

def partialQuad (profile : Profile) (j : Nat) : Nat:=∑k∈Finset.range j,term profile k

theorem partialQuad_zero (p : Profile) : partialQuad p 0=0:=by simp [partialQuad]
theorem partialQuad_succ (p : Profile) (j : Nat) : partialQuad p (j+1)=partialQuad p j+term p j:=Finset.sum_range_succ _ _

theorem count_bound (p : Profile) : p.count≤2520:=by cases p <;> decide

theorem factor_bound (p : Profile) (j : Nat) (hj : j< p.count) : factor j< base:=by
  have count:=count_bound p
  have jj : j≤2520:=by omega
  have a:=Nat.mul_le_mul jj jj
  have b:=Nat.mul_le_mul_left 20 a
  norm_num [factor,base] at b ⊢
  nlinarith

theorem coefficientAbs_bound (p : Profile) (j : Nat) (hj : j< p.count) : coefficientAbs p j≤10000000000000000:=
  InputCell.magnitude_value_bound _ (p.encoded_bound j hj).le

theorem term_bound (p : Profile) (j : Nat) (hj : j< p.count) : term p j≤10^30:=by
  have f : factor j≤1000000000:=by have h:=factor_bound p j hj;change factor j<1000000000 at h;omega
  have h:=Nat.mul_le_mul f (coefficientAbs_bound p j hj)
  norm_num at h ⊢
  exact h.trans (by norm_num)

theorem partialQuad_bound (p : Profile) (j : Nat) (hj : j≤ p.count) : partialQuad p j<10^40:=by
  have bound : partialQuad p j≤ j*10^30:=by
    calc
      partialQuad p j≤∑k∈Finset.range j,(10^30 : Nat):=by
        apply Finset.sum_le_sum
        intro k hk
        exact term_bound p k (lt_of_lt_of_le (Finset.mem_range.mp hk) hj)
      _=j*10^30:=by simp
  have c:=count_bound p
  norm_num at bound ⊢
  omega

theorem abs_coefficient (p : Profile) (j : Nat) : coefficientAbs p j=((p.encoded j:Int)-(InputCell.scale:Int)).natAbs:=by
  unfold coefficientAbs InputCell.magnitudeValue
  by_cases h : InputCell.scale≤ p.encoded j
  · rw [if_pos h]
    rw [←Nat.cast_sub h,Int.natAbs_natCast]
  · rw [if_neg h]
    have eq : (p.encoded j:Int)-(InputCell.scale:Int)=-(↑(InputCell.scale-p.encoded j):Int):=by
      rw [Nat.cast_sub (show p.encoded j≤ InputCell.scale by omega)]
      ring
    rw [eq,Int.natAbs_neg,Int.natAbs_natCast]

theorem fold_partial (p : Profile) (j a : Nat) : (List.range j).foldl (fun sum k=> sum+term p k) a=a+partialQuad p j:=by
  induction j with
  | zero=> simp [partialQuad]
  | succ j ih=>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil,ih,partialQuad_succ,Nat.add_assoc]

#print axioms factor_bound
#print axioms partialQuad_bound
#print axioms abs_coefficient
end RH080Next.FFTPV.QuadSource

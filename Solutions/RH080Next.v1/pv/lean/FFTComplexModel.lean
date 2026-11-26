/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyCorrect
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RH080Next.FFTPV.ComplexSource
open FFT.Limbs

def unit : Nat:=10^36

theorem magnitude_congr (a b : Nat→Nat) (aStart bStart n : Nat)
    (same : ∀k,k<n → a (aStart+k)=b (bStart+k)) :
    magnitude 1000000000 n (fun k=>a (aStart+k))=magnitude 1000000000 n (fun k=>b (bStart+k)):=by
  apply Finset.sum_congr rfl
  intro k hk
  change a (aStart+k)*1000000000^k=b (bStart+k)*1000000000^k
  exact congrArg (fun v=>v*1000000000^k) (same k (Finset.mem_range.mp hk))

theorem represented_congr (a b : Nat→Nat) (aStart bStart : Nat)
    (same : ∀k,k<6 → a (aStart+k)=b (bStart+k)) :
    CanonicalSource.represented a aStart=CanonicalSource.represented b bStart:=by
  exact congrArg₂ signed (congrArg (fun v : Nat=>decide (v≠0)) (same 5 (by omega)))
    (magnitude_congr a b aStart bStart 5 (fun k hk=>same k (by omega)))

#print axioms represented_congr

theorem signed_natAbs (negative : Bool) (m : Nat) : (signed negative m).natAbs=m:=by
  cases negative <;> simp [signed]

theorem represented_natAbs (data : Nat→Nat) (start : Nat) :
    (CanonicalSource.represented data start).natAbs=magnitude 1000000000 5 (fun k=>data (start+k)):=
  signed_natAbs _ _

#print axioms represented_natAbs


end RH080Next.FFTPV.ComplexSource

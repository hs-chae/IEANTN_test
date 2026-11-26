/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTInputCellModel
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace RH080Next.FFTPV.InputCell
open FFT.Limbs

theorem magnitude_value_bound (encoded : Nat) (range : encoded≤2*scale) : magnitudeValue encoded≤scale:=by
  unfold magnitudeValue
  split <;> omega

theorem scaled_value_bound (encoded : Nat) (range : encoded≤2*scale) : magnitudeValue encoded*100≤base^2:=by
  have h:=Nat.mul_le_mul_right 100 (magnitude_value_bound encoded range)
  norm_num [scale,base] at h ⊢
  exact h

theorem packed_digit_bound (value k : Nat) (bound : value≤base^2) (hk : k<5) : packed base value k<base:=by
  interval_cases k
  · norm_num [packed,base]
  · norm_num [packed,base]
  · exact Nat.mod_lt value (by norm_num [base])
  · exact Nat.mod_lt (value/base) (by norm_num [base])
  · change value/base/base<base
    norm_num [base] at bound ⊢
    omega

theorem sign_value_bound (encoded : Nat) : signValue encoded≤1:=by unfold signValue;split <;> omega

theorem cell_digit_bound (encoded k : Nat) (range : encoded≤2*scale) (hk : k<5) : cell encoded k<base:=by
  have canonical:=CanonicalSource.canonicalData_digit (rawCell encoded) 0 k hk
  have unchanged : cell encoded k=rawCell encoded k:=by simpa only [cell,Nat.zero_add] using canonical
  rw [unchanged]
  unfold rawCell
  rw [Function.update_of_ne (by omega : k≠5)]
  exact packed_digit_bound _ _ (scaled_value_bound encoded range) hk

theorem cell_sign_bound (encoded : Nat) : cell encoded 5≤1:=by
  change CanonicalSource.canonicalData (rawCell encoded) 0 (0+5)≤1
  rw [CanonicalSource.canonicalData_sign]
  split
  · omega
  · simpa only [raw_sign] using sign_value_bound encoded

theorem cell_above_five (encoded i : Nat) (hi : 6≤ i) : cell encoded i=0:=by
  unfold cell CanonicalSource.canonicalData
  split
  all_goals
    simp only [Nat.zero_add,Function.update_of_ne (by omega : i≠5),rawCell,
      Function.update_of_ne (by omega : i≠5)]
    rw [show i=(i-6)+6 from by omega]
    rfl

theorem imaginary_zero (encoded : Nat) : CanonicalSource.represented (cell encoded) 6=0:=by
  have same:=ComplexSource.represented_congr (cell encoded) (fun _=>0) 6 0 (by
    intro k hk
    exact cell_above_five encoded (6+k) (by omega))
  have zero : CanonicalSource.represented (fun _=>0) 0=0:=by
    simp [CanonicalSource.represented,signed,magnitude]
  exact same.trans zero

theorem pair_value (encoded : Nat) :
    ComplexSource.pair (cell encoded) 0=(((encoded:Int)-(scale:Int))*100000000000000000000,0):=by
  exact Prod.ext (represented_cell encoded) (imaginary_zero encoded)

#print axioms scaled_value_bound
#print axioms cell_digit_bound
#print axioms cell_sign_bound
#print axioms pair_value
end RH080Next.FFTPV.InputCell

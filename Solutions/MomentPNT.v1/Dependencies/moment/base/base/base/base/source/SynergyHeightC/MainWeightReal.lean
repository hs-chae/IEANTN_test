/- Real meaning of the exact C main's exponential weights and direct division.
Source execution and fixed-width applicability are separate components. -/
import SynergyHeightC.MainWeightModel
import SynergyAnalytic.Laplace
import SynergyAnalytic.HeightPointGeometry
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical SynergyBasis
open SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def realWord (z : Int) : ℝ := (z : ℝ)/(ProofBox.scale 128 : ℝ)

theorem exact_word_sound (z : Int) :
    RealBox.Contains 128 (⟨z,z⟩ : ProofBox) (realWord z) := by
  have hs := RealBox.scale_real_pos 128
  simp [RealBox.Contains,realWord,div_mul_cancel₀ _ hs.ne']

theorem literal_integer_sound (z : Int) :
    RealBox.Contains 128 (ProofBox.literal 128 z 1) (z : ℝ) := by
  simpa using RealBox.literal_sound 128 z 1 (by decide)

theorem weight_sound {left right : ProofBox} {u v : ℝ}
    (hl : RealBox.Contains 128 left u) (hr : RealBox.Contains 128 right v)
    (hu : 0 ≤ u) (hu64 : u ≤ 64) (hv : 0 ≤ v) (hv64 : v ≤ 64)
    (huv : u ≤ v) :
    RealBox.Contains 128 (weight left right) (Real.exp (-u)-Real.exp (-v)) := by
  have hl' := Positive.expNeg_sound hl hu hu64
  have hr' := Positive.expNeg_sound hr hv hv64
  have he : 0 ≤ Real.exp (-u)-Real.exp (-v) := by
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  simpa only [weight,Positive.p,max_eq_right he] using Positive.positiveSub_sound hl' hr'

theorem paired_sound (d : ProofBox) (hd0 : 0 ≤ d.hi)
    (hd330 : d.hi < 330*ProofBox.scale 128) :
    RealBox.Contains 128 (paired d) (pairedFactor (realWord d.hi) (1/8) 330) := by
  let L : ProofBox := ProofBox.literal 128 330 1
  let delta := Positive.positiveSub L (fd d)
  let D : ℝ := realWord d.hi
  have hs := RealBox.scale_real_pos 128
  have hD0 : 0 ≤ D := div_nonneg (by exact_mod_cast hd0) hs.le
  have hD330 : D < 330 := by
    apply (div_lt_iff₀ hs).mpr
    exact_mod_cast hd330
  have hdelta : 0 < 330-D := by linarith
  have hL : RealBox.Contains 128 L 330 := literal_integer_sound 330
  have hfd : RealBox.Contains 128 (fd d) D := exact_word_sound d.hi
  have hd : RealBox.Contains 128 delta (330-D) := by
    simpa only [delta,Positive.p,max_eq_right hdelta.le] using Positive.positiveSub_sound hL hfd
  have hdeltaLo : 0 < delta.lo := by
    have hLword : L=⟨330*ProofBox.scale 128,330*ProofBox.scale 128⟩ := by
      decide +kernel
    simp only [delta,Positive.positiveSub_endpoints,hLword,fd]
    exact lt_max_of_lt_right (sub_pos.mpr hd330)
  have hq := Positive.divN_sound hd (by decide : 0 < (8 : Nat))
  have he := Positive.expNeg_sound hq (by positivity : 0 ≤ (330-D)/8)
    (by linarith : (330-D)/8 ≤ 64)
  have hem : Real.exp (-((330-D)/8)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsub : RealBox.Contains 128
      (Positive.positiveSub Positive.one (Positive.expNeg (Positive.divN delta 8)))
      (1-Real.exp (-((330-D)/8))) := by
    simpa only [Positive.p,Nat.cast_ofNat,max_eq_right (sub_nonneg.mpr hem)] using
      Positive.positiveSub_sound Positive.one_sound he
  have hmul := RealBox.mul_sound hL hsub
  have hdiv := Positive.divI_sound hmul hd
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 330) (sub_nonneg.mpr hem)) hdeltaLo
  have hresult := RealBox.add_sound he hdiv
  rw [pairedFactor_closed (D:=D) (r:=(1/8)) (L:=330) hdelta.ne']
  simpa only [paired,L,delta,D,Positive.p,Nat.cast_ofNat,div_eq_mul_inv,neg_mul,one_mul] using hresult

theorem term_sound {left right c d : ProofBox} {u v : ℝ}
    (hl : RealBox.Contains 128 left u) (hr : RealBox.Contains 128 right v)
    (hu : 0 ≤ u) (hu64 : u ≤ 64) (hv : 0 ≤ v) (hv64 : v ≤ 64)
    (huv : u ≤ v) (hd0 : 0 ≤ d.hi) (hd330 : d.hi < 330*ProofBox.scale 128) :
    RealBox.Contains 128 (term left right c d)
      (2*((Real.exp (-u)-Real.exp (-v))*realWord (adjustedC c).hi)*
        pairedFactor (realWord d.hi) (1/8) 330) := by
  exact RealBox.mul_sound
    (RealBox.mul_sound (literal_integer_sound 2)
      (RealBox.mul_sound (weight_sound hl hr hu hu64 hv hv64 huv)
        (exact_word_sound (adjustedC c).hi))) (paired_sound d hd0 hd330)

#print axioms weight_sound
#print axioms paired_sound
#print axioms term_sound
end SynergyHeightC.MainWeightModel

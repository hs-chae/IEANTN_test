import SynergyAnalytic.TangentBoxBasic
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem momentSeries_sound {a:ProofBox} {x:ℝ} (ha:RealBox.Contains p a x) (n:Nat) :
    RealBox.Contains p (momentSeries a n).1 (x^n/(n.factorial:ℝ)) ∧
    RealBox.Contains p (momentSeries a n).2 (SynergyAnalytic.positiveExpPoly n x) := by
  induction n with
  | zero =>
    constructor <;> simpa [momentSeries,SynergyAnalytic.positiveExpPoly] using one_sound
  | succ n ih =>
    have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hn : (n+1:ℝ) ≠ 0 := by positivity
    have ht:=divN_sound (RealBox.mul_sound ih.1 ha) (by omega : 0<n+1)
    have he : (x^n/(n.factorial:ℝ)*x)/((n+1:Nat):ℝ)=x^(n+1)/((n+1).factorial:ℝ) := by
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
      field_simp
      <;> ring
    rw [he] at ht
    have hs:=RealBox.add_sound ih.2 ht
    have he' : SynergyAnalytic.positiveExpPoly n x+x^(n+1)/((n+1).factorial:ℝ)=
        SynergyAnalytic.positiveExpPoly (n+1) x := by
      simp only [SynergyAnalytic.positiveExpPoly,Finset.sum_range_succ]
    rw [he'] at hs
    simpa only [momentSeries] using And.intro ht hs

 theorem sourceMoment_sound {lambda width common out:ProofBox} {l w:ℝ} (j:Nat)
    (hl:RealBox.Contains p lambda l) (hw:RealBox.Contains p width w)
    (he:RealBox.Contains p common (Real.exp (-l*w))) (hlp:0 < l) (hwp:0 ≤ w)
    (hr:sourceMoment lambda width common j=some out) :
    RealBox.Contains p out (SynergyAnalytic.exponentialMoment j l w) := by
  unfold sourceMoment at hr
  by_cases hbad:4 < j
  · simp [hbad] at hr
  · simp only [if_neg hbad] at hr
    try dsimp only at hr
    have hz:=RealBox.mul_sound hl hw
    have hs:=(momentSeries_sound hz j).2
    have hp:=RealBox.mul_sound he hs
    have hres:=positiveSub_sound one_sound hp
    have hnonneg:=SynergyAnalytic.exponentialMoment_residue_nonneg hlp hwp j
    rw [max_eq_right hnonneg] at hres
    have hf:=rat_sound j.factorial 1 (by decide)
    norm_num only [div_one] at hf
    have hnum:=RealBox.mul_sound hf hres
    have hden:=sourcePower_sound hl (j+1)
    have hn : 0 ≤ (j.factorial:ℝ)*(1-Real.exp (-l*w)*SynergyAnalytic.positiveExpPoly j (l*w)) :=
      mul_nonneg (by positivity) hnonneg
    have hh:=safeDiv_sound hnum hden hn hr
    convert hh using 1 <;> first
      | rfl
      | (unfold SynergyAnalytic.exponentialMoment;ring)

#print axioms momentSeries_sound
#print axioms sourceMoment_sound
end SynergyAnalytic.BoxModel

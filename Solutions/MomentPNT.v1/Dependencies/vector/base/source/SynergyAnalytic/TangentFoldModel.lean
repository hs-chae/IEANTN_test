import SynergyAnalytic.TangentTotals
import SynergyAnalytic.TangentCellModel
import SynergyAnalytic.TangentPrefixModel
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def prefixPoint (pre i:Nat) : ℝ := ((5*pre+i:Nat):ℝ)/((6*pre:Nat):ℝ)
noncomputable def prefixWidth (pre:Nat) : ℝ := (1:ℝ)/((6*pre:Nat):ℝ)
noncomputable def sharedPoint (n i:Nat) : ℝ := ((n+15*i:Nat):ℝ)/(n:ℝ)
noncomputable def sharedWidth (n:Nat) : ℝ := (15:ℝ)/(n:ℝ)

 theorem prefixFold_sound (pre count:Nat) (hp:0 < pre) {out:ProofBox}
    (hr:prefixFold pre count=some out) :
    RealBox.Contains p out (∑i∈Finset.range count,
      SynergyAnalytic.tangentUpper (prefixPoint pre i) (SynergyAnalytic.tangentNewton2 (prefixPoint pre i))
        (prefixWidth pre) 0) := by
  induction count generalizing out with
  | zero =>
    simp only [prefixFold,Option.some.injEq] at hr
    subst out
    simpa only [Finset.sum_range_zero] using zero_sound
  | succ count ih =>
    cases hprevious:prefixFold pre count with
    | none => simp [prefixFold,hprevious] at hr
    | some previous =>
      cases hcell:sourceCell (rat (5*pre+count) (6*pre)) (rat 1 (6*pre)) false with
      | none => simp [prefixFold,hprevious,hcell] at hr
      | some cell =>
        simp only [prefixFold,hprevious,hcell,Option.bind_eq_bind,Option.bind_some,
          Option.pure_def,Option.some.injEq] at hr
        subst out
        have hl:=rat_sound (5*pre+count) (6*pre) (by positivity)
        have hw:=rat_sound 1 (6*pre) (by positivity)
        norm_num only [Nat.cast_one] at hw
        have hx:0 < prefixPoint pre count := by unfold prefixPoint;positivity
        have hwp:0 ≤ prefixWidth pre := by unfold prefixWidth;positivity
        have hc:=sourceCell_prefix_sound hl hw hx hwp hcell
        have hh:=RealBox.add_sound (ih hprevious) hc
        simpa only [Finset.sum_range_succ,prefixPoint,prefixWidth,Nat.cast_one] using hh

 theorem sharedFold_sound (n count:Nat) (hn:0 < n) {out:ProofBox×ProofBox×ProofBox}
    (hr:sharedFold n count=some out) :
    RealBox.Contains p out.1 (∑i∈Finset.range count,
      SynergyAnalytic.tangentUpper (sharedPoint n i) (SynergyAnalytic.tangentNewton2 (sharedPoint n i))
        (sharedWidth n) 0) ∧
    RealBox.Contains p out.2.1 (∑i∈Finset.range count,
      SynergyAnalytic.tangentUpper (sharedPoint n i) (SynergyAnalytic.tangentNewton2 (sharedPoint n i))
        (sharedWidth n) 1) ∧
    RealBox.Contains p out.2.2 (∑i∈Finset.range count,
      SynergyAnalytic.tangentUpper (sharedPoint n i) (SynergyAnalytic.tangentNewton2 (sharedPoint n i))
        (sharedWidth n) 2) := by
  induction count generalizing out with
  | zero =>
    simp only [sharedFold,Option.some.injEq] at hr
    subst out
    constructor
    · simpa only [Finset.sum_range_zero] using zero_sound
    constructor <;> simpa only [Finset.sum_range_zero] using zero_sound
  | succ count ih =>
    cases hprevious:sharedFold n count with
    | none => simp [sharedFold,hprevious] at hr
    | some previous =>
      cases hcell:sourceCell (rat (n+15*count) n) (rat 15 n) true with
      | none => simp [sharedFold,hprevious,hcell] at hr
      | some cell =>
        simp only [sharedFold,hprevious,hcell,Option.bind_eq_bind,Option.bind_some,
          Option.pure_def,Option.some.injEq] at hr
        subst out
        have hl:=rat_sound (n+15*count) n hn
        have hw:=rat_sound 15 n hn
        have hx:0 < sharedPoint n count := by unfold sharedPoint;positivity
        have hwp:0 ≤ sharedWidth n := by unfold sharedWidth;positivity
        have hc:=sourceCell_shared_sound hl hw hx hwp hcell
        have hpreviousSound:=ih hprevious
        constructor
        · simpa only [Finset.sum_range_succ,sharedPoint,sharedWidth,Nat.cast_ofNat] using
            RealBox.add_sound hpreviousSound.1 hc.1
        constructor
        · simpa only [Finset.sum_range_succ,sharedPoint,sharedWidth,Nat.cast_ofNat] using
            RealBox.add_sound hpreviousSound.2.1 hc.2.1
        · simpa only [Finset.sum_range_succ,sharedPoint,sharedWidth,Nat.cast_ofNat] using
            RealBox.add_sound hpreviousSound.2.2 hc.2.2

#print axioms prefixFold_sound
#print axioms sharedFold_sound
end SynergyAnalytic.BoxModel

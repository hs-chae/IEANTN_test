import SynergyAnalytic.TangentFoldModel
import SynergyAnalytic.TangentBasis
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0

 theorem prefixPoint_eq (pre i:Nat) (hp:0 < pre) :
    prefixPoint pre i=SynergyAnalytic.uniformEdge (5/6) 1 pre i := by
  have hp0:(pre:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold prefixPoint SynergyAnalytic.uniformEdge
  push_cast
  field_simp
  <;> ring
 theorem prefixWidth_eq (pre:Nat) (hp:0 < pre) :
    prefixWidth pre=((1:ℝ)-5/6)/(pre:ℝ) := by
  have hp0:(pre:ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold prefixWidth
  push_cast
  field_simp
  <;> ring
 theorem sharedPoint_eq (n i:Nat) (hn:0 < n) :
    sharedPoint n i=SynergyAnalytic.uniformEdge 1 16 n i := by
  have hn0:(n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sharedPoint SynergyAnalytic.uniformEdge
  push_cast
  field_simp
  <;> ring
 theorem sharedWidth_eq (n:Nat) : sharedWidth n=((16:ℝ)-1)/(n:ℝ) := by
  norm_num [sharedWidth]

 theorem prefixSum_eq (pre:Nat) (hp:0 < pre) :
    (∑i∈Finset.range pre,SynergyAnalytic.tangentUpper (prefixPoint pre i)
      (SynergyAnalytic.tangentNewton2 (prefixPoint pre i)) (prefixWidth pre) 0)=
      SynergyAnalytic.tangentSum (5/6) 1 pre 0 := by
  unfold SynergyAnalytic.tangentSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [prefixPoint_eq pre i hp,prefixWidth_eq pre hp]
 theorem sharedSum_eq (n j:Nat) (hn:0 < n) :
    (∑i∈Finset.range n,SynergyAnalytic.tangentUpper (sharedPoint n i)
      (SynergyAnalytic.tangentNewton2 (sharedPoint n i)) (sharedWidth n) j)=
      SynergyAnalytic.tangentSum 1 16 n j := by
  unfold SynergyAnalytic.tangentSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [sharedPoint_eq n i hn,sharedWidth_eq]

/-- Full model-to-real correctness, including finite cells, peak and tail.
The only premise is actual successful computation of this explicit integer
model. The selected256instance is separately proved by ordinary kernel. -/
theorem sourceBasis_sound (n:Nat) {out:ProofBox×ProofBox×ProofBox}
    (hr:sourceBasis n=some out) :
    RealBox.Contains p out.1 (SynergyAnalytic.tangentBasisZero (n/16) n) ∧
    RealBox.Contains p out.2.1 (SynergyAnalytic.tangentBasisOne n) ∧
    RealBox.Contains p out.2.2 (SynergyAnalytic.tangentBasisTwo n) := by
  unfold sourceBasis at hr
  by_cases hbad:n < 16 ∨ 65536 < n
  · simp [hbad] at hr
  · simp only [if_neg hbad] at hr
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at hr
    rcases hr with ⟨first,hfirst,common,hcommon,logarithm,hlogarithm,peak,hpeak,e,he,tail,htail,hout⟩
    subst out
    have hn16:16 ≤ n := le_of_not_gt (not_or.mp hbad).1
    have hn:0 < n := by omega
    have hp:0 < n/16 := by omega
    have hPrefix:=prefixFold_sound (n/16) (n/16) hp hfirst
    rw [prefixSum_eq (n/16) hp] at hPrefix
    have hShared:=sharedFold_sound n n hn hcommon
    rw [sharedSum_eq n 0 hn,sharedSum_eq n 1 hn,sharedSum_eq n 2 hn] at hShared
    have hq:=rat_sound 601 2500 (by decide)
    have h6:=rat_sound 6 1 (by decide)
    have h256:=rat_sound 256 1 (by decide)
    have h2:=rat_sound 2 1 (by decide)
    have h56:=rat_sound 5 6 (by decide)
    norm_num only [Nat.cast_ofNat,div_one] at hq h6 h256 h2 h56
    have hLog:=logPos_sound 384 (RealBox.mul_sound h6 hq) hlogarithm
    have hPeak:=safeExp_sound (divN_sound (RealBox.add_sound one_sound hLog) (by decide : 0<(6:Nat))) hpeak
    have hPeakReal : RealBox.Contains p peak SynergyAnalytic.universalPeak := by
      convert hPeak using 1 <;> first | rfl | (unfold SynergyAnalytic.universalPeak SynergyAnalytic.peakLog;congr 1;ring)
    have hBq:=RealBox.mul_sound h256 hq
    have hE:=safeExp_sound hBq he
    have hTail:=safeDiv_sound (RealBox.mul_sound hE (RealBox.add_sound hBq one_sound))
      (RealBox.mul_sound h2 (RealBox.mul_sound hq hq)) (by positivity) htail
    have hTailReal : RealBox.Contains p tail (SynergyAnalytic.cubicTail 16) := by
      convert hTail using 1 <;> first | rfl | (norm_num [SynergyAnalytic.cubicTail])
    constructor
    · have hh:=RealBox.add_sound (RealBox.add_sound (RealBox.add_sound hPrefix hShared.1)
        (RealBox.mul_sound h56 hPeakReal)) hTailReal
      convert hh using 1 <;> first | rfl | (unfold SynergyAnalytic.tangentBasisZero;ring)
    constructor
    · exact RealBox.add_sound hShared.2.1 hTailReal
    · exact RealBox.add_sound hShared.2.2 hTailReal

#print axioms sourceBasis_sound
end SynergyAnalytic.BoxModel

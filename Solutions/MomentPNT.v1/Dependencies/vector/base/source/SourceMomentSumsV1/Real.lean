/- Closed exact interval sums and real moments. No C execution theorem is imported.
These are numerical/mathematical proofs, not source-first PV by themselves. -/
import SourceMomentSumsV1.All
import SynergyMomentMath.Real
import SynergyAnalytic.MassMomentEnvelope
namespace SourceMomentSumsV1.Real
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyMomentMath
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

theorem interval (stat : Cells.Stat) : RealBox.Contains 128 (Data.total stat 768)
 (∑ i∈Finset.range 768,SynergyMomentMath.Real.term stat i) :=
 SynergyMomentMath.Real.sum_contains (Cells.cell stat) (Data.total stat)
  (SynergyMomentMath.Real.term stat) (Data.zero stat) (All.recurrence stat)
  (SynergyMomentMath.Real.cell_sound stat) 768 (by decide)

theorem mass_interval : RealBox.Contains 128 (Data.total .mass 768)
 (totalMass SynergyMomentMath.Real.mass 768) := by
 simpa only [totalMass,SynergyMomentMath.Real.term] using interval .mass

theorem moment_interval : RealBox.Contains 128 (Data.total .firstMoment 768)
 (firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768) := by
 simpa only [firstMoment,SynergyMomentMath.Real.term,SynergyMomentMath.Real.firstMoment]
  using interval .firstMoment

private theorem contains_bounds {box : ProofBox} {value : ℝ}
 (h : RealBox.Contains 128 box value) :
 SynergyMomentMath.Real.realWord box.lo ≤ value ∧
 value ≤ SynergyMomentMath.Real.realWord box.hi := by
 have hs:=RealBox.scale_real_pos 128
 exact ⟨(div_le_iff₀ hs).mpr h.1,(le_div_iff₀ hs).mpr h.2⟩

theorem mass_word_lower : (6330434504/1000000000000:ℝ) ≤
 SynergyMomentMath.Real.realWord (Data.total .mass 768).lo := by
 rw [Data.mass_final]
 norm_num [SynergyMomentMath.Real.realWord,ProofBox.scale]
theorem mass_word_upper : SynergyMomentMath.Real.realWord (Data.total .mass 768).hi ≤
 (6330434505/1000000000000:ℝ) := by
 rw [Data.mass_final]
 norm_num [SynergyMomentMath.Real.realWord,ProofBox.scale]
theorem moment_word_upper : SynergyMomentMath.Real.realWord (Data.total .firstMoment 768).hi ≤
 (520404202477/1000000000000:ℝ) := by
 rw [Data.first_moment_final]
 norm_num [SynergyMomentMath.Real.realWord,ProofBox.scale]

theorem mass_bounds : (6330434504/1000000000000:ℝ) ≤
 totalMass SynergyMomentMath.Real.mass 768 ∧
 totalMass SynergyMomentMath.Real.mass 768 ≤ 6330434505/1000000000000 :=
 ⟨mass_word_lower.trans (contains_bounds mass_interval).1,
  (contains_bounds mass_interval).2.trans mass_word_upper⟩
theorem moment_upper : firstMoment SynergyMomentMath.Real.mass
 SynergyMomentMath.Real.dValue 768 ≤ 520404202477/1000000000000 :=
 (contains_bounds moment_interval).2.trans moment_word_upper

theorem domains (i : Nat) (hi : i < 768) :
 ∃ left right,SynergyAnalytic.HeightPoint.logCell i=some left ∧
  SynergyAnalytic.HeightPoint.logCell (i+1)=some right := by
 obtain ⟨value,cell,_⟩:=All.recurrence .mass i hi
 have exactCell:=(congrFun (congrFun SynergyMomentMath.Real.cell_function .mass) i).symm.trans cell
 obtain ⟨left,right,hl,hr,_⟩:=SynergyMomentMath.Real.abstract_decode
  SynergyAnalytic.HeightPoint.logCell SourceMomentWordsV1.All.word .mass i value exactCell
 exact ⟨left,right,hl,hr⟩
#print axioms interval
#print axioms mass_interval
#print axioms moment_interval
#print axioms mass_word_lower
#print axioms mass_word_upper
#print axioms moment_word_upper
#print axioms mass_bounds
#print axioms moment_upper
#print axioms domains
end
end SourceMomentSumsV1.Real

/- One fixed-L=300 complete-vector checker challenger.
Only pure kernel-proved mass cells and exact D words are reused. No C execution
proof imports, native evaluation or new analytic assumptions. -/
import SourceMomentSumsV1.Real
import SynergyMomentMath.Bounds
import SynergyAnalytic.MomentAnt300
import SynergyMomentMath.PointCaps
namespace SynergyVector300
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

def difference (after before : ProofBox) : ProofBox :=
 ⟨after.lo-before.lo,after.hi-before.hi⟩
theorem recover_add {before value after : ProofBox}
 (h : ProofBox.add before value=after) : difference after before=value := by
 have lo:=congrArg ProofBox.lo h
 have hi:=congrArg ProofBox.hi h
 change (⟨after.lo-before.lo,after.hi-before.hi⟩ : ProofBox)=⟨value.lo,value.hi⟩
 exact congrArg₂ ProofBox.mk (by dsimp only [ProofBox.add] at lo;omega)
  (by dsimp only [ProofBox.add] at hi;omega)

def massBox (i : Nat) : ProofBox := difference
 (SourceMomentSumsV1.Data.total .mass (i+1)) (SourceMomentSumsV1.Data.total .mass i)
theorem mass_cell (i : Nat) (hi : i < 768) :
 SynergyMomentMath.Cells.cell .mass i=some (massBox i) := by
 obtain ⟨value,cell,next⟩:=SourceMomentSumsV1.All.recurrence .mass i hi
 have exactBox:=@recover_add (SourceMomentSumsV1.Data.total .mass i) value
  (SourceMomentSumsV1.Data.total .mass (i+1)) next
 exact cell.trans (congrArg some exactBox.symm)
theorem mass_sound (i : Nat) (hi : i < 768) :
 RealBox.Contains 128 (massBox i) (SynergyMomentMath.Real.mass i) :=
 SynergyMomentMath.Real.cell_sound .mass i hi (massBox i) (mass_cell i hi)

def denominator (d : Int) : ProofBox := ProofBox.sub
 (ProofBox.literal 128 300 1) ⟨d,d⟩
def ratioTerm (mass : ProofBox) (d : Int) : ProofBox :=
 Positive.divI (ProofBox.mul 128 mass (ProofBox.literal 128 300 1)) (denominator d)
def term (i : Nat) : ProofBox := ratioTerm (massBox i) (SourceMomentWordsV1.All.word i).2
def realTerm (i : Nat) : ℝ :=
 SynergyMomentMath.Real.mass i*(300/(300-SynergyMomentMath.Real.dValue i))

theorem denominator_lo (d : Int) :
 (denominator d).lo=300*ProofBox.scale 128-d := by
 have exact300 : (ProofBox.literal 128 300 1).lo=300*ProofBox.scale 128 := by
  decide +kernel
 change (ProofBox.literal 128 300 1).lo-d=300*ProofBox.scale 128-d
 rw [exact300]
theorem ratio_sound {mass : ProofBox} {x : ℝ} (d : Int)
 (hmass : RealBox.Contains 128 mass x) (nonnegative : 0 ≤ x)
 (rangeD : d ≤ 163*ProofBox.scale 128) :
 RealBox.Contains 128 (ratioTerm mass d)
  (x*(300/(300-SynergyMomentMath.Real.realWord d))) := by
 have hden:=RealBox.sub_sound (SynergyMomentMath.Real.integer_sound 300)
  (SynergyMomentMath.Real.exact_word_sound d)
 have hm:=RealBox.mul_sound hmass (SynergyMomentMath.Real.integer_sound 300)
 have positive : 0 < (denominator d).lo := by
  rw [denominator_lo]
  have scalePositive : (0:Int) < ProofBox.scale 128 := by decide +kernel
  omega
 have q:=Positive.divI_sound hm hden (mul_nonneg nonnegative (by norm_num)) positive
 have same : x*300/(300-SynergyMomentMath.Real.realWord d)=
  x*(300/(300-SynergyMomentMath.Real.realWord d)) := by ring
 exact same ▸ q

theorem term_sound (i : Nat) (hi : i < 768) :
 RealBox.Contains 128 (term i) (realTerm i) :=
 ratio_sound (SourceMomentWordsV1.All.word i).2 (mass_sound i hi)
  (SynergyMomentMath.Bounds.mass_nonnegative i hi)
  (SynergyMomentMath.Bounds.integer_bounds i hi).2.2.2

#print axioms recover_add
#print axioms mass_cell
#print axioms mass_sound
#print axioms denominator_lo
#print axioms ratio_sound
#print axioms term_sound
end
end SynergyVector300

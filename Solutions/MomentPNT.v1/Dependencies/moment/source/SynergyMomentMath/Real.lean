/- Real interpretation of exact mass/first-moment arithmetic, independent of any
C execution theorem. Source-produced word identity is a separate proved bridge. -/
import SynergyMomentMath.Cells
import SynergyAnalytic.HeightPointWordBounds
namespace SynergyMomentMath.Real
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
noncomputable section

def realWord (z : Int) : ℝ := (z : ℝ)/(ProofBox.scale 128 : ℝ)
def cValue (i : Nat) : ℝ := realWord (SourceMomentWordsV1.All.word i).1
def dValue (i : Nat) : ℝ := realWord (SourceMomentWordsV1.All.word i).2
def mass (i : Nat) : ℝ := 2*((1/heightEndpoint i-1/heightEndpoint (i+1))*cValue i)
def firstMoment (i : Nat) : ℝ := mass i*dValue i
def term : Cells.Stat→Nat→ℝ
 | .mass=>mass
 | .firstMoment=>firstMoment

theorem exact_word_sound (z : Int) :
 RealBox.Contains 128 (⟨z,z⟩ : ProofBox) (realWord z) := by
 have hs:=RealBox.scale_real_pos 128
 simp [RealBox.Contains,realWord,div_mul_cancel₀ _ hs.ne']
theorem integer_sound (z : Int) :
 RealBox.Contains 128 (ProofBox.literal 128 z 1) (z : ℝ) := by
 simpa using RealBox.literal_sound 128 z 1 (by decide)
theorem weight_sound {left right : ProofBox} {u v : ℝ}
 (hl : RealBox.Contains 128 left u) (hr : RealBox.Contains 128 right v)
 (hu : 0 ≤ u) (hu64 : u ≤ 64) (hv : 0 ≤ v) (hv64 : v ≤ 64) (huv : u ≤ v) :
 RealBox.Contains 128 (Cells.weight left right) (Real.exp (-u)-Real.exp (-v)) := by
 have a:=Positive.expNeg_sound hl hu hu64
 have b:=Positive.expNeg_sound hr hv hv64
 have hnonneg : 0 ≤ Real.exp (-u)-Real.exp (-v) :=
  sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
 simpa only [Cells.weight,Positive.p,max_eq_right hnonneg] using
  Positive.positiveSub_sound a b

theorem term_sound (stat : Cells.Stat) {left right : ProofBox} {u v : ℝ}
 (cWord dWord : Int) (hl : RealBox.Contains 128 left u)
 (hr : RealBox.Contains 128 right v) (hu : 0 ≤ u) (hu64 : u ≤ 64)
 (hv : 0 ≤ v) (hv64 : v ≤ 64) (huv : u ≤ v) :
 RealBox.Contains 128 (Cells.term stat left right cWord dWord)
  (match stat with
   | .mass=>2*((Real.exp (-u)-Real.exp (-v))*realWord cWord)
   | .firstMoment=>(2*((Real.exp (-u)-Real.exp (-v))*realWord cWord))*realWord dWord) := by
 have base:=RealBox.mul_sound (integer_sound 2)
  (RealBox.mul_sound (weight_sound hl hr hu hu64 hv hv64 huv) (exact_word_sound cWord))
 cases stat with
 | mass=>exact base
 | firstMoment=>exact RealBox.mul_sound base (exact_word_sound dWord)

def abstractCell (grid : Nat→Option ProofBox) (words : Nat→Int×Int)
 (stat : Cells.Stat) (i : Nat) : Option ProofBox := do
 let left←grid i
 let right←grid (i+1)
 let word:=words i
 pure (Cells.term stat left right word.1 word.2)
theorem cell_function : Cells.cell=abstractCell logCell SourceMomentWordsV1.All.word := rfl

theorem abstract_decode (grid : Nat→Option ProofBox) (words : Nat→Int×Int)
 (stat : Cells.Stat) (i : Nat) (out : ProofBox)
 (h : abstractCell grid words stat i=some out) :
 ∃ left right,grid i=some left ∧ grid (i+1)=some right ∧
  Cells.term stat left right (words i).1 (words i).2=out := by
 unfold abstractCell at h
 cases hl : grid i with
 | none=>simp only [hl,Bind.bind,Option.bind] at h;cases h
 | some left=>
  cases hr : grid (i+1) with
  | none=>simp only [hl,hr,Bind.bind,Option.bind] at h;cases h
  | some right=>
   simp only [hl,hr,Bind.bind,Option.bind,Pure.pure] at h
   exact ⟨left,right,rfl,rfl,Option.some.inj h⟩

theorem cell_sound (stat : Cells.Stat) (i : Nat) (hi : i < 768)
 (out : ProofBox) (h : Cells.cell stat i=some out) :
 RealBox.Contains 128 out (term stat i) := by
 have exactCell:=(congrFun (congrFun cell_function stat) i).symm.trans h
 obtain ⟨left,right,hl,hr,result⟩:=abstract_decode logCell
  SourceMomentWordsV1.All.word stat i out exactCell
 have last : logEndpoint logCellCount=60 := by
  have q:=congrArg Real.log heightEndpoint_last
  simpa only [log_heightEndpoint,Real.log_exp] using q
 change logEndpoint 768=60 at last
 have hleft : logEndpoint i ≤ 64 := by
  have q:=logEndpoint_monotone (Nat.le_of_lt hi)
  rw [last] at q
  linarith
 have hright : logEndpoint (i+1) ≤ 64 := by
  have q:=logEndpoint_monotone (Nat.succ_le_of_lt hi)
  rw [last] at q
  linarith
 have sound:=term_sound stat (SourceMomentWordsV1.All.word i).1
  (SourceMomentWordsV1.All.word i).2
  (logCell_sound (Nat.le_of_lt hi) hl) (logCell_sound (Nat.succ_le_of_lt hi) hr)
  (logEndpoint_pos i).le hleft (logEndpoint_pos (i+1)).le hright
  (logEndpoint_monotone (Nat.le_succ i))
 rw [result] at sound
 cases stat <;>
  simpa only [term,mass,firstMoment,cValue,dValue,heightEndpoint,Real.exp_neg,one_div] using sound

theorem sum_contains (get : Nat→Option ProofBox) (totals : Nat→ProofBox)
 (values : Nat→ℝ) (zero : totals 0=⟨0,0⟩)
 (steps : ∀ i,i < 768→∃ value,get i=some value ∧
  ProofBox.add (totals i) value=totals (i+1))
 (sound : ∀ i,i < 768→∀ out,get i=some out→RealBox.Contains 128 out (values i))
 (n : Nat) (hn : n ≤ 768) :
 RealBox.Contains 128 (totals n) (∑ i∈Finset.range n,values i) := by
 induction n with
 | zero=>simp only [zero,Finset.range_zero,Finset.sum_empty,RealBox.Contains];norm_num
 | succ n ih=>
  obtain ⟨value,cell,next⟩:=steps n (by omega)
  have q:=RealBox.add_sound (ih (by omega)) (sound n (by omega) value cell)
  rw [next] at q
  simpa only [Finset.sum_range_succ] using q
#print axioms exact_word_sound
#print axioms integer_sound
#print axioms weight_sound
#print axioms term_sound
#print axioms cell_function
#print axioms abstract_decode
#print axioms cell_sound
#print axioms sum_contains
end
end SynergyMomentMath.Real

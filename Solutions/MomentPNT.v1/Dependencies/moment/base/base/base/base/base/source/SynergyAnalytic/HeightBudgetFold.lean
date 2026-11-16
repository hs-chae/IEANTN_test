import SynergyAnalytic.HeightBudgetBlocks
import SynergyAnalytic.HeightDataBounds
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem sumBudget_sound (count start:Nat) (hbound:start+count ≤ logCellCount)
    {acc out:ProofBox} {x:ℝ} (hx:RealBox.Contains p acc x)
    (hr:sumBudget count start acc=some out) :
    RealBox.Contains p out (x+∑j∈Finset.range count,budgetTerm (start+j)) := by
  induction count generalizing start acc x with
  | zero =>
    have ho : acc=out := by simpa only [sumBudget,Option.some.injEq] using hr
    subst out
    simpa only [Finset.sum_range_zero,add_zero] using hx
  | succ count ih =>
    cases hc:budgetCell start with
    | none => simp [sumBudget,hc] at hr
    | some cell =>
      have hs : start<logCellCount := by omega
      have hcell:=budgetCell_sound hs (D_domain start hs).2 hc
      have hr' : sumBudget count (start+1) (add acc cell)=some out := by
        simpa only [sumBudget,hc,Bind.bind,Option.bind] using hr
      have hh:=ih (start:=start+1) (by omega) (RealBox.add_sound hx hcell) hr'
      have hsum : (∑j∈Finset.range (count+1),budgetTerm (start+j))=
          budgetTerm start+∑j∈Finset.range count,budgetTerm (start+1+j) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
        exact add_comm _ _
      simpa only [hsum,add_assoc] using hh

def genericBudgetCheck (result:Option ProofBox) (cap:Option Int) : Bool := match result,cap with
  | some value,some word=>decide (value.hi ≤ word)
  | _,_=>false

theorem genericBudgetCheck_decode {result:Option ProofBox} {cap:Option Int}
    (h:genericBudgetCheck result cap=true) :
    ∃value word,result=some value ∧ cap=some word ∧ value.hi ≤ word := by
  cases result <;> cases cap <;> simp_all [genericBudgetCheck]

theorem budget_block_upper {b:Nat} (hb:b<24)
    (h:genericBudgetCheck (sumBudget 32 (32*b) zero) (blockWords[b]?)=true) :
    (∑j∈Finset.range 32,budgetTerm (32*b+j)) ≤ (blockWords[b]?.getD 0:ℝ)/(scale p:ℝ) := by
  obtain ⟨value,word,hr,hw,hv⟩:=genericBudgetCheck_decode h
  have hh:=sumBudget_sound 32 (32*b) (by norm_num [logCellCount];omega) zero_sound hr
  have hu : (∑j∈Finset.range 32,budgetTerm (32*b+j))*(scale p:ℝ) ≤ (value.hi:ℝ) := by
    simpa only [zero_add] using hh.2
  have hvR : (value.hi:ℝ) ≤ (word:ℝ) := by exact_mod_cast hv
  rw [hw,Option.getD_some]
  exact (le_div_iff₀ (RealBox.scale_real_pos p)).mpr (hu.trans hvR)

#print axioms sumBudget_sound
#print axioms budget_block_upper
end SynergyAnalytic.HeightPoint

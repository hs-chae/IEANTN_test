import SynergyAnalytic.HeightBudgetReal
import SynergyAnalytic.HeightPointSurvivalBox
import SynergyAnalytic.HeightPointWordBounds
import SynergyAnalytic.HeightReciprocal
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive VectorExpr
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem exactWord_sound (z:Int) : RealBox.Contains p (exactWord z) ((z:ℝ)/(scale p:ℝ)) := by
  have hS : (scale p:ℝ)≠0 := (RealBox.scale_real_pos p).ne'
  constructor <;> dsimp only [exactWord,RealBox.Contains] <;> field_simp <;> exact le_rfl

theorem env_cons {bs:List ProofBox} {xs:List ℝ} {b:ProofBox} {x:ℝ}
    (hb:RealBox.Contains p b x) (h:EnvSound bs xs) : EnvSound (b::bs) (x::xs) := by
  intro i out hi
  cases i with
  | zero =>
    have hout : b=out := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hi
    subst out
    exact ⟨x,rfl,hb⟩
  | succ i =>
    obtain ⟨v,hv,hm⟩:=h i out (by simpa only [List.getElem?_cons_succ] using hi)
    exact ⟨v,hv,hm⟩

theorem run_get_sound (program:List VectorExpr.Expr) {ctx:List ProofBox} {xs:List ℝ} {idx:Nat} {b:ProofBox}
    (hlen:ctx.length=xs.length) (henv:EnvSound ctx xs)
    (h:(VectorExpr.run program ctx >>= fun values=>values[idx]?)=some b) :
    RealBox.Contains p b ((VectorExpr.realRun program xs)[idx]?.getD 0) := by
  cases hr:VectorExpr.run program ctx with
  | none => simp [hr] at h
  | some values =>
    have hb : values[idx]?=some b := by simpa only [hr,Bind.bind,Option.bind] using h
    obtain ⟨x,hx,hm⟩:=(VectorExpr.run_sound program hlen henv hr).2 idx b hb
    simpa only [hx,Option.getD_some] using hm

noncomputable def budgetTerm (i:Nat) : ℝ :=
  2*((1/heightEndpoint i-1/heightEndpoint (i+1))*cValue i)*pairedFactor (DValue i) (1/8) 330

theorem budgetCell_sound {i:Nat} (hi:i<logCellCount) (hD:DValue i<330) {b:ProofBox}
    (hr:budgetCell i=some b) : RealBox.Contains p b (budgetTerm i) := by
  have h0:=survivalBox_sound i (Nat.le_of_lt hi)
  have h1:=survivalBox_sound (i+1) (Nat.succ_le_of_lt hi)
  have h2:=exactWord_sound (dataC i)
  have h3:=exactWord_sound (dataD i)
  have he : EnvSound [survivalBox i,survivalBox (i+1),exactWord (dataC i),exactWord (dataD i)]
      [survival i,survival (i+1),cValue i,DValue i] := by
    apply env_cons h0
    apply env_cons h1
    apply env_cons h2
    apply env_cons h3
    intro j out hj
    cases j <;> simp at hj
  have hb:=run_get_sound budgetProgram (idx:=budgetOutputIndex) (by rfl) he hr
  rw [budget_output_real,budget_output_formula _ _ _ _ hD] at hb
  simpa only [budgetTerm,reciprocal_cell_weight,WinnerOriginalScalars.height] using hb

theorem cValue_eq (i:Nat) : cValue i=baseC i+21600 := by
  unfold cValue dataC baseC
  push_cast
  have hS : (scale p:ℝ)≠0 := (RealBox.scale_real_pos p).ne'
  field_simp

theorem DValue_eq (i:Nat) : DValue i=baseD i := rfl

#print axioms budgetCell_sound
#print axioms cValue_eq
end SynergyAnalytic.HeightPoint

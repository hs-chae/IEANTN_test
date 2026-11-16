import SynergyHeightC.PointExecuteAPI
import SynergyAnalytic.HeightPointRunSound
import SynergyAnalytic.HeightPointReal
namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedC.Syntax ScopedC.Machine
open ScopedNumerical ScopedNumerical.ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
/-- The mathematical enclosures refer to the SAME interval records actually
read from the verified C output buffers, through the proved expression model.
The theorem does not attach an unused execution to independent PNT truth. -/
theorem source_and_model_enclosures {base : State} {input c d : ProofBox} {x : ℝ}
    (h : checked base input c d = true) (hm : modelOutputs input = some (c,d))
    (hx : SynergyBasis.RealBox.Contains 128 input x) :
    ∃ after, ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code 16
      "pointHeight" (args base input) (buffers base) .unit after ∧
      Machine.read SynergyC.Header.layout after (cAddress base) =
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (dAddress base) =
        some (SynergyC.SourceIntervalMath.represented d) ∧
      SynergyBasis.RealBox.Contains 128 c (SynergyAnalytic.HeightPoint.r184 x) ∧
      SynergyBasis.RealBox.Contains 128 d (SynergyAnalytic.HeightPoint.r186 x) := by
  cases hr : SynergyAnalytic.HeightPoint.point SynergyAnalytic.HeightPoint.constantValues input with
  | none => simp [modelOutputs,hr] at hm
  | some values =>
      cases hc : values[SynergyAnalytic.HeightPoint.mainIndex]? with
      | none => simp [modelOutputs,hr,hc] at hm
      | some c' =>
          cases hd : values[SynergyAnalytic.HeightPoint.slopeIndex]? with
          | none => simp [modelOutputs,hr,hc,hd] at hm
          | some d' =>
              have same : c'=c ∧ d'=d := by simpa only
                [modelOutputs,hr,hc,hd,Bind.bind,Option.bind,Pure.pure,
                  Option.some.injEq,Prod.mk.injEq] using hm
              rcases same with ⟨hcc,hdd⟩
              subst c'
              subst d'
              have env := (SynergyAnalytic.HeightPoint.point_sound hx hr).2
              obtain ⟨yc,hyc,hmc⟩ := env SynergyAnalytic.HeightPoint.mainIndex c hc
              obtain ⟨yd,hyd,hmd⟩ := env SynergyAnalytic.HeightPoint.slopeIndex d hd
              have outc := SynergyAnalytic.HeightPoint.main_real_output x
              have outd := SynergyAnalytic.HeightPoint.slope_real_output x
              change (SynergyAnalytic.HeightPoint.realPoint x)[SynergyAnalytic.HeightPoint.mainIndex]?.getD 0 = _ at outc
              rw [hyc] at outc
              change (SynergyAnalytic.HeightPoint.realPoint x)[SynergyAnalytic.HeightPoint.slopeIndex]?.getD 0 = _ at outd
              rw [hyd] at outd
              simp only [Option.getD_some] at outc outd
              obtain ⟨after,source,rc,rd,_⟩ := source_of_checked h
              exact ⟨after,source,rc,rd,outc ▸ hmc,outd ▸ hmd⟩


#print axioms source_and_model_enclosures
end SynergyHeightC.PointExecuteAPI

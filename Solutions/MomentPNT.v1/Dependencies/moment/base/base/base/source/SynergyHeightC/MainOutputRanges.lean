/- Concrete row-output applicability.  The recorded word is used only as a
kernel-checked upper bound for the actual model output, never as its replacement. -/
import SynergyHeightC.MainWeightData
import SynergyAnalytic.HeightGenericAll
import SynergyC.Word512
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical SynergyAnalytic SynergyAnalytic.HeightPoint
open SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem recorded_c_range_checks :
    (List.range logCellCount).all (fun i=>decide
      (cWords[i]?.getD 0+21600*ProofBox.scale 128 < (2:Int)^512))=true := by
  decide +kernel

theorem adjustedC_hi (c : ProofBox) :
    (adjustedC c).hi=c.hi+21600*ProofBox.scale 128 := by
  have hLit : ProofBox.literal 128 21600 1=
      ⟨21600*ProofBox.scale 128,21600*ProofBox.scale 128⟩ := by decide +kernel
  simp only [adjustedC,hLit,ProofBox.add]

theorem model_c_upper {i : Nat} (hi : i<logCellCount)
    (checked : cellDomain i=true) :
    (modelPair i).1.hi ≤ cWords[i]?.getD 0 := by
  obtain ⟨hl,hr,hm,hdomain⟩ := domain_spec (i:=i) checked
  obtain ⟨input,values,c,d,cw,dw,ht,hv,hc,hd,hcw,hdw,hcmp⟩ :=
    genericPointCheck_decode (kernel_generic_height_all i hi)
  have hmodel : modelOutputs input=some (c,d) := by
    simp only [modelOutputs,hv,hc,hd,Bind.bind,Option.bind,Pure.pure]
  have sameInput : input=gridInput (i+1) := Option.some.inj (ht.symm.trans hr)
  have hsame : modelOutputs input=some (modelPair i) :=
    (congrArg modelOutputs sameInput).trans hm
  have sameOutputs : (c,d)=modelPair i := Option.some.inj (hmodel.symm.trans hsame)
  have sameHigh : c.hi=(modelPair i).1.hi :=
    congrArg (fun pair : ProofBox × ProofBox=>pair.1.hi) sameOutputs
  have hcwValue : cWords[i]?.getD 0=cw := by rw [hcw]; rfl
  rw [hcwValue,←sameHigh]
  exact hcmp.1

private theorem integer_add_upper (a b c bound : Int)
    (hab : a ≤ b) (hb : b+c < bound) : a+c < bound := by omega

theorem row_output_ranges {i : Nat} (hi : i<logCellCount)
    (checked : cellDomain i=true) :
    SynergyC.Word512.Range (adjustedC (modelPair i).1).hi ∧
    SynergyC.Word512.Range (modelPair i).2.hi := by
  have hd := (domain_spec (i:=i) checked).2.2.2
  have hcUpper := model_c_upper hi checked
  have hword := (List.all_eq_true.mp recorded_c_range_checks) i (List.mem_range.mpr hi)
  have hword' : cWords[i]?.getD 0+21600*ProofBox.scale 128 < (2:Int)^512 :=
    of_decide_eq_true hword
  have hbig : 330*ProofBox.scale 128 < (2:Int)^512 := by decide +kernel
  refine ⟨⟨hd.2.2.2.2.2.2.1,?_⟩,
    ⟨hd.2.2.2.2.2.2.2.1,lt_trans hd.2.2.2.2.2.2.2.2.1 hbig⟩⟩
  rw [adjustedC_hi]
  exact integer_add_upper ((modelPair i).1.hi) (cWords[i]?.getD 0)
    (21600*ProofBox.scale 128) ((2:Int)^512) hcUpper hword' 

#print axioms recorded_c_range_checks
#print axioms adjustedC_hi
#print axioms model_c_upper
#print axioms row_output_ranges
end SynergyHeightC.MainWeightModel

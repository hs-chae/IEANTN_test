/- Pure interval-model endpoint caps. No C/source-execution module is imported. -/
import SynergyMomentMath.Bounds
import SynergyAnalytic.EndpointAnyWidth
namespace SynergyMomentMath.PointCaps
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 100000
noncomputable section

private theorem pair_exists (value : Option (ProofBox×ProofBox)) (word : Int×Int)
 (checked : WordModel.highPair (value.getD (⟨0,0⟩,⟨0,0⟩))=word)
 (positive : 0 < word.2) :
 ∃ pair,value=some pair ∧ WordModel.highPair pair=word := by
 cases value with
 | none=>
  have second:=congrArg Prod.snd checked
  change (0:Int)=word.2 at second
  omega
 | some pair=>exact ⟨pair,rfl,checked⟩

private theorem model_enclosures {input c d : ProofBox} {x : ℝ}
 (hm : WordModel.modelOutputs input=some (c,d)) (hx : RealBox.Contains 128 input x) :
 RealBox.Contains 128 c (r184 x) ∧ RealBox.Contains 128 d (r186 x) := by
 cases hr : point constantValues input with
 | none=>simp [WordModel.modelOutputs,hr] at hm
 | some values=>
  cases hc : values[mainIndex]? with
  | none=>simp [WordModel.modelOutputs,hr,hc] at hm
  | some c'=>
   cases hd : values[slopeIndex]? with
   | none=>simp [WordModel.modelOutputs,hr,hc,hd] at hm
   | some d'=>
    have same : c'=c ∧ d'=d := by
     simpa only [WordModel.modelOutputs,hr,hc,hd,Bind.bind,Option.bind,Pure.pure,
       Option.some.injEq,Prod.mk.injEq] using hm
    rcases same with ⟨hcc,hdd⟩
    subst c'
    subst d'
    have env:=(point_sound hx hr).2
    obtain ⟨yc,hyc,hmc⟩:=env mainIndex c hc
    obtain ⟨yd,hyd,hmd⟩:=env slopeIndex d hd
    have outc:=main_real_output x
    have outd:=slope_real_output x
    change (realPoint x)[mainIndex]?.getD 0=_ at outc
    rw [hyc] at outc
    change (realPoint x)[slopeIndex]?.getD 0=_ at outd
    rw [hyd] at outd
    simp only [Option.getD_some] at outc outd
    exact ⟨outc ▸ hmc,outd ▸ hmd⟩

private theorem word_reals (pair : ProofBox×ProofBox) (word : Int×Int)
 (checked : WordModel.highPair pair=word) :
 Real.realWord pair.1.hi=Real.realWord word.1-21600 ∧
 Real.realWord pair.2.hi=Real.realWord word.2 := by
 have hc:=congrArg Prod.fst checked
 have hd:=congrArg Prod.snd checked
 have shift : (ProofBox.literal 128 21600 1).hi=21600*ProofBox.scale 128 := by decide +kernel
 change pair.1.hi+(ProofBox.literal 128 21600 1).hi=word.1 at hc
 rw [shift] at hc
 constructor
 · have scalePos:=RealBox.scale_real_pos 128
   have casted : (pair.1.hi:ℝ)+21600*(ProofBox.scale 128:ℝ)=(word.1:ℝ) := by
    exact_mod_cast hc
   unfold Real.realWord
   apply (eq_sub_iff_add_eq).mpr
   apply (eq_div_iff scalePos.ne').mpr
   rw [add_mul,div_mul_cancel₀ _ scalePos.ne']
   exact casted
 · exact congrArg Real.realWord hd

theorem endpoint_caps
 (defined : ∀ i,i < 768→∃ left right,logCell i=some left ∧ logCell (i+1)=some right) :
 EndpointHeightCaps heightEndpoint (fun i=>Real.cValue i-21600) Real.dValue logCellCount := by
 intro i hi
 obtain ⟨left,right,hl,hr⟩:=defined i hi
 have rightInput : (logCell (i+1)).getD (⟨0,0⟩:ProofBox)=right :=
  congrArg (fun v : Option ProofBox=>v.getD ⟨0,0⟩) hr
 have resultIdentity : WordModel.outputs i=
   (WordModel.modelOutputs right).getD (⟨0,0⟩,⟨0,0⟩) :=
  (congrFun WordModel.outputs_function_exact i).trans (congrArg
    (fun value : ProofBox=>(WordModel.modelOutputs value).getD (⟨0,0⟩,⟨0,0⟩)) rightInput)
 have checked:=SourceMomentWordsV1.All.all_words i hi
 have actual : WordModel.highPair
   ((WordModel.modelOutputs right).getD (⟨0,0⟩,⟨0,0⟩))=SourceMomentWordsV1.All.word i :=
  Eq.mp (congrArg (fun pair : ProofBox×ProofBox=>
    WordModel.highPair pair=SourceMomentWordsV1.All.word i) resultIdentity) checked
 have wordPositive : (0:Int) < (SourceMomentWordsV1.All.word i).2 :=
  lt_of_lt_of_le (by decide +kernel : (0:Int) < 77*ProofBox.scale 128)
    (Bounds.integer_bounds i hi).2.2.1
 obtain ⟨pair,model,words⟩:=pair_exists (WordModel.modelOutputs right)
  (SourceMomentWordsV1.All.word i) actual wordPositive
 obtain ⟨c,d⟩:=pair
 have enclosure:=model_enclosures model (logCell_sound (Nat.succ_le_of_lt hi) hr)
 have main : r184 (logEndpoint (i+1)) ≤ Real.realWord c.hi :=
  (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr enclosure.1.2
 have slope : r186 (logEndpoint (i+1)) ≤ Real.realWord d.hi :=
  (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr enclosure.2.2
 have meanings:=word_reals (c,d) (SourceMomentWordsV1.All.word i) words
 rw [meanings.1,point_main_exact (logEndpoint_pos (i+1))] at main
 rw [meanings.2,point_slope_exact] at slope
 exact ⟨main,slope,(by have q:=(Bounds.d_range i hi).1;linarith)⟩

theorem actual_caps
 (defined : ∀ i,i < 768→∃ left right,logCell i=some left ∧ logCell (i+1)=some right)
 (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
 (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height) :
 ActualHeightCaps heightEndpoint Real.cValue Real.dValue logCellCount := by
 have caps:=endpoint_any_width_actual_height_caps (a:=heightEndpoint)
   (c:=fun i=>Real.cValue i-21600) (D:=Real.dValue) (n:=logCellCount) heightEndpoint_monotone
   heightEndpoint_zero heightEndpoint_last h (endpoint_caps defined) hRH
 have same : (fun i=>Real.cValue i-21600+21600)=Real.cValue := by funext i;ring
 rw [same] at caps
 exact caps
#print axioms endpoint_caps
#print axioms actual_caps
end
end SynergyMomentMath.PointCaps

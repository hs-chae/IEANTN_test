/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.GenericSource
open Real FKS2Scalar FKS2Table4 SumStability
namespace FKS2Pair.Old
def oldU (j : ℕ) : ℚ :=
  if j<10 then 1.6930e-12 else if j<20 then 1.6882e-12 else if j<30 then 1.6837e-12 else 1.6795e-12
def arg (j : ℕ) : ℚ := ((j:ℚ)-30)/2
def hi (j : ℕ) : ℚ := (330*oldU j/(300+j)^2)*(expHi 1-1)*expHi (arg j)^2
def literals : List String := ["0.0000000000009094947017729282379150390625", "0.0000000000009094947017729282379150390625", "0.0000000000020485459408897024100901640220711894088863325169569407080416567623615264892578125", "0.000000000005531829917302185148488522859572282777858298619122479067300446331501007080078125", "0.000000000014938307342881757897452412866081718212374340737369493581354618072509765625", "0.00000000004034069358614968731515700237620115908843132501715444959700107574462890625", "0.00000000010894183056054016720160323906618185692274369813503653858788311481475830078125", "0.000000000294208524792141046758043329982013937284879290245953598059713840484619140625", "0.00000000079455698928669188958540775300051946239410227690314059145748615264892578125", "0.000000002145872965100532252290299581906456161117802139415289275348186492919921875", "0.00000000577908389575161140188737637153788828658917964276042766869068145751953125", "0.000000015608317498931772501981446693401778258447620828519575297832489013671875", "0.00000004215626857022000242348515330892411157037713564932346343994140625", "0.0000001138615672860518887372875272874506169529240651172585785388946533203125", "0.00000030753958101767024725081678925009409653057446121238172054290771484375", "0.0000008306798749080193100253859117554355862012016586959362030029296875", "0.00000224375334347217498401154921194855518251642934046685695648193359375", "0.0000060607341693413729295032872645965227320630219765007495880126953125", "0.00001637133148535274351710773477197591319054481573402881622314453125", "0.0000442233214692598218704955304048098696512170135974884033203125", "0.000119142872128312634315283613517522098845802247524261474609375", "0.0003218492037149632751559524823647961966344155371189117431640625", "0.0008694512622260661995066133300724686705507338047027587890625", "0.00234880208057421970002653921483215526677668094635009765625", "0.006345355069377305555489154897941261879168450832366943359375", "0.0171424822892383456329756796776564442552626132965087890625", "0.046312658662094892403349177811833214946091175079345703125", "0.1251220611305639829335945023558451794087886810302734375", "0.338046302220092298451703527462086640298366546630859375", "0.9133275605746182801425447905785404145717620849609375"]
def data : List ℚ := literals.map fun s => (loadLiteral s).getD 0
def oldProgram : TransportProgram := ⟨literals,"0.000000000000003552713678800500929355621337890625","0.0000000000000000000000003492236819106224570749842044323542651977040183691099386744583195981046774836187296386924572288990020751953125","0.00000000000167950000000000006325582692276102616938705802684950185721390880644321441650390625","0.0000000000000051204268292682928950204700138082945508563614302188771176815862418152391910552978515625"⟩
def oldSource : String := include_str ".."/"c"/"fks2_table4_transport_old.c"
def st : CState := FKS2SumBridge.sumInitial data
def sumOut : ℚ := (runSum data 0).getD 0
def out : ℚ := decodeBits 0x3d7dba0e6c578b0f
theorem oldU_nonneg (j : ℕ) : (0:ℚ) ≤ oldU j := by unfold oldU;split_ifs <;> norm_num
theorem exp_checks : expCheck 1 (expLo 1) (expHi 1)=true ∧
    ∀ j ∈ Finset.range 30,expCheck (arg j) (expLo (arg j)) (expHi (arg j))=true := by native_decide
theorem enclosure_checks :
    data.length=30 ∧
    (∀ r ∈ data,FKS2SumBridge.inputCheck r=true) ∧
    (∀ j ∈ Finset.range 30,(2:ℚ)^48*hi j ≤ data[j]!) ∧
    ((List.range 30).filter (fun j => (2:ℚ)^48*hi j < 1/2^40)).length=2 ∧
    (∀ j ∈ Finset.range 30,(if (2:ℚ)^48*hi j < 1/2^40 then data[j]! = 1/2^40 else True)) := by
  native_decide
theorem cell_upper (j : ℕ) (hj : j ∈ Finset.range 30) :
    cellU (oldU j:ℝ) (300+j) ≤ (hi j:ℝ) := by
  have h1 := (expCheck_sound exp_checks.1).2
  norm_num only [Rat.cast_one] at h1
  have he := exp_pow_upper (n := 2) (exp_checks.2 j hj)
  have harg : (2:ℝ)*(arg j:ℝ) = (300+(j:ℝ))-330 := by simp [arg];ring
  norm_num only [Nat.cast_ofNat] at he
  rw [harg] at he
  have hu : (0:ℝ) ≤ (oldU j:ℝ) := by exact_mod_cast oldU_nonneg j
  have hfactor : (0:ℝ) ≤ 330*(oldU j:ℝ)/(300+(j:ℝ))^2 := by positivity
  have hexp : (0:ℝ) ≤ (expHi 1:ℝ)-1 := by linarith [add_one_le_exp (1:ℝ)]
  unfold cellU hi
  push_cast
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (by linarith : exp 1-1 ≤ (expHi 1:ℝ)-1) hfactor
  · simpa only [Rat.cast_pow] using he
  · positivity
  · positivity
theorem scaled_cell (j : ℕ) (hj : j ∈ Finset.range 30) :
    cellU (oldU j:ℝ) (300+j) ≤ (1/(2:ℝ)^48)*(data[j]!:ℝ) := by
  have hr : (2:ℝ)^48*(hi j:ℝ) ≤ (data[j]!:ℝ) := by exact_mod_cast enclosure_checks.2.2.1 j hj
  have hc := cell_upper j hj
  nlinarith
theorem source_tokens : (SumStability.tokens oldSource).isSome=true ∧
    SumStability.tokens oldSource = SumStability.tokens (renderTransport oldProgram) := by native_decide
theorem execution_checks : oldProgram.inputs.mapM loadLiteral=some data ∧
    RepresentsInput st data ∧ runSum data 0=some sumOut ∧ chainCheck data 0 sumOut=true ∧
    runSuffix oldProgram sumOut=some out := by unfold RepresentsInput;native_decide
theorem kernel_execution : ∃ final,ExecC selectedSumProgram st final sumOut := by
  have h := kernel_from_chain execution_checks.2.2.2.1
    (show data.length ≤ 64 by rw [enclosure_checks.1];norm_num)
  simpa [st,initialFor] using h
theorem kernel_stability : |(sumOut:ℝ)-(data.sum:ℚ)| ≤ (gamma 29:ℝ)*((data.map abs).sum:ℚ) := by
  obtain ⟨last,hexec⟩ := kernel_execution
  have hd : ValidInputs data := by
    intro r hr
    exact FKS2SumBridge.inputCheck_sound (enclosure_checks.2.1 r hr)
  simpa [enclosure_checks.1,exactSum,sumAbs] using c_sum_forward_error_real data st last sumOut
    (by rw [enclosure_checks.1];norm_num) hd execution_checks.2.1 hexec
-- The shared generic normalization, not the QRH-only cancellation.
theorem generic_cell_normalization (u b : ℝ) :
    330*exp (-330)*u*((exp (b+1)-exp b)/b^2) = cellU u b :=
  FKS2Pair.cell_normalization u b
def ratioCoeff : ℚ := oldU 29/oldU 0*(300/329)^2
theorem ratio_checks : expCheck 29 (expLo 29) (expHi 29)=true ∧
    (2:ℚ)^40 < ratioCoeff*expLo 29 := by native_decide
theorem ratio_obstruction : (2:ℝ)^40 < (ratioCoeff:ℝ)*exp 29 := by
  have he := (expCheck_sound ratio_checks.1).1
  have hrat : (2:ℝ)^40 < (ratioCoeff:ℝ)*(expLo 29:ℝ) := by exact_mod_cast ratio_checks.2
  have hp : (0:ℝ) ≤ (ratioCoeff:ℝ) := by norm_num [ratioCoeff,oldU]
  exact hrat.trans_le (mul_le_mul_of_nonneg_left he hp)
theorem ratio_identity : cellU (oldU 29:ℝ) 329 =
    (ratioCoeff:ℝ)*exp 29*cellU (oldU 0:ℝ) 300 := by
  have he : exp (-1:ℝ)=exp 29*exp (-30) := by rw [← exp_add];norm_num
  unfold cellU
  norm_num [oldU,ratioCoeff]
  rw [he]
  ring
theorem no_common_exact_scaling : ¬∃ s:ℝ,
    (1/(2:ℝ)^40) ≤ s*cellU (oldU 0:ℝ) 300 ∧ s*cellU (oldU 29:ℝ) 329 ≤ 1 := by
  rintro ⟨s,hlo,hhi⟩
  have hp : 0<s*cellU (oldU 0:ℝ) 300 := lt_of_lt_of_le (by norm_num) hlo
  have hm := mul_lt_mul_of_pos_right ratio_obstruction hp
  have hf : 1 ≤ (2:ℝ)^40*(s*cellU (oldU 0:ℝ) 300) := by nlinarith
  have hid : s*cellU (oldU 29:ℝ) 329 =
      ((ratioCoeff:ℝ)*exp 29)*(s*cellU (oldU 0:ℝ) 300) := by rw [ratio_identity];ring
  rw [hid] at hhi
  linarith

noncomputable def profile (j : ℕ) : ℝ := (oldU j:ℝ)
def scale : ℚ := (loadLiteral oldProgram.scale).getD 0
def anchorUpper : ℚ := (loadLiteral oldProgram.anchor).getD 0
def pointUpper : ℚ := (loadLiteral oldProgram.point).getD 0
def tailUpper : ℚ := (loadLiteral oldProgram.tail).getD 0

theorem source_checked : sourceMatches oldSource oldProgram=true := by
  unfold sourceMatches
  have hguard := source_tokens.1
  rw [source_tokens.2] at hguard ⊢
  simp [hguard]

end FKS2Pair.Old

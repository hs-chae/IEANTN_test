/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForwardRamanujan.Math
import ForwardRamanujan.Source

namespace ForwardRamanujan.Old
open Real IEANTN FKS2Scalar FKS2Table4 SumStability ForwardRamanujan
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def m : ℚ := -1194
def M : ℚ := 1426
def A : ℚ := 3914
def Y : ℚ := 3915
def targets : List ℚ := [2852,(2984/3915),(5992/15327225),(5896/20002028625),(22816/78307942066875),(2033476/919726779575446875),(2149636014196611085828125/1797607752008961505568)]
def literals : List String := ["0.6962890625","0.0001860831736909323240979075020362643044791184365749359130859375","0.000000095443932283893530335493952769521097678762089344672858715057373046875","0.00000000007196535671391181711166085848731255314447707860381342470645904541015625","0.0000000000009094947017729282379150390625","0.0000000000009094947017729282379150390625","0.2919510551965249778305633299169130623340606689453125"]
def data : List ℚ := literals.map fun s => (loadLiteral s).getD 0
def program : ForwardRamanujan.Program := ⟨literals,"4096.0","134.0","0.0"⟩
def actualSource : String := include_str ".."/"c"/"baseline.c"
def initial : CState := FKS2SumBridge.sumInitial data
def sumOut : ℚ := (runSum data 0).getD 0
def outputBits : ℕ := 0x40ae95302f2fc329
def out : ℚ := decodeBits outputBits
def scale : ℚ := 4096
def fixedOffset : ℚ := 134
def positiveOffset : ℚ := 0
def r0 : ℚ := (round64 (sumOut*scale)).getD 0
def r1 : ℚ := (round64 (r0-fixedOffset)).getD 0
def suffixError : ℚ := 1/10^10
def totalError : ℚ := forwardError scale sumOut suffixError data.length
def bound : ℚ := (39147/10)

theorem source_check : sourceMatches actualSource program=true := by native_decide

theorem enclosure_check : data.length=7 ∧ targets.length=7 ∧
    (∀ j ∈ Finset.range 7, (([2852,(2984/3915),(5992/15327225),(5896/20002028625),(22816/78307942066875),(2033476/919726779575446875),(2149636014196611085828125/1797607752008961505568)] : List ℚ))[j]!/4096 ≤ data[j]!) ∧
    (∀ j ∈ Finset.range 7, if (([2852,(2984/3915),(5992/15327225),(5896/20002028625),(22816/78307942066875),(2033476/919726779575446875),(2149636014196611085828125/1797607752008961505568)] : List ℚ))[j]!/4096 < 1/2^40 then data[j]! =1/2^40 else True) ∧
    targets.sum ≤ scale*data.sum := by native_decide

theorem domain_check : ∀ r ∈ data,FKS2SumBridge.inputCheck r=true := by native_decide

theorem execution_check : program.inputs.mapM loadLiteral=some data ∧
    RepresentsInput initial data ∧ runSum data 0=some sumOut ∧
    chainCheck data 0 sumOut=true ∧ suffix program sumOut=some out ∧
    finiteBits outputBits=true ∧ encodePositiveNormal out=some outputBits := by
  unfold RepresentsInput
  native_decide

theorem suffix_check : loadLiteral program.scale=some scale ∧
    loadLiteral program.fixedOffset=some fixedOffset ∧
    loadLiteral program.positiveOffset=some positiveOffset ∧
    additionCheck (sumOut*scale) r0=true ∧
    additionCheck (r0-fixedOffset) r1=true ∧
    additionCheck (r1-positiveOffset) out=true ∧
    r0=scale*sumOut ∧
    |r1-(r0-fixedOffset)|≤1/10^11 ∧
    |out-(r1-positiveOffset)|≤1/10^11 := by native_decide

theorem budget_check : (data.map abs).sum=data.sum ∧
    0≤gamma (data.length-1) ∧ gamma (data.length-1)<1 ∧
    0≤scale ∧ 0≤totalError ∧ totalError≤1/10^8 ∧
    out+totalError≤bound := by native_decide

theorem suffix_roundoff : |out-(scale*sumOut-fixedOffset-positiveOffset)|≤suffixError := by
  have h1 := abs_le.mp suffix_check.2.2.2.2.2.2.2.1
  have h2 := abs_le.mp suffix_check.2.2.2.2.2.2.2.2
  rw [suffix_check.2.2.2.2.2.2.1] at h1
  rw [abs_le]
  unfold suffixError
  constructor <;> linarith

theorem suffix_IEEE : ForwardRamanujan.SuffixIEEE program sumOut out := by
  exact ⟨scale,fixedOffset,positiveOffset,r0,r1,
    suffix_check.1,suffix_check.2.1,suffix_check.2.2.1,
    additionCheck_sound suffix_check.2.2.2.1,
    additionCheck_sound suffix_check.2.2.2.2.1,
    additionCheck_sound suffix_check.2.2.2.2.2.1⟩

theorem concrete_execution : Exec actualSource program initial out := by
  obtain ⟨final,hkernel⟩ := ForwardRamanujan.kernel_from_chain execution_check.2.2.2.1
    (show data.length≤64 by rw [enclosure_check.1];norm_num)
  exact ⟨source_check,by decide,by decide,data,sumOut,final,execution_check.1,
    execution_check.2.1,execution_check.2.2.1,hkernel,execution_check.2.2.2.2.1,suffix_IEEE⟩

/-- Domain evidence is a parameter so an independently checked kernel certificate can replace it. -/
theorem verified_with_domain (hd : ValidInputs data) {q : ℚ}
    (he : Exec actualSource program initial q) :
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) := by
  have hn : 1≤data.length ∧ data.length≤64 := by rw [enclosure_check.1];norm_num
  have hg : (gamma (data.length-1):ℝ)<1 := by exact_mod_cast budget_check.2.2.1
  have href : (targets.sum:ℝ)≤(scale:ℝ)*(data.sum:ℝ) := by
    exact_mod_cast enclosure_check.2.2.2.2
  have hf : |(out:ℝ)-((scale:ℝ)*(sumOut:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ))|≤(suffixError:ℝ) := by
    exact_mod_cast suffix_roundoff
  exact source_linked_upper he execution_check.1 execution_check.2.2.1
    execution_check.2.2.2.2.1 hn hd budget_check.1 hg budget_check.2.2.2.1 href hf

theorem checked_domain : ValidInputs data := by
  intro r hr
  exact FKS2SumBridge.inputCheck_sound (domain_check r hr)

theorem verified_transport {q : ℚ} (he : Exec actualSource program initial q) :
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) :=
  verified_with_domain checked_domain he

theorem selected_execution_witness : ∃ q : ℚ, Exec actualSource program initial q ∧
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ)≤(q:ℝ)+(totalError:ℝ) :=
  ⟨out,concrete_execution,verified_transport concrete_execution⟩

theorem terms_cast : (targets.sum:ℝ)=(terms (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)).sum := by
  norm_num [targets,terms,m,M,A,Y,List.sum_cons,List.sum_nil]

theorem upper_as_targets : upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)=
    (targets.sum:ℝ)-(fixedOffset:ℝ)-(positiveOffset:ℝ) := by
  rw [upper,←terms_cast]
  norm_num [m,fixedOffset,positiveOffset]

theorem certified_upper_with_domain (hd : ValidInputs data) :
    upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)≤(bound:ℝ) := by
  rw [upper_as_targets]
  have h := verified_with_domain hd concrete_execution
  have hb : (out:ℝ)+(totalError:ℝ)≤(bound:ℝ) := by
    exact_mod_cast budget_check.2.2.2.2.2.2
  exact h.trans hb

theorem certified_upper : upper (m:ℝ) (M:ℝ) (A:ℝ) (Y:ℝ)≤(bound:ℝ) :=
  certified_upper_with_domain checked_domain

theorem epsilon_bound : ∀ x>exp (Y:ℝ),
    DudekPlatt.v3.εUpper (M:ℝ) x-DudekPlatt.v3.εLower (m:ℝ) (exp (A:ℝ)) x≤(bound:ℝ) := by
  intro x hx
  have hY : (0:ℝ)<(Y:ℝ) := by norm_num [Y]
  have hM : (0:ℝ)≤(M:ℝ) := by norm_num [M]
  have hlog : (Y:ℝ)≤log x := by
    have ht := log_lt_log (exp_pos (Y:ℝ)) hx
    rw [log_exp] at ht
    exact ht.le
  exact (epsilon_majorant hM hY hlog).trans certified_upper
end ForwardRamanujan.Old

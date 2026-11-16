/- Operational output interface independent of a particular bounded executor.
   Every successful alternative provider still supplies actual C source calls,
   actual pointer reads, and equality with the proved interval-expression model. -/
import SynergyHeightC.PointEndpointCaps
namespace SynergyHeightC.PointExecuteAPI
open ScopedC ScopedC.Machine ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive SynergyAnalytic SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The records are read from the actual source-call output buffers. The call
rank is existential, so any sound evaluator of the SAME source semantics can
supply the evidence, including proved-callee acceleration. -/
def SourcePointOutputs (base : State) (input c d : ProofBox) : Prop :=
  ∃ rank after, ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code rank
    "pointHeight" (args base input) (buffers base) .unit after ∧
    Machine.read SynergyC.Header.layout after (cAddress base) =
      some (SynergyC.SourceIntervalMath.represented c) ∧
    Machine.read SynergyC.Header.layout after (dAddress base) =
      some (SynergyC.SourceIntervalMath.represented d)

/-- No numerical premise is silently discharged here: all768 source calls and
same-output model identities must actually be supplied to close this provider. -/
def SourcePointOutputsProvider (base : State) : Prop :=
  ∀ i < logCellCount, ∃ input c d,
    logCell (i+1) = some input ∧ modelOutputs input = some (c,d) ∧
      SourcePointOutputs base input c d

theorem source_outputs_of_checked {base : State} {input c d : ProofBox}
    (h : checked base input c d = true) : SourcePointOutputs base input c d := by
  obtain ⟨after,source,rc,rd,_⟩ := source_of_checked h
  exact ⟨16,after,source,rc,rd⟩

/-- Generic interval-model correctness for the boxes identified with actual
source output records by SourcePointOutputs. -/
theorem model_output_enclosures {input c d : ProofBox} {x : ℝ}
    (hm : modelOutputs input = some (c,d))
    (hx : RealBox.Contains 128 input x) :
    RealBox.Contains 128 c (r184 x) ∧ RealBox.Contains 128 d (r186 x) := by
  cases hr : point constantValues input with
  | none => simp [modelOutputs,hr] at hm
  | some values =>
      cases hc : values[mainIndex]? with
      | none => simp [modelOutputs,hr,hc] at hm
      | some c' =>
          cases hd : values[slopeIndex]? with
          | none => simp [modelOutputs,hr,hc,hd] at hm
          | some d' =>
              have same : c'=c ∧ d'=d := by simpa only
                [modelOutputs,hr,hc,hd,Bind.bind,Option.bind,Pure.pure,
                  Option.some.injEq,Prod.mk.injEq] using hm
              rcases same with ⟨hcc,hdd⟩
              subst c'
              subst d'
              have env := (point_sound hx hr).2
              obtain ⟨yc,hyc,hmc⟩ := env mainIndex c hc
              obtain ⟨yd,hyd,hmd⟩ := env slopeIndex d hd
              have outc := main_real_output x
              have outd := slope_real_output x
              change (realPoint x)[mainIndex]?.getD 0 = _ at outc
              rw [hyc] at outc
              change (realPoint x)[slopeIndex]?.getD 0 = _ at outd
              rw [hyd] at outd
              simp only [Option.getD_some] at outc outd
              exact ⟨outc ▸ hmc,outd ▸ hmd⟩

/-- The enclosure is a property of the interval read at each actual pointer,
not a parallel numerical result detached from that read. -/
theorem source_output_enclosures {base : State} {input c d : ProofBox} {x : ℝ}
    (source : SourcePointOutputs base input c d)
    (hm : modelOutputs input = some (c,d))
    (hx : RealBox.Contains 128 input x) :
    ∃ rank after, ArraySourceCalls.SourceCall SynergyC.Header.layout Bundle.code rank
      "pointHeight" (args base input) (buffers base) .unit after ∧
      Machine.read SynergyC.Header.layout after (cAddress base) =
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (dAddress base) =
        some (SynergyC.SourceIntervalMath.represented d) ∧
      RealBox.Contains 128 c (r184 x) ∧ RealBox.Contains 128 d (r186 x) := by
  obtain ⟨rank,after,call,rc,rd⟩ := source
  obtain ⟨hc,hd⟩ := model_output_enclosures hm hx
  exact ⟨rank,after,call,rc,rd,hc,hd⟩

/-- Lift the original checked evaluator without requiring any replacement
executor to prove Boolean equivalence to that evaluator. -/
theorem outputs_provider_of_checks {base : State} (hsource : SourcePointChecks base)
    (hwords : ∀ i < logCellCount, genericPointCheck (logCell (i+1))
      (point constantValues) (cWords[i]?) (DWords[i]?) mainIndex slopeIndex = true) :
    SourcePointOutputsProvider base := by
  intro i hi
  obtain ⟨input,values,c,d,cw,dw,ht,hv,hc,hd,hcw,hdw,hcmp⟩ :=
    genericPointCheck_decode (hwords i hi)
  have hm : modelOutputs input = some (c,d) := by
    simp only [modelOutputs,hv,hc,hd,Bind.bind,Option.bind,Pure.pure]
  have hs := hsource i hi
  have hin : pointInput i = input := by simp only [pointInput,ht,Option.getD_some]
  rw [hin] at hs
  have checked : checked base input c d = true := by
    simpa only [checkedModel,hm] using hs
  exact ⟨input,c,d,ht,hm,source_outputs_of_checked checked⟩

#print axioms source_outputs_of_checked
#print axioms model_output_enclosures
#print axioms source_output_enclosures
#print axioms outputs_provider_of_checks
end SynergyHeightC.PointExecuteAPI

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTraceTwiddles
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFT.IntegerModel

/-- A genuine execution itself supplies the exact size of every used stage. -/
theorem ExecutionTrace.stage_length {stages : Nat → List CInt} {input : Nat → CInt}
    {s index step : Nat} {out : List CInt} (h : ExecutionTrace stages input s index step out) :
    ∀t,t<s → (stages (t+1)).length=2^t := by
  induction h with
  | leaf index step => intro t ht;omega
  | node s index step as bs ps qs left right merge ihl ihr =>
    intro t ht
    by_cases top : t=s
    · subst t;exact merge.lengths.2.1.symm.trans left.output_length
    · exact ihl t (by omega)

/-- Transfer an independent integer execution using only equal source-domain
inputs and equal complete used stages. No large literal output is evaluated. -/
theorem ExecutionTrace.transfer {aStages bStages : Nat → List CInt} {aInput bInput : Nat → CInt}
    {s index step : Nat} {out : List CInt}
    (h : ExecutionTrace aStages aInput s index step out)
    (stageEq : ∀t,t<s → aStages (t+1)=bStages (t+1))
    (inputEq : ∀j,j<2^s → aInput (index+step*j)=bInput (index+step*j)) :
    ExecutionTrace bStages bInput s index step out := by
  induction h with
  | leaf index step =>
    have same:=inputEq 0 (by norm_num)
    simp only [Nat.mul_zero,Nat.add_zero] at same
    rw [same]
    exact .leaf index step
  | node s index step as bs ps qs left right merge ihl ihr =>
    have stageBelow : ∀t,t<s → aStages (t+1)=bStages (t+1) := fun t ht=>stageEq t (by omega)
    have evenInput : ∀j,j<2^s → aInput (index+(step*2)*j)=bInput (index+(step*2)*j) := by
      intro j hj
      have same:=inputEq (2*j) (by rw [Nat.pow_succ];omega)
      simpa only [Nat.mul_assoc] using same
    have oddInput : ∀j,j<2^s → aInput ((index+step)+(step*2)*j)=bInput ((index+step)+(step*2)*j) := by
      intro j hj
      have same:=inputEq (2*j+1) (by rw [Nat.pow_succ];omega)
      simpa only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using same
    apply ExecutionTrace.node s index step as bs ps qs (ihl stageBelow evenInput) (ihr stageBelow oddInput)
    rw [←stageEq s (by omega)]
    exact merge

/-- Two true executions agree from pointwise equality on every used input
and stage entry. Stage lengths are derived from the executions themselves. -/
theorem ExecutionTrace.outputs_eq {aStages bStages : Nat → List CInt} {aInput bInput : Nat → CInt}
    {s index step : Nat} {aOut bOut : List CInt}
    (a : ExecutionTrace aStages aInput s index step aOut)
    (b : ExecutionTrace bStages bInput s index step bOut)
    (inputEq : ∀j,j<2^s → aInput (index+step*j)=bInput (index+step*j))
    (entryEq : ∀t,t<s → ∀j,j<2^t →
      (aStages (t+1)).getD j (0,0)=(bStages (t+1)).getD j (0,0)) : aOut=bOut := by
  have stageEq : ∀t,t<s → aStages (t+1)=bStages (t+1) := by
    intro t ht
    have al:=a.stage_length t ht
    have bl:=b.stage_length t ht
    apply List.ext_getElem (al.trans bl.symm)
    intro i hi hj
    have same:=entryEq t ht i (by omega)
    simpa only [List.getD_eq_getElem,hi,hj,if_pos] using same
  exact (a.transfer stageEq inputEq).deterministic b

/-- Full root transform form consumed by the actual source/certificate bridge. -/
theorem ExecutionTrace.root_outputs_eq {aStages bStages : Nat → List CInt} {aInput bInput : Nat → CInt}
    {S : Nat} {aOut bOut : List CInt}
    (a : ExecutionTrace aStages aInput S 0 1 aOut)
    (b : ExecutionTrace bStages bInput S 0 1 bOut)
    (inputEq : ∀j,j<2^S → aInput j=bInput j)
    (entryEq : ∀t,t<S → ∀j,j<2^t →
      (aStages (t+1)).getD j (0,0)=(bStages (t+1)).getD j (0,0)) : aOut=bOut :=
  a.outputs_eq b (by simpa using inputEq) entryEq

#print axioms ExecutionTrace.transfer
#print axioms ExecutionTrace.outputs_eq
#print axioms ExecutionTrace.root_outputs_eq
end RH080Next.FFT.IntegerModel

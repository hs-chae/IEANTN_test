/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.PVFloorProgram
import PVEvolutionA.Recovery.StepGrid
namespace PVEvolutionA.Recovery.PVFloor
open Real LeanCert.Core LeanCert.Engine WinnerDensityA WinnerDensityA.Program
set_option maxHeartbeats 0

theorem list_range_sum (f : Nat→ℝ) (n : Nat) :
    ((List.range n).map f).sum=∑ i∈Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ,List.map_append,List.sum_append,ih,
      Finset.sum_range_succ];simp

theorem one_row (e : Expr) : WinnerProgramA.rowValue ⟨e,1⟩=Expr.eval (sumBodyRealEnv 0) e := by
  simp [WinnerProgramA.rowValue]

theorem program_semantics : WinnerProgramA.value program=
    StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells 331 := by
  simp only [WinnerProgramA.value,program,List.map_cons,List.map_map,List.sum_cons]
  rw [list_range_sum]
  simp only [Function.comp_apply,one_row,Expr.eval,weightExpr,lit,mul,sub,WinnerProgramA.sub]
  push_cast
  simp only [sigmaQ_cast]
  unfold StepGrid.weighted
  rw [graded_zero (by decide : 0<cells)]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · have he : -(331:ℝ)/8=331*((3/4:ℝ)-7/8) := by norm_num
    rw [he]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [sub_eq_add_neg]

theorem box_moment (hb : boxesAccepted) (j : Nat) (hj : j<cells)
    {s : ℝ} (hs : (sigmaQ cells j:ℝ)≤s ∧ s≤(sigmaQ cells (j+1):ℝ)) :
    (cap j:ℝ)≤momentOnly s := by
  have hmem : s∈box j := hs
  have h:=BoxLower.sound (hb ⟨j,hj⟩) hmem
  simpa only [moment_semantics] using h

theorem point_in_box (j k : Nat) (hk : k<16) :
    (sigmaQ cells j:ℝ)≤gradedGrid (cells*16) (j*16+k) ∧
      gradedGrid (cells*16) (j*16+k)≤(sigmaQ cells (j+1):ℝ) := by
  rw [sigmaQ_cast,sigmaQ_cast,
    ←StepGrid.graded_refinement (by decide : 0<cells) (by decide : 0<16) j,
    ←StepGrid.graded_refinement (by decide : 0<cells) (by decide : 0<16) (j+1)]
  exact ⟨graded_monotone _ (by omega),graded_monotone _ (by omega)⟩

theorem lower_grid (hb : boxesAccepted) {L τ : ℝ} (hL : 0≤L) (hτ : 0<τ) :
    StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells L≤
      gridCoefficient (fun s=>SlopedProgram.mathEnvelope s τ) (gradedGrid 65536) 65536 L := by
  have hfin:=StepGrid.refinement_lower (gradedGrid (cells*16))
    (fun s=>SlopedProgram.mathEnvelope s τ) (fun i=>(cap i:ℝ)) cells 16
    (graded_monotone _) hL
    ((box_moment hb 0 (by decide) (point_in_box 0 0 (by decide))).trans
      (moment_le_envelope _ _ hτ))
    (fun j hj k hk=>(box_moment hb j hj (point_in_box j k hk)).trans
      (moment_le_envelope _ _ hτ))
  have hgrid : (fun j=>gradedGrid (cells*16) (j*16))=gradedGrid cells :=
    funext (StepGrid.graded_refinement (by decide) (by decide))
  rw [hgrid] at hfin
  exact hfin

theorem floor_coefficient (hb : boxesAccepted) (ha : arithmetic) (ht : totalAccepted=true)
    {L τ : ℝ} (hL : 0≤L) (hU : L≤331) (hτ : 0<τ) :
    (floor:ℝ)≤Sloped.coefficient 65536 L τ := by
  have hc : ∀i<cells,(cap (i+1):ℝ)≤(cap i:ℝ) := by
    intro i hi
    exact_mod_cast (ha ⟨i,hi⟩).2
  have hlast : gradedGrid cells cells=(7/8:ℝ):=graded_last _
  have hmono:=StepGrid.antitone (gradedGrid cells) (fun i=>(cap i:ℝ)) cells
    (fun i hi=>(graded_monotone cells hi).trans_eq hlast) hc hlast hU
  have hp : (floor:ℝ)≤StepGrid.weighted (gradedGrid cells) (fun i=>(cap i:ℝ)) cells 331 := by
    rw [←program_semantics]
    exact lower_of_execution ht
  have hgrid:=(hp.trans hmono).trans (lower_grid hb hL hτ)
  unfold Sloped.coefficient
  have htail : 0≤exp (-L/8)*((τ+1/10^9)^2/(2*Real.pi)+
      (2+1/Real.pi)*(τ+1/10^9))+1/10^12 := by positivity
  linarith
#print axioms program_semantics
#print axioms floor_coefficient
end PVEvolutionA.Recovery.PVFloor

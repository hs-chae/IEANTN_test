/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Partitioned execution of the unchanged8192-cell AST; all ranges are proved to cover it. -/
import PVEvolutionA.Recovery.RayProgram
import PVEvolutionA.Recovery.StepGrid
namespace PVEvolutionA.Recovery.Chunks
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def size : Nat := 1024
def count : Nat := 8
def body : Expr := Numerical.gradedTerm 330 100 Ray.sigmaCells
def first (i : Nat) := i*size
def last (i : Nat) := first i+size-1
def bounds : Array ℚ := #[1011/1000000000000,543/25000000000,4876271/1000000000000,187703387/1000000000000,799617681/500000000000,384518333/100000000000,740671277/250000000000,534909073/1000000000000]
def bound (i : Nat) : ℚ := bounds[i]!
def runSlice (i : Nat) : IntervalDyadic × Bool :=
  CH2QRH.DensityComputation.checkedSumAux body (first i) (last i) finSumZero
    (LeanCert.Internal.Dyadic.prepareContext PVEvolutionA.Fast.cfg)
def Exec (i : Nat) (out : IntervalDyadic × Bool) : Prop := out=runSlice i
def accepted (i : Nat) : Bool := (runSlice i).2 && (runSlice i).1.upperBoundedBy (bound i)
def baseProgram : List Row := [⟨Numerical.base 330 100,1⟩]
def baseOutput := PVEvolutionA.Fast.run baseProgram
def baseAccepted : Bool := acceptUpper baseOutput [3/1000000000000]

theorem execution (i : Nat) : Exec i (runSlice i) := rfl
theorem nonempty_execution (i : Nat) : ∃out,Exec i out := ⟨runSlice i,execution i⟩

noncomputable def sliceValue (i : Nat) : ℝ :=
  ∑ k∈Finset.range size, Expr.eval (sumBodyRealEnv (first i+k)) body
noncomputable def representedCoefficient : ℝ :=
  WinnerProgramA.value baseProgram+∑i∈Finset.range count,sliceValue i

theorem slice_to_Icc (f : Nat→ℝ) (start : Nat) :
    (∑ k∈Finset.range size,f (start+k))=∑ k∈Finset.Icc start (start+size-1),f k := by
  apply Finset.sum_bij (fun k _=>start+k)
  · intro k hk
    have hk':=Finset.mem_range.mp hk
    simp only [Finset.mem_Icc]
    norm_num [size] at hk' ⊢
    omega
  · intro a _ b _ h
    omega
  · intro k hk
    have hh:=Finset.mem_Icc.mp hk
    refine ⟨k-start,?_,?_⟩
    · apply Finset.mem_range.mpr
      norm_num [size] at hh ⊢
      omega
    · omega
  · intro k _
    rfl

theorem slice_upper {i : Nat} (hc : accepted i=true) : sliceValue i≤(bound i:ℝ) := by
  unfold sliceValue
  rw [slice_to_Icc (fun k=>Expr.eval (sumBodyRealEnv k) body) (first i)]
  apply CH2QRH.DensityComputation.verify_upper body (first i) (last i)
    (bound i) PVEvolutionA.Fast.cfg (by decide)
  exact hc

theorem coefficient_semantics : representedCoefficient=Numerical.coefficient Ray.sigmaCells 330 100 := by
  have h:=Numerical.program_semantics 330 100 (by norm_num [Ray.sigmaCells] : 0<Ray.sigmaCells)
    (by norm_num : (0:ℝ)<(100:ℚ))
  norm_num only [Rat.cast_ofNat] at h
  rw [←h]
  simp only [representedCoefficient,WinnerProgramA.value,baseProgram,Numerical.program,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  apply congrArg₂ (fun a b : ℝ=>a+b) rfl
  unfold sliceValue first
  unfold WinnerProgramA.rowValue
  have hs : Finset.Icc 0 (Ray.sigmaCells-1)=Finset.range (count*size) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_range]
    norm_num [Ray.sigmaCells,count,size]
    omega
  rw [hs,StepGrid.sum_blocks]
  rfl

theorem coefficient_of_checks (hbase : baseAccepted=true)
    (hc : ∀i:Fin count,accepted i.val=true) :
    Numerical.coefficient Ray.sigmaCells 330 100≤(9134699/1000000000:ℝ) := by
  rw [←coefficient_semantics]
  have hb:=PVEvolutionA.Fast.source_linked_upper baseProgram [3/1000000000000] hbase
  norm_num only [List.sum_cons,List.sum_nil,add_zero,Rat.cast_div,Rat.cast_ofNat] at hb
  have hh : (∑i∈Finset.range count,sliceValue i)≤∑i∈Finset.range count,(bound i:ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact slice_upper (hc ⟨i,Finset.mem_range.mp hi⟩)
  have ha : (3/1000000000000:ℝ)+∑i∈Finset.range count,(bound i:ℝ)≤9134699/1000000000 := by
    norm_num [count,Finset.sum_range_succ,bound,bounds]
  unfold representedCoefficient
  linarith
#print axioms coefficient_semantics
#print axioms coefficient_of_checks
end PVEvolutionA.Recovery.Chunks

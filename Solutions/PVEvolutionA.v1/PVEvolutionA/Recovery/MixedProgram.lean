/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- The identical disjoint ranges and caps, with more Taylor terms on ranges4–6. -/
import PVEvolutionA.Recovery.ChunksProgram
namespace PVEvolutionA.Recovery.Mixed
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def cfg (i : Nat) : DyadicConfig :=
  if i=4 ∨ i=5 ∨ i=6 then { precision := -80, taylorDepth := 20 } else PVEvolutionA.Fast.cfg
def run (i : Nat) : IntervalDyadic × Bool :=
  CH2QRH.DensityComputation.checkedSumAux Chunks.body (Chunks.first i) (Chunks.last i) finSumZero
    (LeanCert.Internal.Dyadic.prepareContext (cfg i))
def Exec (i : Nat) (out : IntervalDyadic × Bool) : Prop := out=run i
def accepted (i : Nat) : Bool := (run i).2 && (run i).1.upperBoundedBy (Chunks.bound i)
 theorem execution (i : Nat) : Exec i (run i) := rfl
 theorem nonempty_execution (i : Nat) : ∃out,Exec i out := ⟨run i,execution i⟩
 theorem fast_eq {i : Nat} (h : ¬(i=4 ∨ i=5 ∨ i=6)) : accepted i=Chunks.accepted i := by
  simp only [accepted,run,cfg,if_neg h,Chunks.accepted,Chunks.runSlice]
 theorem slice_upper {i : Nat} (hc : accepted i=true) : Chunks.sliceValue i≤(Chunks.bound i:ℝ) := by
  unfold Chunks.sliceValue
  rw [Chunks.slice_to_Icc (fun k=>Expr.eval (sumBodyRealEnv k) Chunks.body) (Chunks.first i)]
  apply CH2QRH.DensityComputation.verify_upper Chunks.body (Chunks.first i) (Chunks.last i)
    (Chunks.bound i) (cfg i)
  · unfold cfg
    split_ifs <;> decide
  · exact hc
 theorem coefficient_of_checks (hbase : Chunks.baseAccepted=true)
    (hc : ∀i:Fin Chunks.count,accepted i.val=true) :
    Numerical.coefficient Ray.sigmaCells 330 100≤(1826923053/200000000000:ℝ) := by
  rw [←Chunks.coefficient_semantics]
  have hb:=PVEvolutionA.Fast.source_linked_upper Chunks.baseProgram [3/1000000000000] hbase
  norm_num only [List.sum_cons,List.sum_nil,add_zero,Rat.cast_div,Rat.cast_ofNat] at hb
  have hh : (∑i∈Finset.range Chunks.count,Chunks.sliceValue i)≤
      ∑i∈Finset.range Chunks.count,(Chunks.bound i:ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact slice_upper (hc ⟨i,Finset.mem_range.mp hi⟩)
  have ha : (3/1000000000000:ℝ)+∑i∈Finset.range Chunks.count,(Chunks.bound i:ℝ)=
      1826923053/200000000000 := by
    norm_num [Chunks.count,Finset.sum_range_succ,Chunks.bound,Chunks.bounds]
  unfold Chunks.representedCoefficient
  linarith
#print axioms slice_upper
#print axioms coefficient_of_checks
end PVEvolutionA.Recovery.Mixed

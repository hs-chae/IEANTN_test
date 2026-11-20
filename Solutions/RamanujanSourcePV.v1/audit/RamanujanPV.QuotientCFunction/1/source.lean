/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCFunctionPrefix
import RamanujanPV.QuotientCWhole
import RamanujanPV.QuotientCDeterminism

/-! Complete source-bound optimized count function. The prefix executes real
initialization from arbitrary original buffer contents, the actual outer loop
establishes the survivor invariant, and the source returns its actual table read.
This proves source-program correctness; a concrete native result/certificate and
physical compiler/runtime/ABI association are separate obligations. -/
namespace RamanujanPV.QuotientCFunction
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientTables QuotientCExecute QuotientCRound
open QuotientCFunctionPrefix
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem source_shape : QuotientCSourceV2.countFunction.body =
    .sequence (prefixStatements++[QuotientCWhole.outerFor,
      .returnStmt (.index (.var "large") (.nat 1))]) := rfl

/-- Whole actual optimized C function, for every supported mathematical input.
No initial table values, count output, successful guard, prime list, or source
execution is assumed. The supplied allocation metadata and valid argument range
are the actual source call's applicability conditions. -/
theorem function_refines (N capacity sb lb : Nat) (heap : Heap)
    (hN2 : 2 ≤ N) (hN : N ≤ 2000000000000) (hcap : N.sqrt < capacity)
    (_capacityWord : capacity < modulus)
    (owned : Owned heap) (buffers : QuotientCInit.Buffers heap sb lb N.sqrt) :
    ∃ t, Run QuotientSqrtExecute.service QuotientCSourceV2.countFunction.body
        (input N capacity sb lb heap) (.returned t (.u64 (Nat.primeCounting N))) ∧
      t.env=(input N capacity sb lb heap).env ∧ Owned t.heap := by
  let initial := input N capacity sb lb heap
  obtain ⟨initialized,first,envFirst,ownedFirst,repFirst⟩ := prefix_exec
    (s:=initial) hN2 hN hcap owned buffers
    (by simp [initial,input]) (by simp [initial,input])
    (by simp [initial,input]) (by simp [initial,input])
    (by simp [initial,input,emptyEnv]) (by simp [initial,input,emptyEnv])
  have hr1 : 1 ≤ N.sqrt := Nat.sqrt_pos.mpr (by omega)
  have roundEnv : RoundEnv sb lb N N.sqrt 2 (bind initialized.env "p" (.u64 2)) := by
    constructor <;> simp [envFirst,initial,input,emptyEnv]
  have freshP : initialized.env "p"=none := by simp [envFirst,initial,input,emptyEnv]
  obtain ⟨last,U,outer,envLast,ownedLast,repLast,invariant⟩ :=
    QuotientCWhole.outer_for_exec hN2 hN rfl ownedFirst repFirst roundEnv freshP
  have frontier : N < (N.sqrt+1)*(N.sqrt+1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt N
  have count : U.large 1=Nat.primeCounting N := by
    calc
      U.large 1=QuotientSieve.total (N.sqrt+1) (N/1) := invariant.2 1 (by omega) hr1
      _=Nat.primeCounting N := by rw [Nat.div_one]; exact QuotientSieve.total_final frontier
  have largeEnv : last.env "large"=some (.ptr lb) := by simp [envLast,envFirst,initial,input]
  have readCount : QuotientCMachine.read last.heap lb 1=some (.u64 (Nat.primeCounting N)) := by
    simpa only [count] using repLast.2.2 1 (by omega) hr1
  let final := closeScope initial last
  have envFinal : final.env=initial.env := by
    funext name
    by_cases hr : name="r"
    · subst name
      simp [final,closeScope,initial,input,emptyEnv]
    · simp only [final,closeScope,envLast,envFirst,QuotientCMachine.bind,Function.update_of_ne hr]
      cases h : initial.env name <;> simp [h]
  refine ⟨final,?_,envFinal,ownedLast⟩
  rw [source_shape]
  apply StmtRun.sequence (inner:=.returned last (.u64 (Nat.primeCounting N)))
  · exact seq_append first (SeqRun.next outer (SeqRun.returned (return_large largeEnv readCount)))
  · rfl

/-- Every completed run of the same actual source under the same initial
application-owned buffers returns the mathematically correct prime count. This
uses source execution determinism, not a native-execution axiom. -/
theorem completed_execution_correct {N capacity sb lb : Nat} {heap : Heap}
    (hN2 : 2 ≤ N) (hN : N ≤ 2000000000000) (hcap : N.sqrt < capacity)
    (capacityWord : capacity < modulus)
    (owned : Owned heap) (buffers : QuotientCInit.Buffers heap sb lb N.sqrt)
    {t : State} {value : Value}
    (run : Run QuotientSqrtExecute.service QuotientCSourceV2.countFunction.body
      (input N capacity sb lb heap) (.returned t value)) :
    value=.u64 (Nat.primeCounting N) ∧
      t.env=(input N capacity sb lb heap).env ∧ Owned t.heap := by
  obtain ⟨expected,correct,envExpected,ownedExpected⟩ :=
    function_refines N capacity sb lb heap hN2 hN hcap capacityWord owned buffers
  obtain ⟨sameState,sameValue⟩ := QuotientCDeterminism.returned_unique run correct
  exact ⟨sameValue,sameState ▸ envExpected,sameState ▸ ownedExpected⟩

#print axioms source_shape
#print axioms function_refines
#print axioms completed_execution_correct
end RamanujanPV.QuotientCFunction

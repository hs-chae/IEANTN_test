/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTEncodedSelectorExecution
import FFTEncodedSelectorDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots

theorem binary64_ge (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .ge (integer64 a) (integer64 b)=some (.boolean (decide (b≤a))):=by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt≥(Integer.cast .u64 (b:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

def result (length fallback : Nat) (tree : Tree) (j : Nat) : Nat:=
  if length≤j then fallback else tree.value j

theorem result_fits (length fallback : Nat) (tree : Tree) (j : Nat)
    (fallbackFits : fallback<2^64) (safe : tree.Safe) : result length fallback tree j<2^64:=by
  unfold result
  split
  · exact fallbackFits
  · exact Tree.value_safe safe j

/-- The complete selector body executes its actual unsigned range guard,
all chosen branches and literal return, preserving every caller object. -/
theorem body_execution {F : Type} (context : Context F) (length fallback : Nat) (tree : Tree)
    (before : State F) (id owner j : Nat) (lengthFits : length<2^64) (fallbackFits : fallback<2^64)
    (safe : tree.Safe) (well : WellScoped before)
    (lookup : before.environment.lookup "j"=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 (.integer (integer64 j))) (fits : j<2^64) :
    ∃after,ExecList context before (body length fallback tree)
      (.returned (.integer (integer64 (result length fallback tree j)))) after ∧ ReadOnly before after:=by
  have cond : Eval context before (.binary .ge (.variable "j") (.literal (.integer length "ULL")))
      (.integer (.boolean (decide (length≤j)))) before:=by
    exact .binaryLR (.variable lookup slot.read)
      (.literal (.integer length "ULL") _ (.integer (integer64 length)) (by simp [Literal.value,integer64];exact lengthFits))
      (by simp only [binary,binary64_ge j length fits lengthFits,Option.map_some])
  by_cases outside : length≤j
  · have inherited : Slot before.enterScope id owner .u64 (.integer (integer64 j)):=⟨slot.storable,slot.object⟩
    obtain ⟨middle,leaf,effect⟩:=execution context (.leaf fallback) before.enterScope id owner j fallbackFits
      (wellScoped_enter well) lookup inherited fits
    let after : State F:={middle.leaveScope before.nextScope before.environment with scope:=before.scope}
    have block : Exec context before (.block [.returnValue (some (.literal (.integer fallback "ULL")))])
        (.returned (.integer (integer64 fallback))) after:=.block rfl (.abrupt leaf (by simp)) rfl
    have rangeRun : Exec context before (guard length fallback) (.returned (.integer (integer64 fallback))) after:=
      .ifTrue cond (by simp only [outside,decide_true];rfl) block
    have all : ExecList context before [guard length fallback,tree.statement] (.returned (.integer (integer64 fallback))) after:=
      .abrupt rangeRun (by simp)
    refine ⟨after,?_,close_readonly well effect⟩
    simpa only [body,result,outside,↓reduceIte] using all
  · obtain ⟨after,selected,effect⟩:=execution context tree before id owner j safe well lookup slot fits
    have rangeRun : Exec context before (guard length fallback) .normal before:=
      .ifFalse cond (by simp only [outside,decide_false];rfl)
    have all : ExecList context before [guard length fallback,tree.statement]
        (.returned (.integer (integer64 (tree.value j)))) after:=.cons rangeRun (.abrupt selected (by simp))
    refine ⟨after,?_,effect⟩
    simpa only [body,result,outside,↓reduceIte] using all

#print axioms body_execution
end RH080Next.FFTPV.EncodedSelector

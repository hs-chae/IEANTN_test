/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderBranch
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def scaledExpression : Expr:=.paren (.binary .mul (.variable "value") (.literal (.integer 100 "ULL")))
def scaledDeclaration : Stmt:=.declare .u64 "scaled" (some scaledExpression)
def pointerExpression : Expr:=.paren (.binary .add (.variable "data") (.paren (.binary .mul (.variable "j") (.literal (.integer 12 "ULL")))))
def pointerDeclaration : Stmt:=.declare (.pointer .u64) "p" (some pointerExpression)

theorem source_preparation : ((ProductRow.items loopBody).drop 4).take 2 = [scaledDeclaration,pointerDeclaration]:=rfl

theorem BodyView.preparation_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 3 j cutoff ids (branchValues input j) memory) :
    ∃after finalIds,ExecList context before [scaledDeclaration,pointerDeclaration] .normal after ∧
      EveryList context before [scaledDeclaration,pointerDeclaration] .normal after ∧
      BodyView after input fo bo 5 j cutoff finalIds (branchValues input j) memory ∧
      ApplicationBirthFrame.Frame cutoff before after [] ∧
      ∀p,finalIds (.inl p)=ids (.inl p):=by
  let encoded:=input.profile.encoded j
  have bound:=input.profile.encoded_bound j h.active
  have abs64 : InputCell.magnitudeValue encoded<2^64:=lt_of_le_of_lt (InputCell.magnitude_value_bound encoded bound.le) (by norm_num [InputCell.scale])
  have scaled64 : InputCell.magnitudeValue encoded*100<2^64:=lt_of_le_of_lt (InputCell.scaled_value_bound encoded bound.le) (by norm_num [InputCell.base])
  have valueRead : Eval context before (.variable "value") (.integer (integer64 (InputCell.magnitudeValue encoded))) before:=by
    simpa [branchValues,temporaryName,encoded] using h.variable context .value (by norm_num [Active,localIndex])
  have scaledRead : Eval context before scaledExpression (.integer (integer64 (InputCell.magnitudeValue encoded*100))) before:=
    .paren (.binaryLR valueRead (.literal (.integer 100 "ULL") _ (.integer (integer64 100)) (by rfl))
      (by simp only [binary,binary64_mul _ _ abs64 (show 100<2^64 by norm_num) scaled64,Option.map_some]))
  obtain ⟨middle,run1,every1,h1,frame1⟩:=h.birth context (next:=.scaled) (expression:=scaledExpression) rfl
    (by simpa [branchValues,plannedValues,varType,encoded] using ZeroFrame.u64_storable (InputCell.magnitudeValue encoded*100) scaled64)
    (by simpa [branchValues,plannedValues,varType,encoded] using scaledRead) (by trivial)
  have shape:=input.profile.shape
  have j64 : j<2^64:=by have a:=h.active;omega
  have offset64 : j*12<2^64:=by have a:=h.active;omega
  have offsetBound : 0+j*12<12*input.profile.grid:=by have a:=h.active;omega
  have multiplyRead : Eval context middle (.paren (.binary .mul (.variable "j") (.literal (.integer 12 "ULL"))))
      (.integer (integer64 (j*12))) middle:=
    .paren (.binaryLR (h1.parameter_eval context .j) (.literal (.integer 12 "ULL") _ (.integer (integer64 12)) (by rfl))
      (by simp only [parameterValues,binary,binary64_mul _ _ j64 (show 12<2^64 by norm_num) offset64,Option.map_some]))
  have added:=slice_pointer_add (start:=0) (i:=j*12) h1.array offsetBound
  have pointerRead : Eval context middle pointerExpression (.pointer (wordPointer input.object (12*j))) middle:=by
    apply Eval.paren
    apply Eval.binaryLR (h1.parameter_eval context .data) multiplyRead
    simpa only [parameterValues,binary,added,Option.map_some,Nat.zero_add,Nat.mul_comm]
  obtain ⟨after,run2,every2,h2,frame2⟩:=h1.birth context (next:=.p) (expression:=pointerExpression) rfl
    (by simpa [branchValues,plannedValues,varType,encoded] using CompareSource.pointer_storable input.object (12*j))
    (by simpa [branchValues,plannedValues,varType,encoded] using pointerRead) (by trivial)
  exact ⟨after,_,.cons run1 (.cons run2 .nil),every_cons every1 (every_cons every2 (every_nil after)),h2,
    (lower_frame frame1 h.fresh).trans (lower_frame frame2 h1.fresh),by intro p;simp⟩

#print axioms source_preparation
#print axioms BodyView.preparation_execution
end RH080Next.FFTPV.InputLoader

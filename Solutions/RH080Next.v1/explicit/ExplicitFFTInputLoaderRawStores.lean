/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderWordStore
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def baseLiteral : Expr:=.literal (.integer InputCell.base "ULL")
def scaledMod : Expr:=.paren (.binary .mod (.variable "scaled") baseLiteral)
def scaledDiv : Expr:=.paren (.binary .div (.variable "scaled") baseLiteral)
def divideScaled : Stmt:=.assign (.variable "scaled") scaledDiv

def rawStatements : List Stmt:=[wordAssignment 2 scaledMod,divideScaled,wordAssignment 3 scaledMod,
  wordAssignment 4 scaledDiv,wordAssignment 5 (.variable "sign")]

def dividedValues (input : Input) (j : Nat) : Var → Value:=Function.update (branchValues input j) (.inr .scaled)
  (.integer (integer64 ((InputCell.magnitudeValue (input.profile.encoded j)*100)/InputCell.base)))

theorem source_raw_stores : ((ProductRow.items loopBody).drop 6).take 5=rawStatements:=rfl

theorem BodyView.mod_eval {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff x : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids values memory)
    (valueEq : values (.inr .scaled)=.integer (integer64 x)) (fits : x<2^64) :
    Eval context before scaledMod (.integer (integer64 (x%InputCell.base))) before:=by
  have read : Eval context before (.variable "scaled") (.integer (integer64 x)) before:=by
    simpa only [temporaryName,valueEq] using h.variable context .scaled (by norm_num [Active,localIndex])
  exact .paren (.binaryLR read (.literal (.integer InputCell.base "ULL") _ (.integer (integer64 InputCell.base)) (by rfl))
    (by simp only [binary,binary64_mod _ _ fits (show InputCell.base<2^64 by norm_num [InputCell.base]) (show 0< InputCell.base by norm_num [InputCell.base]),Option.map_some]))

theorem BodyView.div_eval {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff x : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids values memory)
    (valueEq : values (.inr .scaled)=.integer (integer64 x)) (fits : x<2^64) :
    Eval context before scaledDiv (.integer (integer64 (x/InputCell.base))) before:=by
  have read : Eval context before (.variable "scaled") (.integer (integer64 x)) before:=by
    simpa only [temporaryName,valueEq] using h.variable context .scaled (by norm_num [Active,localIndex])
  exact .paren (.binaryLR read (.literal (.integer InputCell.base "ULL") _ (.integer (integer64 InputCell.base)) (by rfl))
    (by simp only [binary,binary64_div _ _ fits (show InputCell.base<2^64 by norm_num [InputCell.base]) (show 0< InputCell.base by norm_num [InputCell.base]),Option.map_some]))

theorem BodyView.raw_stores_execution {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids (branchValues input j) memory) :
    ∃after,ExecList context before rawStatements .normal after ∧ EveryList context before rawStatements .normal after ∧
      BodyView after input fo bo 5 j cutoff ids (dividedValues input j) (rawStores memory (12*j) (input.profile.encoded j)) ∧
      ApplicationBirthFrame.Frame cutoff before after [input.object]:=by
  let encoded:=input.profile.encoded j
  let scaled:=InputCell.magnitudeValue encoded*100
  have scaled64 : scaled<2^64:=lt_of_le_of_lt (InputCell.scaled_value_bound encoded (input.profile.encoded_bound j h.active).le) (by norm_num [InputCell.base])
  have quotient64 : scaled/InputCell.base<2^64:=lt_of_le_of_lt (Nat.div_le_self _ _) scaled64
  have remainder64 (x : Nat) : x%InputCell.base<2^64:=lt_trans (Nat.mod_lt _ (by norm_num [InputCell.base])) (by norm_num [InputCell.base])
  have pointerEq : branchValues input j (.inr .p)=.pointer (wordPointer input.object (12*j)):=by simp [branchValues,plannedValues]
  have scaledEq : branchValues input j (.inr .scaled)=.integer (integer64 scaled):=by simp [branchValues,plannedValues,scaled,encoded]
  obtain ⟨s1,run1,every1,h1,f1⟩:=h.word_store context 2 (scaled%InputCell.base) (by omega) scaledMod (h.mod_eval context scaledEq scaled64) (by trivial) (remainder64 _) pointerEq
  obtain ⟨s2,run2,every2,h2,f2⟩:=h1.assign context .scaled (by norm_num [Active,localIndex]) (.integer (integer64 (scaled/InputCell.base))) scaledDiv
    (by simpa only [varType] using ZeroFrame.u64_storable (scaled/InputCell.base) quotient64) (h1.div_eval context scaledEq scaled64) (by trivial)
  have dividedEq : Function.update (branchValues input j) (.inr .scaled) (.integer (integer64 (scaled/InputCell.base)))=dividedValues input j:=rfl
  rw [dividedEq] at h2
  have pointerDivided : dividedValues input j (.inr .p)=.pointer (wordPointer input.object (12*j)):=by simp [dividedValues,branchValues,plannedValues]
  have quotientEq : dividedValues input j (.inr .scaled)=.integer (integer64 (scaled/InputCell.base)):=rfl
  obtain ⟨s3,run3,every3,h3,f3⟩:=h2.word_store context 3 ((scaled/InputCell.base)%InputCell.base) (by omega) scaledMod
    (h2.mod_eval context quotientEq quotient64) (by trivial) (remainder64 _) pointerDivided
  obtain ⟨s4,run4,every4,h4,f4⟩:=h3.word_store context 4 ((scaled/InputCell.base)/InputCell.base) (by omega) scaledDiv
    (h3.div_eval context quotientEq quotient64) (by trivial) (lt_of_le_of_lt (Nat.div_le_self _ _) quotient64) pointerDivided
  have signRead : Eval context s4 (.variable "sign") (.integer (integer64 (InputCell.signValue encoded))) s4:=by
    simpa [temporaryName,dividedValues,branchValues,encoded] using h4.variable context .sign (by norm_num [Active,localIndex])
  have sign64 : InputCell.signValue encoded<2^64:=by have b:=InputCell.sign_value_bound encoded;omega
  obtain ⟨after,run5,every5,h5,f5⟩:=h4.word_store context 5 (InputCell.signValue encoded) (by omega) (.variable "sign") signRead (by trivial) sign64 pointerDivided
  exact ⟨after,.cons run1 (.cons run2 (.cons run3 (.cons run4 (.cons run5 .nil)))),
    every_cons every1 (every_cons every2 (every_cons every3 (every_cons every4 (every_cons every5 (every_nil after))))),h5,
    (((f1.trans (frame_widen f2 (by intros;simp_all))).trans f3).trans f4).trans f5⟩

#print axioms source_raw_stores
#print axioms BodyView.raw_stores_execution
end RH080Next.FFTPV.InputLoader

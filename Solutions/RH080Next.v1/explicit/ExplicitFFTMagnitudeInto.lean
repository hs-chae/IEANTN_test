/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSimpleFrame
import ExplicitFFTZeroSliceFullFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MagnitudeIntoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

def base : Nat:=1000000000
structure Input where
  object : Nat
  size : Nat
  start : Nat
  old : Nat → Nat
  value : Nat
  bound : start+6≤size
  small : value<base^2

def finalData (input : Input) : Nat → Nat:=
  Function.update (Function.update (ZeroSlice.zeroData input.old input.start 6) input.start (input.value%base))
    (input.start+1) (input.value/base)

inductive Param where | out | value deriving DecidableEq

def name : Param → String | .out=>"out" | .value=>"value"
def ctype : Param → CType | .out=>.pointer .u64 | .value=>.u64
def value (input : Input) : Param → Value
  | .out=>.pointer (wordPointer input.object input.start)
  | .value=>.integer (integer64 input.value)
def paramIds (first : Nat) : Param → Nat | .out=>first | .value=>first+1

structure View {F : Type} (state : State F) (input : Input) (owner : Nat) (ids : Param → Nat) (data : Nat → Nat) : Prop where
  array : WordArrayRep state input.object input.size data
  locals : Locals state name ctype ids owner (value input)
  separate : ∀p,input.object≠ids p
  well : WellScoped state

theorem input_small64 (input : Input) : input.value<2^64:=lt_trans input.small (by norm_num [base])

theorem initialize_parameters {F : Type} {entry : State F} (input : Input)
    (well : WellScoped entry) (empty : entry.environment=[])
    (rep : WordArrayRep entry input.object input.size input.old) :
    ∃s1 s2,entry.declare (.pointer .u64) "out" (some (value input .out))=some s1 ∧
      s1.declare .u64 "value" (some (value input .value))=some s2 ∧
      View s2 input entry.scope (paramIds entry.nextObject) input.old:=by
  obtain ⟨s1,d1⟩:=ZeroFrame.declare_exists well _ "out" _ (CompareSource.pointer_storable input.object input.start)
  have w1:=wellScoped_declare well d1
  obtain ⟨s2,d2⟩:=ZeroFrame.declare_exists w1 _ "value" _ (ZeroFrame.u64_storable input.value (input_small64 input))
  have i1:=declare_storable (CompareSource.pointer_storable input.object input.start)
    (CompareSource.pointer_storable input.object input.start).converted d1
  have i2:=declare_storable (ZeroFrame.u64_storable input.value (input_small64 input)) (convert64 _ (input_small64 input)) d2
  have declarations : Declarations entry s2:=.cons d1 (.cons d2 (.nil s2))
  have live:=well.objectIds _ _ rep.2.1
  have words : WordArrayRep s2 input.object input.size input.old:=by
    refine ⟨declarations.fields.2.2.2.1.trans rep.1,?_,rep.2.2⟩
    rw [declarations.fields.2.2.2.2 _ live];exact rep.2.1
  have locals : Locals s2 name ctype (paramIds entry.nextObject) entry.scope (value input):=by
    constructor
    · intro p;cases p <;> simp [name,ctype,paramIds,i2.environment,i1.environment,empty,i1.nextObject,List.lookup]
    · intro p
      cases p with
      | out=>simpa only [ctype,paramIds,value] using ApplicationBirthFrame.slot_declare_old w1 i1.slot i2
      | value=>simpa only [ctype,paramIds,value,i1.nextObject,i1.scope] using i2.slot
    · intro a b eq;cases a <;> cases b <;> simp_all [paramIds] <;> omega
    · rw [i2.nextScope,i1.nextScope];exact well.current
  exact ⟨s1,s2,d1,d2,words,locals,(by intro p;cases p <;> simp only [paramIds] <;> omega),wellScoped_declare w1 d2⟩

theorem View.reframe {F : Type} {before after : State F} {input : Input} {owner : Nat} {ids : Param → Nat} {old data : Nat → Nat}
    (h : View before input owner ids old) (rep : WordArrayRep after input.object input.size data)
    (frame : IncrementSource.FullCallerFrame before after input.object) (scope : owner≤before.scope) :
    View after input owner ids data:=by
  refine ⟨rep,⟨?_,?_,h.locals.distinct,?_⟩,h.separate,frame.well⟩
  · rw [frame.environment];exact h.locals.lookup
  · intro p
    refine ⟨(h.locals.slots p).storable,?_⟩
    rw [frame.objects _ (h.well.objectIds _ _ (h.locals.slots p).object) (h.separate p).symm]
    exact (h.locals.slots p).object
  · exact lt_of_le_of_lt (scope.trans_eq frame.scope.symm) frame.well.current

def zeroStatement : Stmt:=.expression (.call "zero_words" [.variable "out",.literal (.integer 6 "ULL")])
def storeStatement (offset : Nat) (op : Binary) : Stmt:=
  .assign (.index (.variable "out") (.literal (.integer offset "ULL")))
    (.paren (.binary op (.variable "value") (.literal (.integer base "ULL"))))
def statements : List Stmt:=[zeroStatement,storeStatement 0 .mod,storeStatement 1 .div,.returnValue (some (.literal (.integer 0 "ULL")))]

theorem actual_body : magnitude_into_ast.body=.block statements:=rfl

theorem zero_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : View before input owner ids data) (scope : owner≤before.scope) :
    ∃after,Exec context before zeroStatement .normal after ∧ Every context before zeroStatement .normal after ∧
      View after input owner ids (ZeroSlice.zeroData data input.start 6) ∧ IncrementSource.FullCallerFrame before after input.object:=by
  obtain ⟨after,called,post,frame⟩:=ZeroSlice.zero_words_call_framed context selected before input.object input.size input.start 6 data h.well h.array input.bound (by norm_num)
  have args : Args context before [.variable "out",.literal (.integer 6 "ULL")]
      [.pointer (wordPointer input.object input.start),.integer (integer64 6)] before:=by
    apply Args.ordered (order:=[(0,.variable "out"),(1,.literal (.integer 6 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.object input.start)),(1,.integer (integer64 6))])
    · exact List.Perm.refl _
    · exact .cons (.variable (h.locals.lookup Param.out) (h.locals.read Param.out)) (.cons (.literal _ _ _ (by rfl)) .nil)
    · change List.Forall₂ _ [0,1] _;exact .cons rfl (.cons rfl .nil)
  have full : IncrementSource.FullCallerFrame before after input.object:=
    ⟨⟨frame.environment,frame.scope,frame.foreign,frame.well,frame.objects⟩,frame.nextObject,frame.nextScope,frame.mode⟩
  exact ⟨after,.expression (.call args called),every_expression_call (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl <;> trivial) args
    (fun state result actual=>ZeroCallUnique.returned_call_unique selected called actual),h.reframe post full scope,full⟩

theorem store_execution {F : Type} (context : Context F)
    {before : State F} {input : Input} {owner : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : View before input owner ids data) (offset result : Nat) (offsetBound : offset<6) (offset64 : offset<2^64)
    (op : Binary) (result64 : result<2^64)
    (computed : Integer.binary op (integer64 input.value) (integer64 base)=some (integer64 result)) :
    ∃after,Exec context before (storeStatement offset op) .normal after ∧ Every context before (storeStatement offset op) .normal after ∧
      View after input owner ids (Function.update data (input.start+offset) result) ∧ IncrementSource.FullCallerFrame before after input.object:=by
  have bound : input.start+offset< input.size:=by have hb:=input.bound;omega
  obtain ⟨after,stored,rep⟩:=word_store_with_rep h.array bound result64
  have rhs : Eval context before (.paren (.binary op (.variable "value") (.literal (.integer base "ULL")))) (.integer (integer64 result)) before:=by
    apply Eval.paren
    exact .binaryLR (.variable (h.locals.lookup Param.value) (h.locals.read Param.value)) (.literal (.integer base "ULL") _ (.integer (integer64 base)) (by rfl)) (by simp only [value,binary,computed,Option.map_some])
  have place : Place context before (.index (.variable "out") (.literal (.integer offset "ULL")))
      (wordPointer input.object (input.start+offset)) before:=.index (.variable (h.locals.lookup Param.out) (h.locals.read Param.out))
        (.literal _ _ _ (by have ho : offset<18446744073709551616:=offset64;simp [Literal.value,integer64,ho])) (slice_pointer_add h.array bound)
  have run : Exec context before (storeStatement offset op) .normal after:=.assign rhs place stored
  have frame:=assignment_full_frame h.well (by trivial) (by trivial) rhs place rfl run
  have locals:=ApplicationBirthFrame.locals_store_other h.locals (fun p=>(h.separate p).symm) stored
  exact ⟨after,run,every_pure (by simp [storeStatement,PureDeterminism.Simple,SourcePure.CallFree]) run,⟨rep,locals,h.separate,frame.well⟩,frame⟩

#print axioms initialize_parameters
#print axioms zero_execution
#print axioms store_execution
end RH080Next.FFTPV.MagnitudeIntoSource

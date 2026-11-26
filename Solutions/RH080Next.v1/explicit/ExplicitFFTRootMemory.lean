/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSquare
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)

/-- Only the two actual pointer parameters are address bases. -/
def PointerParam (p : Param) : Prop:=p=.root ∨ p=.work

def pointerStart (input : Input) : Param → Nat
  | .root=>input.layout.rootStart
  | _=>input.layout.workStart

def pointerExpr (p : Param) (k : Nat) : Expr:=
  if k=0 then .variable (paramName p) else offsetExpr (paramName p) k

theorem pointer_expr_pure (p : Param) (k : Nat) : SourcePure.CallFree (pointerExpr p k) := by
  unfold pointerExpr
  split_ifs <;> simp [offsetExpr,SourcePure.CallFree]

theorem pointer_eval {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ParamView before input owner ids data) (p : Param) (hp : PointerParam p)
    (k : Nat) (bound : pointerStart input p+k< input.layout.size) (fits : k<2^64) :
    Eval context before (pointerExpr p k)
      (.pointer (wordPointer input.layout.object (pointerStart input p+k))) before := by
  have variableEval : Eval context before (.variable (paramName p))
      (.pointer (wordPointer input.layout.object (pointerStart input p))) before:=by
    rcases hp with rfl|rfl <;> exact .variable (h.locals.lookup _) (h.locals.read _)
  by_cases zero : k=0
  · subst k;simpa [pointerExpr] using variableEval
  · rw [pointerExpr,if_neg zero]
    apply Eval.paren
    apply Eval.binaryLR variableEval
      (.literal (.integer k "ULL") _ (.integer (integer64 k)) ?_)
    · simp only [binary,slice_pointer_add h.array bound,Option.map_some]
    · have hk : k<18446744073709551616:=fits;simp [Literal.value,integer64,hk]

/-- Preserve true function locals and the true status slot across an actual
callee's independently proved application frame. -/
theorem ScaleView.reframe {F : Type} {before after : State F} {input : Input} {owner statusId : Nat}
    {ids : Param → Nat} {old data : Nat → Nat} (h : ScaleView before input owner statusId ids old)
    (rep : WordArrayRep after input.layout.object input.layout.size data)
    (environment : after.environment=before.environment) (scope : owner≤ before.scope)
    (restore : after.scope=before.scope) (well : WellScoped after)
    (objects : ∀id,id < before.nextObject → id≠input.layout.object → after.objects id=before.objects id) :
    ScaleView after input owner statusId ids data := by
  have locals : Locals after paramName paramType ids owner (paramValue input):=by
    refine ⟨?_,?_,h.params.locals.distinct,?_⟩
    · rw [environment];exact h.params.locals.lookup
    · intro v
      refine ⟨(h.params.locals.slots v).storable,?_⟩
      rw [objects _ (h.params.well.objectIds _ _ (h.params.locals.slots v).object) (h.params.separate v).symm]
      exact (h.params.locals.slots v).object
    · exact lt_of_le_of_lt (scope.trans_eq restore.symm) well.current
  refine ⟨⟨rep,locals,h.params.separate,well⟩,⟨h.status.storable,?_⟩,?_,h.statusSeparate⟩
  · rw [objects _ (h.params.well.objectIds _ _ h.status.object) h.statusSeparate.symm];exact h.status.object
  · rw [environment];exact h.statusLookup

def literalStore (p : Param) (offset value : Nat) : Stmt:=
  .assign (.index (.variable (paramName p)) (.literal (.integer offset "ULL"))) (.literal (.integer value "ULL"))

theorem literal_store_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (p : Param) (hp : PointerParam p)
    (offset value : Nat) (bound : pointerStart input p+offset< input.layout.size) (offset64 : offset<2^64) (value64 : value<2^64) :
    ∃after,Exec context before (literalStore p offset value) .normal after ∧
      ScaleView after input owner statusId ids (Function.update data (pointerStart input p+offset) value) ∧
      after.scope=before.scope := by
  obtain ⟨after,stored,rep⟩:=word_store_with_rep h.params.array bound value64
  have variableEval : Eval context before (.variable (paramName p))
      (.pointer (wordPointer input.layout.object (pointerStart input p))) before:=by
    rcases hp with rfl|rfl <;> exact .variable (h.params.locals.lookup _) (h.params.locals.read _)
  have run : Exec context before (literalStore p offset value) .normal after:=.assign
    (.literal (.integer value "ULL") _ (.integer (integer64 value))
      (by have hval : value<18446744073709551616:=value64;simp [Literal.value,integer64,hval]))
    (.index variableEval (.literal (.integer offset "ULL") _ (.integer (integer64 offset))
      (by have hoff : offset<18446744073709551616:=offset64;simp [Literal.value,integer64,hoff]))
      (slice_pointer_add h.params.array bound)) stored
  have lm:=ApplicationBirthFrame.locals_store_other h.params.locals (fun v=>(h.params.separate v).symm) stored
  have status:=ApplicationBirthFrame.slot_store_other h.status h.statusSeparate.symm stored
  have fields:=SourceLocals.store_frame stored
  have well:=wellScoped_store h.params.well stored
  exact ⟨after,run,⟨⟨rep,lm,h.params.separate,well⟩,status,by rw [fields.1];exact h.statusLookup,h.statusSeparate⟩,fields.2.2.1⟩

def zeroSliceStatement (p : Param) (offset length : Nat) : Stmt:=.expression
  (.call "zero_words" [pointerExpr p offset,.literal (.integer length "ULL")])

theorem zero_slice_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset length : Nat)
    (offsetBound : pointerStart input p+offset< input.layout.size)
    (bound : pointerStart input p+offset+length≤ input.layout.size) (offset64 : offset<2^64) (length64 : length<2^64) :
    ∃after,Exec context before (zeroSliceStatement p offset length) .normal after ∧
      ScaleView after input owner statusId ids (ZeroSlice.zeroData data (pointerStart input p+offset) length) ∧ after.scope=before.scope := by
  obtain ⟨after,called,post,frame⟩:=ZeroSlice.zero_words_call context selected before input.layout.object input.layout.size
    (pointerStart input p+offset) length data h.params.well h.params.array bound length64
  have args : Args context before [pointerExpr p offset,.literal (.integer length "ULL")]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),.integer (integer64 length)] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,.literal (.integer length "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),(1,.integer (integer64 length))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.params p hp offset offsetBound offset64)
        (.cons (.literal (.integer length "ULL") _ (.integer (integer64 length))
          (by have hl : length<18446744073709551616:=length64;simp [Literal.value,integer64,hl])) .nil)
    · change List.Forall₂ _ [0,1] _;exact .cons rfl (.cons rfl .nil)
  exact ⟨after,.expression (.call args called),h.reframe post frame.environment scope frame.scope frame.well frame.objects,frame.scope⟩

def copySliceStatement (p : Param) (offset : Nat) (q : Param) (inputOffset : Nat) : Stmt:=.expression
  (.call "copy_words" [pointerExpr p offset,pointerExpr q inputOffset,.literal (.integer 6 "ULL")])

theorem copy_slice_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "copy_words"=some copy_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset : Nat) (q : Param) (hq : PointerParam q) (inputOffset : Nat)
    (bound : pointerStart input p+offset+6≤ input.layout.size) (inputBound : pointerStart input q+inputOffset+6≤ input.layout.size)
    (ranges : pointerStart input p+offset=pointerStart input q+inputOffset ∨
      pointerStart input p+offset+6≤ pointerStart input q+inputOffset ∨
      pointerStart input q+inputOffset+6≤ pointerStart input p+offset)
    (offset64 : offset<2^64) (inputOffset64 : inputOffset<2^64) :
    ∃after,Exec context before (copySliceStatement p offset q inputOffset) .normal after ∧
      ScaleView after input owner statusId ids (CopyLoop.prefixData data
        (fun i=>data (pointerStart input q+inputOffset+i)) (pointerStart input p+offset) 6) ∧ after.scope=before.scope := by
  obtain ⟨after,called,post,readSource,frame⟩:=CopyLoop.copy_words_call context selected before
    input.layout.object input.layout.size (pointerStart input p+offset)
    input.layout.object input.layout.size (pointerStart input q+inputOffset) 6 data data
    h.params.well h.params.array h.params.array (fun _=>rfl) (Or.inr ranges) bound inputBound (by norm_num)
  have args : Args context before [pointerExpr p offset,pointerExpr q inputOffset,.literal (.integer 6 "ULL")]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),
       .pointer (wordPointer input.layout.object (pointerStart input q+inputOffset)),.integer (integer64 6)] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,pointerExpr q inputOffset),(2,.literal (.integer 6 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),
        (1,.pointer (wordPointer input.layout.object (pointerStart input q+inputOffset))),(2,.integer (integer64 6))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.params p hp offset (by omega) offset64)
        (.cons (pointer_eval context h.params q hq inputOffset (by omega) inputOffset64)
          (.cons (.literal (.integer 6 "ULL") _ (.integer (integer64 6)) (by rfl)) .nil))
    · change List.Forall₂ _ [0,1,2] _;exact .cons rfl (.cons rfl (.cons rfl .nil))
  exact ⟨after,.expression (.call args called),h.reframe post frame.environment scope frame.scope frame.well frame.objects,frame.scope⟩

#print axioms pointer_eval
#print axioms literal_store_execution
#print axioms zero_slice_execution
#print axioms copy_slice_execution
end RH080Next.FFTPV.RootSource

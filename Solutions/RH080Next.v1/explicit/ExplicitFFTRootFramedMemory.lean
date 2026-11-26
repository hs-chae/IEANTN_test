/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootSimpleFrame
import ExplicitFFTZeroSliceFullFrame
import FFTCopyDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem zero_slice_framed {F : Type} (context : Context F)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset length : Nat)
    (offsetBound : pointerStart input p+offset< input.layout.size)
    (bound : pointerStart input p+offset+length≤ input.layout.size) (offset64 : offset<2^64) (length64 : length<2^64) :
    ∃after,Exec context before (zeroSliceStatement p offset length) .normal after ∧
      Every context before (zeroSliceStatement p offset length) .normal after ∧
      ScaleView after input owner statusId ids (ZeroSlice.zeroData data (pointerStart input p+offset) length) ∧ IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,called,post,frame⟩:=ZeroSlice.zero_words_call_framed context selected before input.layout.object input.layout.size
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
  have everyStep:=every_expression_call (args:=args)
    (callee:=fun state output actual=>ZeroCallUnique.returned_call_unique selected called actual)
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl
        · exact pointer_expr_pure _ _
        · trivial)
  exact ⟨after,.expression (.call args called),everyStep,h.reframe post frame.environment scope frame.scope frame.well frame.objects,⟨⟨frame.environment,frame.scope,frame.foreign,frame.well,frame.objects⟩,frame.nextObject,frame.nextScope,frame.mode⟩⟩

theorem copy_slice_framed {F : Type} (context : Context F)
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
      Every context before (copySliceStatement p offset q inputOffset) .normal after ∧
      ScaleView after input owner statusId ids (CopyLoop.prefixData data
        (fun i=>data (pointerStart input q+inputOffset+i)) (pointerStart input p+offset) 6) ∧ IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,called,post,readSource,frame,birth⟩:=CopyLoop.copy_words_call_framed context selected before
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
  have everyStep:=every_expression_call (args:=args)
    (callee:=fun state output actual=>CopyLoop.call_unique selected called actual)
    (by intro e member;simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl
        · exact pointer_expr_pure _ _
        · exact pointer_expr_pure _ _
        · trivial)
  exact ⟨after,.expression (.call args called),everyStep,h.reframe post frame.environment scope frame.scope frame.well frame.objects,full_caller_frame frame.environment frame.scope birth⟩

#print axioms zero_slice_framed
#print axioms copy_slice_framed
end RH080Next.FFTPV.RootSource

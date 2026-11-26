/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexParameters
import FFTWordSlices
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

structure Layout where
  object : PVar→Nat
  start : PVar→Nat
  length : Nat→Nat
  bound : ∀r,start r+(if r=.work then 46 else 12)≤length (object r)

def pointerExpr (r : PVar) (offset : Nat) : Expr:=
  if offset=0 then .variable (pName r)
  else .paren (.binary .add (.variable (pName r)) (.literal (.integer offset "ULL")))

def aOffset (i : Fin 4) : Nat:=if i.val%2=1 then 6 else 0
def bOffset (i : Fin 4) : Nat:=if i.val=1 ∨ i.val=2 then 6 else 0

def multiplyArguments (i : Fin 4) : List Expr:=
  [pointerExpr .work (6*i.val),pointerExpr .a (aOffset i),pointerExpr .b (bOffset i),pointerExpr .work 36]

def addArguments (i : Fin 2) : List Expr:=
  if i.val=0 then [pointerExpr .output 0,pointerExpr .work 0,pointerExpr .work 6,.literal (.integer 1 "ULL")]
  else [pointerExpr .output 6,pointerExpr .work 12,pointerExpr .work 18,.literal (.integer 0 "ULL")]

def functionStatements : List Stmt:=
  [statusDeclaration,StatusCall.statement "fixed_multiply" (multiplyArguments 0),
    StatusCall.statement "fixed_multiply" (multiplyArguments 1),
    StatusCall.statement "fixed_multiply" (multiplyArguments 2),
    StatusCall.statement "fixed_multiply" (multiplyArguments 3),
    StatusCall.statement "fixed_add" (addArguments 0),
    StatusCall.statement "fixed_add" (addArguments 1),.returnValue (some (.variable "status"))]

theorem actual_body : complex_multiply_ast.body=.block functionStatements:=by rfl

theorem pointer_offset_eval {F : Type} (context : Context F) {before : State F}
    {layout : Layout} {data : Nat→Nat→Nat} {ids : PVar→Nat} {owner : Nat}
    (params : Locals before pName pType ids owner (pValue (layout.object .output) (layout.start .output)
      (layout.object .a) (layout.start .a) (layout.object .b) (layout.start .b) (layout.object .work) (layout.start .work)))
    (rep : ∀r,WordArrayRep before (layout.object r) (layout.length (layout.object r)) (data (layout.object r)))
    (r : PVar) (offset : Nat) (small : offset≤36) (bound : layout.start r+offset<layout.length (layout.object r)) :
    Eval context before (pointerExpr r offset) (.pointer (wordPointer (layout.object r) (layout.start r+offset))) before:=by
  have sourceVar : Eval context before (.variable (pName r))
      (.pointer (wordPointer (layout.object r) (layout.start r))) before:=by
    have ev:=Eval.variable (context:=context) (params.lookup r) (params.read r)
    cases r <;> exact ev
  by_cases zero : offset=0
  · subst offset
    simpa [pointerExpr] using sourceVar
  · have fits : offset<2^64:=by omega
    have added:=slice_pointer_add (rep r) bound
    simpa only [pointerExpr,zero,↓reduceIte] using
      Eval.paren (Eval.binaryLR sourceVar
        (Eval.literal (.integer offset "ULL") before (.integer (integer64 offset)) (by simp [Literal.value,integer64];omega))
        (by simpa only [binary,Option.map_some] using congrArg (Option.map Value.pointer) added))

theorem four_arguments {F : Type} {context : Context F} {before : State F}
    {a b c d : Expr} {va vb vc vd : Value}
    (ha : Eval context before a va before) (hb : Eval context before b vb before)
    (hc : Eval context before c vc before) (hd : Eval context before d vd before) :
    Args context before [a,b,c,d] [va,vb,vc,vd] before:=by
  refine .ordered (List.Perm.refl _) (.cons ha (.cons hb (.cons hc (.cons hd .nil)))) ?_
  exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))

def multiplyValues (layout : Layout) (i : Fin 4) : List Value:=
  [.pointer (wordPointer (layout.object .work) (layout.start .work+6*i.val)),
    .pointer (wordPointer (layout.object .a) (layout.start .a+aOffset i)),
    .pointer (wordPointer (layout.object .b) (layout.start .b+bOffset i)),
    .pointer (wordPointer (layout.object .work) (layout.start .work+36))]

theorem multiply_arguments_eval {F : Type} (context : Context F) {before : State F}
    {layout : Layout} {data : Nat→Nat→Nat} {ids : PVar→Nat} {owner : Nat}
    (params : Locals before pName pType ids owner (pValue (layout.object .output) (layout.start .output)
      (layout.object .a) (layout.start .a) (layout.object .b) (layout.start .b) (layout.object .work) (layout.start .work)))
    (rep : ∀r,WordArrayRep before (layout.object r) (layout.length (layout.object r)) (data (layout.object r)))
    (i : Fin 4) : Args context before (multiplyArguments i) (multiplyValues layout i) before:=by
  have workBound:=layout.bound MultiplyParameters.Var.work
  have aBound:=layout.bound MultiplyParameters.Var.a
  have bBound:=layout.bound MultiplyParameters.Var.b
  simp only [ite_true,if_neg (by decide : MultiplyParameters.Var.a≠MultiplyParameters.Var.work),if_neg (by decide : MultiplyParameters.Var.b≠MultiplyParameters.Var.work)] at workBound aBound bBound
  have ia:=i.isLt
  have ao : aOffset i≤6:=by unfold aOffset;split <;> omega
  have bo : bOffset i≤6:=by unfold bOffset;split <;> omega
  apply four_arguments
  · exact pointer_offset_eval context params rep .work _ (by omega) (by omega)
  · exact pointer_offset_eval context params rep .a _ (by omega) (by omega)
  · exact pointer_offset_eval context params rep .b _ (by omega) (by omega)
  · exact pointer_offset_eval context params rep .work _ (by omega) (by omega)

theorem pointer_expression_closed (r : PVar) (offset : Nat) : SourcePure.CallFree (pointerExpr r offset):=by
  unfold pointerExpr
  split <;> trivial

theorem multiply_arguments_closed (i : Fin 4) : ∀e∈multiplyArguments i,SourcePure.CallFree e:=by
  intro e member
  simp only [multiplyArguments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> exact pointer_expression_closed _ _

#print axioms actual_body
#print axioms pointer_offset_eval
#print axioms four_arguments
#print axioms multiply_arguments_eval
end RH080Next.FFTPV.ComplexSource

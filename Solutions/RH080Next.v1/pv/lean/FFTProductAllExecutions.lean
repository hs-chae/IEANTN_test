/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductCoreMath
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open ApplicationBirthFrame

theorem inner_body_unique {F : Type} (context : Context F) : CompareSource.Unique context ProductInner.innerBody := by
  intro before a b fa fb first second
  exact PureDeterminism.block_unique
    (by simp [ProductInner.innerBody,ProductRow.actual_inner_shape,ProductRow.kExpr,ProductRow.tExpr,
      ProductRow.digitStmt,ProductRow.digitExpr,ProductRow.carryExpr,ProductRow.arrayAt,ZeroLoop.increment,
      PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem inner_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context ProductInner.innerLoop :=
  CompareSource.while_unique (by simp [ProductInner.innerCondition,SourcePure.CallFree]) (inner_body_unique context)

theorem outer_body_unique {F : Type} (context : Context F) : CompareSource.Unique context outerBody := by
  apply CompareSource.block_unique
  intro stmt member
  simp only [rowDeclarations,List.cons_append,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact fun first second=>PureDeterminism.simple_unique
      (by simp [PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second=>PureDeterminism.simple_unique
      (by simp [PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact inner_loop_unique context
  · exact fun first second=>PureDeterminism.simple_unique
      (by simp [carryStore,carryIndex,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second=>PureDeterminism.simple_unique
      (by simp [incrementI,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem outer_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context outerLoop :=
  CompareSource.while_unique (by simp [outerCondition,SourcePure.CallFree]) (outer_body_unique context)

/-- Every permitted evaluation order and every actual operational execution
of the complete source multiplication core has the mathematically correct
product. Constructive termination is supplied separately by source_product_core. -/
theorem every_source_product_core {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (initialized : ∀k,k<10 → data (workStart+k)=0)
    (run : Exec context before outerLoop flow after) :
    flow=.normal ∧ ∃finalData,
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b finalData 5 ∧
      Frame before.nextObject before after [workObj,ids PVar.i] ∧
      RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
        RH080Next.FFT.Limbs.value 1000000000 5 a*RH080Next.FFT.Limbs.value 1000000000 5 b := by
  obtain ⟨canonical,finalData,canonicalRun,ha,frame,product⟩:=source_product_core context h initialized
  obtain ⟨flowEq,stateEq⟩:=outer_loop_unique context run canonicalRun
  cases stateEq
  exact ⟨flowEq,finalData,ha,frame,product⟩

#print axioms inner_body_unique
#print axioms outer_body_unique
#print axioms outer_loop_unique
#print axioms every_source_product_core
end RH080Next.FFTPV.ProductOuter

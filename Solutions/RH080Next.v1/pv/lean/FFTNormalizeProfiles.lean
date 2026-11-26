/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTNormalizeDivision
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.NormalizeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def literal (d : Nat) : Expr:=.literal (.integer d "ULL")
def nDivisor : Expr:=.variable "n"

theorem actual_w4_total_divisions : ((ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body).drop 32).take 2=
    [divideStmt false (literal 100),divideStmt false nDivisor]:=by rfl

theorem actual_fap_total_division : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[32]?=
    some (divideStmt false nDivisor):=by rfl

theorem actual_w4_quad_divisions : ((ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body).drop 36).take 3=
    [divideStmt true (literal 3),divideStmt true nDivisor,divideStmt true nDivisor]:=by rfl

theorem actual_fap_quad_divisions : ((ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body).drop 36).take 3=
    [divideStmt true (literal 3),divideStmt true nDivisor,divideStmt true nDivisor]:=by rfl

theorem literal_eval {F : Type} (context : Context F) (state : State F) (d : Nat) (fits : d<2^64) :
    Eval context state (literal d) (.integer (integer64 d)) state:=
  .literal _ _ _ (by simp [literal,Literal.value,integer64];omega)

theorem n_eval {F : Type} (context : Context F) {state : State F} {workObject n owner : Nat} {ids : Var→Nat}
    (params : Locals state name type ids owner (values workObject n)) :
    Eval context state nDivisor (.integer (integer64 n)) state:=.variable (params.lookup Var.n) (params.read Var.n)

theorem source_division_execution {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (quad : Bool) (divisor : Expr) (d : Nat) (positive : 0<d) (small : d<1000000000)
    (pure : SourcePure.CallFree divisor) (evaluated : Eval context before divisor (.integer (integer64 d)) before)
    (digits : ∀k,k<6 → old (start quad+k)<1000000000) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      (∃after,Exec context before (divideStmt quad divisor) .normal after ∧
        WordArrayRep after workObject 512 (DivideSource.roundedData old (start quad) 6 d 1) ∧
        Locals after name type ids owner (values workObject n) ∧
        MultiplyCall.CallerFrame before after [workObject] ∧
        FFT.Limbs.magnitude 1000000000 6 (fun k=>DivideSource.roundedData old (start quad) 6 d 1 (start quad+k))=
          FFT.Limbs.ceilQuotient (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (start quad+k))) d ∧
        (∀k,k<6 → DivideSource.roundedData old (start quad) 6 d 1 (start quad+k)<1000000000) ∧
        (∀k,(k<start quad ∨ start quad+6≤k) → DivideSource.roundedData old (start quad) 6 d 1 k=old k) ∧
        (∀other flow,Exec context before (divideStmt quad divisor) flow other → flow=.normal ∧ other=after)) := by
  have selected : findFunction context.program "divide_small"=some divide_small_ast:=by rcases programPinned with h|h <;> rw [h] <;> rfl
  have increment : findFunction context.program "increment_words"=some increment_words_ast:=by rcases programPinned with h|h <;> rw [h] <;> rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    division_execution context selected increment params array separate well quad divisor d positive small pure evaluated digits⟩

#print axioms actual_w4_total_divisions
#print axioms actual_fap_total_division
#print axioms actual_w4_quad_divisions
#print axioms actual_fap_quad_divisions
#print axioms source_division_execution
end RH080Next.FFTPV.NormalizeSource

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.NormalizeSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

inductive Var where | n | total | quad | status deriving DecidableEq

def name : Var→String | .n=>"n" | .total=>"total" | .quad=>"quad" | .status=>"status"
def type : Var→CType | .total | .quad=>.pointer .u64 | _=>.u64

def values (workObject n : Nat) : Var→Value
  | .n=>.integer (integer64 n)
  | .total=>.pointer (wordPointer workObject 192)
  | .quad=>.pointer (wordPointer workObject 208)
  | .status=>.integer (integer64 0)

def field (quad : Bool) : Var:=if quad then .quad else .total
def start (quad : Bool) : Nat:=if quad then 208 else 192

def arguments (quad : Bool) (divisor : Expr) : List Expr:=
  [.variable (name (field quad)),.literal (.integer 6 "ULL"),divisor,.literal (.integer 1 "ULL")]
def divideStmt (quad : Bool) (divisor : Expr) : Stmt:=StatusCall.statement "divide_small" (arguments quad divisor)

/-- Actual source upward-division status assignment. Both C evaluation orders,
all argument orders, real callee births, exact unsigned quotient and full
physical workspace frame are consumed from the verified divide_small source. -/
theorem division_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (increment : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {workObject n owner : Nat} {ids : Var→Nat} {old : Nat→Nat}
    (params : Locals before name type ids owner (values workObject n))
    (array : WordArrayRep before workObject 512 old) (separate : ∀v,workObject≠ids v) (well : WellScoped before)
    (quad : Bool) (divisor : Expr) (d : Nat) (positive : 0<d) (small : d<1000000000)
    (pure : SourcePure.CallFree divisor) (evaluated : Eval context before divisor (.integer (integer64 d)) before)
    (digits : ∀k,k<6 → old (start quad+k)<1000000000) :
    ∃after,Exec context before (divideStmt quad divisor) .normal after ∧
      WordArrayRep after workObject 512 (DivideSource.roundedData old (start quad) 6 d 1) ∧
      Locals after name type ids owner (values workObject n) ∧
      MultiplyCall.CallerFrame before after [workObject] ∧
      FFT.Limbs.magnitude 1000000000 6 (fun k=>DivideSource.roundedData old (start quad) 6 d 1 (start quad+k))=
        FFT.Limbs.ceilQuotient (FFT.Limbs.magnitude 1000000000 6 (fun k=>old (start quad+k))) d ∧
      (∀k,k<6 → DivideSource.roundedData old (start quad) 6 d 1 (start quad+k)<1000000000) ∧
      (∀k,(k<start quad ∨ start quad+6≤k) → DivideSource.roundedData old (start quad) 6 d 1 k=old k) ∧
      (∀other flow,Exec context before (divideStmt quad divisor) flow other → flow=.normal ∧ other=after) := by
  have bound : start quad+6≤512:=by cases quad <;> norm_num [start]
  obtain ⟨⟨after,called,rep,fullFrame,every⟩,value,normalized,outside⟩:=
    DivideSource.divide_small_total context selected increment before workObject 512 (start quad) 6 d 1 old well array bound
      (by norm_num) digits positive small (by norm_num)
  have frame:=ComplexSource.add_caller_frame fullFrame
  have postParams : Locals after name type ids owner (values workObject n):=by
    refine ⟨?_,?_,params.distinct,params.bound.trans_le frame.frame.nextScope⟩
    · intro v;rw [frame.environment];exact params.lookup v
    · intro v;exact ComplexSource.slot_after_call well (params.slots v) frame (by simpa using (separate v).symm)
  have pointer : Eval context before (.variable (name (field quad))) (.pointer (wordPointer workObject (start quad))) before:=by
    cases quad <;> exact .variable (params.lookup _) (params.read _)
  have args : Args context before (arguments quad divisor)
      [.pointer (wordPointer workObject (start quad)),.integer (integer64 6),.integer (integer64 d),.integer (integer64 1)] before:=
    ComplexSource.four_arguments pointer (.literal (.integer 6 "ULL") _ _ (by rfl)) evaluated (.literal (.integer 1 "ULL") _ _ (by rfl))
  have statusSlot : Slot before (ids Var.status) owner .u64 (.integer (integer64 0)):=params.slots Var.status
  have newStatus : Slot after (ids Var.status) owner .u64 (.integer (integer64 0)):=postParams.slots Var.status
  have run : Exec context before (divideStmt quad divisor) .normal after:=
    StatusCall.assignment_execution (params.lookup Var.status) (postParams.lookup Var.status) statusSlot newStatus args called
  refine ⟨after,run,rep,postParams,frame,by simpa only [IncrementSource.base,if_pos (show (0:Nat)<1 by decide)] using value,normalized,?_,?_⟩
  · intro k away
    exact outside k (by omega)
  · intro other flow arbitrary
    apply StatusCall.assignment_every_execution (params.lookup Var.status) (postParams.lookup Var.status) statusSlot newStatus
      (by intro e member;simp only [arguments,List.mem_cons,List.mem_nil_iff,or_false] at member;rcases member with rfl|rfl|rfl|rfl <;> first | exact pure | trivial)
      args every arbitrary

#print axioms division_execution
end RH080Next.FFTPV.NormalizeSource

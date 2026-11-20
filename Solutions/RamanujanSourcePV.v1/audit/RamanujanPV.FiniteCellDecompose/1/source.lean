import RamanujanPV.FiniteCellExecution
namespace RamanujanPV.FiniteCellDecompose
open FiniteScalarMachine LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

theorem sequence_returned {p : Prototypes} {c : Service} {body : List Stmt}
    {s t : State} {answer : Value}
    (run:Run p c (.sequence body) s (.returned t answer)) :
    ∃inner,SeqRun p c body s (.returned inner answer) := by
  cases run with
  | @sequence _ _ inner _ steps scope=>
    change .returned t answer=closeFlow s inner at scope
    cases inner with
    | continuing state=>contradiction
    | returned state result=>
      have eq:=LCMSourcePV.ASTLoops.Flow.returned.inj scope
      subst result
      exact ⟨state,steps⟩

theorem zero_eval (p : Prototypes) (c : Service) (s : State) : Eval p c (.nat 0) s s (i32 0) := rfl

theorem zero_return_value {p : Prototypes} {c : Service} {s t : State} {v : Value}
    (run:Run p c (.returnStmt (.nat 0)) s (.returned t v)) : v=i32 0 := by
  cases run with
  | returnValue evaluated=>
    have equal : (t,v)=(s,i32 0) := Option.some.inj (evaluated.symm.trans (zero_eval p c s))
    exact equal.2

theorem skip_no_return {p : Prototypes} {c : Service} {s t : State} {v : Value}
    (run:Run p c .skip s (.returned t v)) : False := by cases run

/-- Positive final output forces a serial rejecting guard to fall through,
retaining the exact source expression evaluation and its state effects. -/
theorem guard_fallthrough {p : Prototypes} {c : Service} {condition : Expr}
    {tail : List Stmt} {s t : State}
    (steps:SeqRun p c (.branch condition (.returnStmt (.nat 0)) .skip::tail)
      s (.returned t (i32 1))) :
    ∃next value,Eval p c condition s next value ∧WideScalar.truth value=false ∧
      SeqRun p c tail next (.returned t (i32 1)) := by
  cases steps with
  | next first rest=>
    cases first with
    | branch tested body=>
      cases keep:WideScalar.truth _ with
      | false=>
        simp only [keep,Bool.false_eq_true,↓reduceIte] at body
        cases body
        exact ⟨_,_,tested,keep,rest⟩
      | true=>
        simp only [keep,↓reduceIte] at body
        cases body
  | returned first=>
    cases first with
    | branch tested body=>
      cases keep:WideScalar.truth _ with
      | false=>
        simp only [keep,Bool.false_eq_true,↓reduceIte] at body
        exact False.elim (skip_no_return body)
      | true=>
        simp only [keep,↓reduceIte] at body
        have impossible:=zero_return_value body
        cases impossible

theorem declaration_fallthrough {p : Prototypes} {c : Service} {decls : List Decl}
    {tail : List Stmt} {s t : State} {answer : Value}
    (steps:SeqRun p c (.declare decls::tail) s (.returned t answer)) :
    ∃next,Declare p c decls s next ∧SeqRun p c tail next (.returned t answer) := by
  cases steps with
  | next first rest=>cases first with|declare declared=>exact ⟨_,declared,rest⟩
  | returned first=>cases first

theorem final_return_value {p : Prototypes} {c : Service} {e : Expr} {s t : State} {v : Value}
    (steps:SeqRun p c [.returnStmt e] s (.returned t v)) : Eval p c e s t v := by
  cases steps with
  | next first rest=>cases first
  | returned first=>cases first with|returnValue evaluated=>exact evaluated

#print axioms sequence_returned
#print axioms guard_fallthrough
#print axioms declaration_fallthrough
#print axioms final_return_value
end RamanujanPV.FiniteCellDecompose

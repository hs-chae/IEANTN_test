import GoldbachDirect.PureEval

namespace GoldbachDirect.PureEval
open Semantics
open SourcePure

private theorem complete_by_size {F : Type} {context : Context F} (fuel : Nat) :
    ∀ expression : Expr, sizeOf expression < fuel →
      (∀ {state : State F} {pointer : Pointer}, CallFree expression →
        place context state expression = some pointer → Place context state expression pointer state) ∧
      (∀ {state : State F} {value : Value}, CallFree expression →
        eval context state expression = some value → Eval context state expression value state) := by
  induction fuel with
  | zero => intro expression bound; omega
  | succ fuel ih =>
    intro expression bound
    have placeComplete : ∀ {state : State F} {pointer : Pointer}, CallFree expression →
        place context state expression = some pointer → Place context state expression pointer state := by
      intro state pointer closed computed
      cases expression with
      | «variable» name => exact .variable (by simpa only [place] using computed)
      | paren expression =>
          exact .paren ((ih _ (by simp_all; omega)).1 closed (by simpa only [place] using computed))
      | unary op expression =>
          cases op <;> simp only [place] at computed
          all_goals try contradiction
          cases found : eval context state expression with
          | none => simp [found] at computed
          | some value =>
            cases value <;> simp only [found] at computed
            all_goals try contradiction
            cases Option.some.inj computed
            exact .dereference ((ih _ (by simp_all; omega)).2 closed found)
      | index base offset =>
          cases hb : eval context state base with
          | none => simp [place,hb] at computed
          | some value =>
            cases value <;> simp only [place,hb] at computed
            all_goals try contradiction
            cases hi : eval context state offset with
            | none => simp [hi] at computed
            | some value =>
              cases value <;> simp only [hi] at computed
              all_goals try contradiction
              exact .index ((ih _ (by simp_all; omega)).2 closed.1 hb)
                ((ih _ (by simp_all; omega)).2 closed.2 hi) computed
      | _ => simp [place] at computed
    refine ⟨placeComplete,?_⟩
    intro state value closed computed
    cases expression with
    | literal literal => exact .literal literal state value (by simpa only [eval] using computed)
    | paren expression => exact .paren ((ih _ (by simp_all; omega)).2 closed (by simpa only [eval] using computed))
    | «variable» name =>
        cases hp : state.environment.lookup name with
        | some pointer => exact .variable hp (by simpa [eval,hp] using computed)
        | none =>
          simp only [eval,hp] at computed
          by_cases allowed : constantName name
          · exact .constant hp allowed (by simpa [allowed] using computed)
          · simp [allowed] at computed
    | cast type expression =>
        cases found : eval context state expression with
        | none => simp [eval,found] at computed
        | some v =>
          exact .cast ((ih _ (by simp_all; omega)).2 closed found)
            (by simpa [eval,found] using computed)
    | unary op expression =>
        cases op with
        | address =>
          simp only [eval,Option.map_eq_some_iff] at computed
          obtain ⟨pointer,found,same⟩ := computed
          subst value
          exact .address ((ih _ (by simp_all; omega)).1 closed found)
        | dereference =>
          cases found : eval context state expression with
          | none => simp [eval,found] at computed
          | some v =>
            cases v <;> simp only [eval,found] at computed
            all_goals try contradiction
            exact .load (.dereference ((ih _ (by simp_all; omega)).2 closed found)) computed
        | logicalNot | bitNot | negate =>
          cases found : eval context state expression with
          | none => simp [eval,found] at computed
          | some v =>
            cases v <;> simp only [eval,found] at computed
            all_goals try contradiction
            simp [Option.bind_eq_some_iff] at computed
            obtain ⟨result,operation,same⟩ := computed
            subst value
            exact .unary ((ih _ (by simp_all; omega)).2 closed found) operation
    | binary op left right =>
        cases hl : eval context state left with
        | none => cases op <;> simp [eval,hl] at computed
        | some a =>
          have leftRun := (ih _ (by simp_all; omega)).2 closed.1 hl
          cases op with
          | logicalAnd =>
            cases test : a.truth with
            | none => simp [eval,hl,test] at computed
            | some b =>
              cases b with
              | false =>
                simp [eval,hl,test] at computed
                subst value
                exact .andFalse leftRun test
              | true =>
                cases hr : eval context state right with
                | none => simp [eval,hl,test,hr] at computed
                | some b =>
                  cases result : b.truth with
                  | none => simp [eval,hl,test,hr,result] at computed
                  | some truth =>
                    simp [eval,hl,test,hr,result] at computed
                    subst value
                    exact .andTrue leftRun test ((ih _ (by simp_all; omega)).2 closed.2 hr) result
          | logicalOr =>
            cases test : a.truth with
            | none => simp [eval,hl,test] at computed
            | some b =>
              cases b with
              | true =>
                simp [eval,hl,test] at computed
                subst value
                exact .orTrue leftRun test
              | false =>
                cases hr : eval context state right with
                | none => simp [eval,hl,test,hr] at computed
                | some b =>
                  cases result : b.truth with
                  | none => simp [eval,hl,test,hr,result] at computed
                  | some truth =>
                    simp [eval,hl,test,hr,result] at computed
                    subst value
                    exact .orFalse leftRun test ((ih _ (by simp_all; omega)).2 closed.2 hr) result
          | add | sub | mul | div | mod | shl | shr | bitAnd | bitOr | bitXor |
            eq | ne | lt | le | gt | ge =>
              cases hr : eval context state right with
              | none => simp [eval,hl,hr] at computed
              | some b =>
                exact .binaryLR leftRun ((ih _ (by simp_all; omega)).2 closed.2 hr)
                  (by simpa [eval,hl,hr] using computed)
    | index base offset =>
        cases hb : eval context state base with
        | none => simp [eval,hb] at computed
        | some v =>
          cases v <;> simp only [eval,hb] at computed
          all_goals try contradiction
          cases hi : eval context state offset with
          | none => simp [hi] at computed
          | some v =>
            cases v <;> simp only [hi] at computed
            all_goals try contradiction
            simp [Option.bind_eq_some_iff] at computed
            obtain ⟨pointer,added,read⟩ := computed
            exact .load (.index ((ih _ (by simp_all; omega)).2 closed.1 hb)
              ((ih _ (by simp_all; omega)).2 closed.2 hi) added) read
    | member base field arrow =>
        cases base <;> cases arrow <;> simp only [eval] at computed
        all_goals try contradiction
        rename_i name
        by_cases allowed : builtinName name field
        · exact .builtin allowed (by simpa [allowed] using computed)
        · simp [allowed] at computed
    | conditional test yes no =>
        cases ht : eval context state test with
        | none => simp [eval,ht] at computed
        | some v =>
          cases truth : v.truth with
          | none => simp [eval,ht,truth] at computed
          | some b =>
            cases b with
            | true =>
              exact .conditionalTrue ((ih _ (by simp_all; omega)).2 closed.1 ht) truth
                ((ih _ (by simp_all; omega)).2 closed.2.1 (by simpa [eval,ht,truth] using computed))
            | false =>
              exact .conditionalFalse ((ih _ (by simp_all; omega)).2 closed.1 ht) truth
                ((ih _ (by simp_all; omega)).2 closed.2.2 (by simpa [eval,ht,truth] using computed))
    | call => exact False.elim closed

theorem eval_complete {F : Type} {context : Context F} {state : State F}
    {expression : Expr} {value : Value} (closed : CallFree expression)
    (computed : eval context state expression = some value) :
    Eval context state expression value state :=
  (complete_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).2 closed computed

theorem place_complete {F : Type} {context : Context F} {state : State F}
    {expression : Expr} {pointer : Pointer} (closed : CallFree expression)
    (computed : place context state expression = some pointer) :
    Place context state expression pointer state :=
  (complete_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).1 closed computed

end GoldbachDirect.PureEval

import GoldbachDirect.SourcePure

/-! A computational interpreter for call-free host expressions and lvalues.
The soundness theorems below are consequences of the actual Eval/Place rules,
not a new source correspondence or arithmetic assumption. Missing cells and
unsupported operations return none. -/
namespace GoldbachDirect.PureEval
open Semantics
open SourcePure

instance (name : String) : Decidable (constantName name) := by
  unfold constantName
  infer_instance

instance (name field : String) : Decidable (builtinName name field) := by
  unfold builtinName
  infer_instance

mutual
  def eval (context : Context F) (state : State F) (expression : Expr) : Option Value :=
    match expression with
    | .literal value => value.value
    | .paren expression => eval context state expression
    | .variable name =>
      match state.environment.lookup name with
      | some pointer => state.load pointer
      | none => if constantName name then context.headerConstant name else none
    | .cast type expression => do (← eval context state expression).convert type
    | .unary .address expression => (place context state expression).map Value.pointer
    | .unary .dereference expression => do
      let .pointer pointer ← eval context state expression | none
      state.load pointer
    | .unary op expression => do
      let .integer value ← eval context state expression | none
      return .integer (← Integer.unary op value)
    | .binary .logicalAnd left right => do
      let test ← (← eval context state left).truth
      if test then return .integer (.boolean (← (← eval context state right).truth))
      else return .integer (.boolean false)
    | .binary .logicalOr left right => do
      let test ← (← eval context state left).truth
      if test then return .integer (.boolean true)
      else return .integer (.boolean (← (← eval context state right).truth))
    | .binary op left right => do
      binary state op (← eval context state left) (← eval context state right)
    | .index base offset => do
      let .pointer pointer ← eval context state base | none
      let .integer index ← eval context state offset | none
      state.load (← state.pointerAdd pointer index.toInt)
    | .member (.variable name) field false =>
      if builtinName name field then context.builtin name field else none
    | .member _ _ _ | .call _ _ => none
    | .conditional test yes no => do
      let choice ← (← eval context state test).truth
      if choice then eval context state yes else eval context state no
  termination_by sizeOf expression

  def place (context : Context F) (state : State F) (expression : Expr) : Option Pointer :=
    match expression with
    | .variable name => state.environment.lookup name
    | .paren expression => place context state expression
    | .unary .dereference expression => do
      let .pointer pointer ← eval context state expression | none
      return pointer
    | .index base offset => do
      let .pointer pointer ← eval context state base | none
      let .integer index ← eval context state offset | none
      state.pointerAdd pointer index.toInt
    | _ => none
  termination_by sizeOf expression
end

private theorem binary_and_none (state : State F) (a b : Value) :
    binary state .logicalAnd a b = none := by
  cases a <;> cases b <;> simp [binary, Integer.binary]

private theorem binary_or_none (state : State F) (a b : Value) :
    binary state .logicalOr a b = none := by
  cases a <;> cases b <;> simp [binary, Integer.binary]

private theorem sound_by_size {F : Type} {context : Context F} (fuel : Nat) :
    ∀ expression : Expr, sizeOf expression < fuel →
      (∀ {before after : State F} {pointer : Pointer},
        Place context before expression pointer after → CallFree expression →
          place context before expression = some pointer ∧
          eval context before expression = before.load pointer) ∧
      (∀ {before after : State F} {value : Value},
        Eval context before expression value after → CallFree expression →
          eval context before expression = some value) := by
  induction fuel with
  | zero => intro expression bound; omega
  | succ fuel ih =>
    intro expression bound
    have placeSound : ∀ {before after : State F} {pointer : Pointer},
        Place context before expression pointer after → CallFree expression →
          place context before expression = some pointer ∧
          eval context before expression = before.load pointer := by
      intro before after pointer run closed
      cases run with
      | «variable» present => simp [place,eval,present]
      | paren run =>
          obtain ⟨hp,he⟩ := (ih _ (by simp_all; omega)).1 run closed
          simpa only [place,eval] using And.intro hp he
      | dereference run =>
          have he := (ih _ (by simp_all; omega)).2 run closed
          simp [place,eval,he]
      | index base index added =>
          have hs := SourcePure.eval_state base closed.1
          have ht := SourcePure.eval_state index closed.2
          subst_vars
          have hb := (ih _ (by simp_all; omega)).2 base closed.1
          have hi := (ih _ (by simp_all; omega)).2 index closed.2
          simp [place,eval,hb,hi,added]
    refine ⟨placeSound,?_⟩
    intro before after value run closed
    cases run with
    | literal => simp only [eval]; assumption
    | paren run => simpa only [eval] using (ih _ (by simp_all; omega)).2 run closed
    | «variable» present read => simp [eval,present,read]
    | constant absent allowed read => simp [eval,absent,allowed,read]
    | builtin allowed read => simp [eval,allowed,read]
    | address run =>
        have hp := ((ih _ (by simp_all; omega)).1 run closed).1
        simp [eval,hp]
    | load run read =>
        have hs := SourcePure.place_state run closed
        subst_vars
        exact (placeSound run closed).2.trans read
    | cast run converted =>
        have he := (ih _ (by simp_all; omega)).2 run closed
        simp [eval,he,converted]
    | @unary _ _ _ _ op _ run computed =>
        have he := (ih _ (by simp_all; omega)).2 run closed
        cases op <;> simp_all [eval,Integer.unary]
    | binaryLR left right computed =>
        have hs := SourcePure.eval_state left closed.1
        have ht := SourcePure.eval_state right closed.2
        subst_vars
        have hl := (ih _ (by simp_all; omega)).2 left closed.1
        have hr := (ih _ (by simp_all; omega)).2 right closed.2
        rename_i op
        cases op <;> simp_all [eval,binary_and_none,binary_or_none]
    | binaryRL right left computed =>
        have hs := SourcePure.eval_state right closed.2
        have ht := SourcePure.eval_state left closed.1
        subst_vars
        have hl := (ih _ (by simp_all; omega)).2 left closed.1
        have hr := (ih _ (by simp_all; omega)).2 right closed.2
        rename_i op
        cases op <;> simp_all [eval,binary_and_none,binary_or_none]
    | andFalse left test =>
        have he := (ih _ (by simp_all; omega)).2 left closed.1
        simp [eval,he,test]
    | andTrue left test right result =>
        have hs := SourcePure.eval_state left closed.1
        subst_vars
        have hl := (ih _ (by simp_all; omega)).2 left closed.1
        have hr := (ih _ (by simp_all; omega)).2 right closed.2
        simp [eval,hl,hr,test,result]
    | orTrue left test =>
        have he := (ih _ (by simp_all; omega)).2 left closed.1
        simp [eval,he,test]
    | orFalse left test right result =>
        have hs := SourcePure.eval_state left closed.1
        subst_vars
        have hl := (ih _ (by simp_all; omega)).2 left closed.1
        have hr := (ih _ (by simp_all; omega)).2 right closed.2
        simp [eval,hl,hr,test,result]
    | conditionalTrue test truth branch =>
        have hs := SourcePure.eval_state test closed.1
        subst_vars
        have ht := (ih _ (by simp_all; omega)).2 test closed.1
        have hb := (ih _ (by simp_all; omega)).2 branch closed.2.1
        simp [eval,ht,hb,truth]
    | conditionalFalse test truth branch =>
        have hs := SourcePure.eval_state test closed.1
        subst_vars
        have ht := (ih _ (by simp_all; omega)).2 test closed.1
        have hb := (ih _ (by simp_all; omega)).2 branch closed.2.2
        simp [eval,ht,hb,truth]
    | call => exact False.elim closed

/-- Every call-free evaluation computes the unique pure value and preserves the
complete actual state, including host objects and the CUDA protocol state. -/
theorem eval_sound {F : Type} {context : Context F} {expression : Expr}
    {before after : State F} {value : Value}
    (run : Eval context before expression value after) (closed : CallFree expression) :
    after = before ∧ eval context before expression = some value :=
  ⟨SourcePure.eval_state run closed,
    (sound_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).2 run closed⟩

/-- Lvalue computation has the same unique pointer. Reading that lvalue is
exactly the existing initialized, typed and bounded State.load operation. -/
theorem place_sound {F : Type} {context : Context F} {expression : Expr}
    {before after : State F} {pointer : Pointer}
    (run : Place context before expression pointer after) (closed : CallFree expression) :
    after = before ∧ place context before expression = some pointer ∧
      eval context before expression = before.load pointer :=
  ⟨SourcePure.place_state run closed,
    (sound_by_size (sizeOf expression+1) expression (Nat.lt_succ_self _)).1 run closed⟩

end GoldbachDirect.PureEval

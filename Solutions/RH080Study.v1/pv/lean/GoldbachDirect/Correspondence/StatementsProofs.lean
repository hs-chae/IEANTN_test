import GoldbachDirect.Correspondence.Statements

namespace GoldbachDirect.Correspondence

theorem objectTypeGuard_sound {t : CType} (h : objectTypeGuard t = true) :
    typeSyntaxSafe t = true ∧ ObjectType t := by
  simpa only [objectTypeGuard, Bool.and_eq_true, decide_eq_true_eq] using h

theorem targetGuard_sound : ∀ e, targetGuard e = true → AssignmentTarget e
  | .variable name, _ => .variable name
  | .index base offset, _ => .index base offset
  | .unary .dereference value, _ => .dereference value
  | .paren value, h => .paren (targetGuard_sound value h)
  | .literal _, h | .cast .., h | .binary .., h | .member .., h | .call .., h |
      .conditional .., h => by simp [targetGuard] at h
  | .unary .logicalNot _, h | .unary .bitNot _, h | .unary .negate _, h |
      .unary .address _, h => by simp [targetGuard] at h

theorem delimitedGuard_sound {s : Stmt} (h : delimitedGuard s = true) : Delimited s := by
  cases s <;> simp_all [delimitedGuard]
  · exact .block _
  · exact .gotoLabel _

theorem executableGuard_sound {s : Stmt} (h : executableGuard s = true) : Executable s := by
  cases s <;> simp_all [executableGuard, Executable]

theorem arguments_tokens_syntax (E : List String → Expr → Prop) (exprOK : Expr → Bool)
    (sound : ∀ e, exprOK e = true → E e.tokens e) (args : List Expr)
    (h : args.all exprOK = true) :
    ArgumentsSyntax E (List.flatten ((args.map Expr.tokens).intersperse [","])) args := by
  induction args with
  | nil => exact .nil
  | cons e es ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases es with
    | nil => simpa using ArgumentsSyntax.singleton (sound e h.1)
    | cons e' rest =>
      simpa only [List.map_cons, List.intersperse_cons_cons, List.flatten_cons,
        List.singleton_append, List.append_assoc] using
        ArgumentsSyntax.cons (sound e h.1) (ih h.2) (by simp)

/-- Simultaneous fuel induction follows guard recursion; the targets are the independent
ordinary-statement and compound-item grammars, not a restatement of guard success. -/
theorem statement_items_tokens_syntax (E : List String → Expr → Prop) (N : String → Prop)
    (exprOK : Expr → Bool) (nameOK : String → Bool)
    (exprSound : ∀ e, exprOK e = true → E e.tokens e)
    (nameSound : ∀ n, nameOK n = true → N n) (fuel : Nat) :
    (∀ s, statementGuard exprOK nameOK fuel s = true → StatementSyntax E N s.tokens s) ∧
    (∀ items, itemsGuard exprOK nameOK fuel items = true →
      ItemsSyntax E N (List.flatten (items.map Stmt.tokens)) items) := by
  induction fuel with
  | zero => simp [statementGuard, itemsGuard]
  | succ fuel ih =>
    constructor
    · intro s h
      cases s with
      | block body =>
        simpa only [Stmt.tokens] using StatementSyntax.block (ih.2 body h)
      | declare t n value =>
        simp only [statementGuard, Bool.and_eq_true] at h
        have th := objectTypeGuard_sound h.1.1
        cases value with
        | none =>
          simpa only [Stmt.tokens, List.append_nil, List.append_assoc,
            List.singleton_append] using
            StatementSyntax.declare (type_tokens_syntax t th.1) th.2 (nameSound n h.1.2)
        | some e =>
          simp only [Option.toList_some, List.all_cons, List.all_nil, Bool.and_true] at h
          simpa [Stmt.tokens, List.append_assoc] using
            StatementSyntax.initialize (type_tokens_syntax t th.1) th.2
              (nameSound n h.1.2) (exprSound e h.2)
      | assign d e =>
        simp only [statementGuard, Bool.and_eq_true] at h
        simpa only [Stmt.tokens] using
          StatementSyntax.assign (N := N) (exprSound d h.1.2)
            (targetGuard_sound d h.1.1) (exprSound e h.2)
      | expression e =>
        simpa only [Stmt.tokens] using StatementSyntax.expression (N := N) (exprSound e h)
      | ite c y no =>
        cases no with
        | none =>
          simp only [statementGuard, Bool.and_eq_true, Option.toList_none,
            List.all_nil, and_true] at h
          simpa only [Stmt.tokens, List.append_nil] using
            StatementSyntax.ifThen (exprSound c h.1.1) (ih.1 y h.2)
              (delimitedGuard_sound h.1.2)
        | some n =>
          simp only [statementGuard, Bool.and_eq_true, Option.toList_some,
            List.all_cons, List.all_nil, Bool.and_true] at h
          simpa only [Stmt.tokens, List.append_assoc, List.singleton_append] using
            StatementSyntax.ifElse (exprSound c h.1.1.1) (ih.1 y h.1.2)
              (delimitedGuard_sound h.1.1.2) (ih.1 n h.2.2)
              (delimitedGuard_sound h.2.1)
      | whileLoop c b =>
        simp only [statementGuard, Bool.and_eq_true] at h
        simpa only [Stmt.tokens] using
          StatementSyntax.whileLoop (exprSound c h.1.1) (ih.1 b h.2)
            (delimitedGuard_sound h.1.2)
      | returnValue value =>
        cases value with
        | none => simpa [Stmt.tokens] using StatementSyntax.returnVoid (E := E) (N := N)
        | some e =>
          simp only [statementGuard, Option.toList_some, List.all_cons, List.all_nil,
            Bool.and_true] at h
          simpa only [Stmt.tokens] using StatementSyntax.returnValue (N := N) (exprSound e h)
      | gotoLabel n =>
        simpa only [Stmt.tokens] using StatementSyntax.gotoLabel (E := E) (nameSound n h)
      | launch n g b shared stream args =>
        simp only [statementGuard, Bool.and_eq_true, List.all_append, List.all_cons,
          List.all_nil, and_true] at h
        simpa only [Stmt.tokens, comma, List.intersperse, List.map_cons, List.flatten_cons,
          List.flatten_nil, List.append_nil, List.singleton_append, List.append_assoc,
          List.cons_append, List.nil_append] using
          StatementSyntax.launch (nameSound n h.1) (exprSound g h.2.1.1)
            (exprSound b h.2.1.2.1) (exprSound shared h.2.1.2.2.1)
            (exprSound stream h.2.1.2.2.2)
            (arguments_tokens_syntax E exprOK exprSound args h.2.2)
      | _ =>
        simp [statementGuard] at h
    · intro items h
      cases items with
      | nil => exact .nil
      | cons s rest =>
        cases s with
        | label n =>
          cases rest with
          | nil => simp [itemsGuard] at h
          | cons s rest =>
            simp only [itemsGuard, Bool.and_eq_true] at h
            simpa only [List.map_cons, List.flatten_cons, Stmt.tokens, List.append_assoc]
              using ItemsSyntax.labeled (nameSound n h.1.1.1)
                (executableGuard_sound h.1.1.2) (ih.1 s h.1.2) (ih.2 rest h.2)
        | _ =>
          simp only [itemsGuard, Bool.and_eq_true] at h
          exact .cons (ih.1 _ h.1) (ih.2 _ h.2)

theorem qualifiers_tokens_syntax (qs : List Qualifier) (h : qualifiersGuard qs = true) :
    QualifiersSyntax (qs.map Qualifier.token) qs := by
  cases qs with
  | nil => exact .plain
  | cons q rest =>
    cases q <;> cases rest <;> simp_all [qualifiersGuard, Qualifier.token]
    · exact .local
    · exact .kernel

theorem parameters_tokens_syntax (N : String → Prop) (nameOK : String → Bool)
    (sound : ∀ n, nameOK n = true → N n) (ps : List (CType × String))
    (h : ps.all (fun p => objectTypeGuard p.1 && nameOK p.2) = true) :
    ParametersSyntax N
      (List.flatten ((ps.map (fun p => p.1.tokens ++ [p.2])).intersperse [","])) ps := by
  induction ps with
  | nil => exact .nil
  | cons p ps ih =>
    rcases p with ⟨t, n⟩
    simp only [List.all_cons, Bool.and_eq_true] at h
    have th := objectTypeGuard_sound h.1.1
    have nh := sound n h.1.2
    cases ps with
    | nil =>
      simpa using ParametersSyntax.singleton (type_tokens_syntax t th.1) th.2 nh
    | cons p rest =>
      simpa only [List.map_cons, List.intersperse_cons_cons, List.flatten_cons,
        List.singleton_append, List.append_assoc, List.cons_append, List.nil_append] using
        ParametersSyntax.cons (type_tokens_syntax t th.1) th.2 nh (ih h.2) (by simp)

theorem function_tokens_syntax (E : List String → Expr → Prop) (N : String → Prop)
    (exprOK : Expr → Bool) (nameOK : String → Bool)
    (exprSound : ∀ e, exprOK e = true → E e.tokens e)
    (nameSound : ∀ n, nameOK n = true → N n) (f : Function)
    (h : functionGuard exprOK nameOK f = true) : FunctionSyntax E N f.tokens f := by
  rcases f with ⟨qs, emptyVoid, result, name, ps, body⟩
  cases body with
  | block items =>
    simp only [functionGuard, Bool.and_eq_true] at h
    have qh := qualifiers_tokens_syntax qs h.1.1.1.1
    have rh := type_tokens_syntax result h.1.1.1.2
    have nh := nameSound name h.1.1.2
    have ph := parameters_tokens_syntax N nameOK nameSound ps h.1.2
    have bh := (statement_items_tokens_syntax E N exprOK nameOK exprSound nameSound 1024).2
      items h.2
    cases emptyVoid with
    | false =>
      simpa [Function.tokens, Stmt.tokens, comma, List.append_assoc] using
        FunctionSyntax.ordinary qh rh nh ph bh (Or.inl rfl)
    | true =>
      cases ps with
      | nil =>
        simpa [Function.tokens, Stmt.tokens, comma, List.append_assoc] using
          FunctionSyntax.voidParameters qh rh nh bh
      | cons p rest =>
        simpa [Function.tokens, Stmt.tokens, comma, List.append_assoc] using
          FunctionSyntax.ordinary qh rh nh ph bh (Or.inr (by simp))
  | _ => simp [functionGuard] at h

theorem header_tokens_syntax (h : Header) : HeaderSyntax h.tokens h := by
  cases h <;> constructor

theorem programGuard_sound (E : List String → Expr → Prop) (N : String → Prop)
    (exprOK : Expr → Bool) (nameOK : String → Bool)
    (exprSound : ∀ e, exprOK e = true → E e.tokens e)
    (nameSound : ∀ n, nameOK n = true → N n) (p : Program)
    (h : programGuard exprOK nameOK p = true) : ProgramSyntax E N p.tokens p := by
  induction p with
  | nil => exact .nil
  | cons top rest ih =>
    simp only [programGuard, List.all_cons, Bool.and_eq_true] at h
    have restSyntax := ih h.2
    have topSyntax : TopSyntax E N top.tokens top := by
      cases top with
      | «include» header => exact .include (header_tokens_syntax header)
      | pragmaOnce => exact .pragmaOnce
      | function f =>
        exact .function (function_tokens_syntax E N exprOK nameOK exprSound nameSound f h.1)
    simpa only [Program.tokens, List.map_cons, List.flatten_cons] using
      ProgramSyntax.cons topSyntax restSyntax

/-- Concrete application checker used by the final source certificate. -/
def programSyntaxSafe (p : Program) : Bool :=
  programGuard (exprSyntaxSafe 1024) syntaxIdentifier p

/-- General grammar correspondence, proved in the kernel without native decision. -/
theorem programSyntaxSafe_sound {p : Program} (h : programSyntaxSafe p = true) :
    ProgramSyntax (ExpressionSyntax 13) (fun n => syntaxIdentifier n = true) p.tokens p := by
  exact programGuard_sound (ExpressionSyntax 13) (fun n => syntaxIdentifier n = true)
    (exprSyntaxSafe 1024) syntaxIdentifier (fun _ he => exprSyntaxSafe_sound he)
    (fun _ hn => hn) p h

/-- There is no grammar rule interpreting a bare colon label as a complete statement. -/
theorem standalone_label_not_statement (E : List String → Expr → Prop) (N : String → Prop)
    (ts : List String) (name : String) : ¬ StatementSyntax E N ts (.label name) := by
  intro h
  cases h

theorem functionSyntax_body_compound {E : List String → Expr → Prop} {N : String → Prop}
    {ts : List String} {f : Function} (h : FunctionSyntax E N ts f) :
    ∃ items, f.body = .block items := by
  cases h <;> exact ⟨_, rfl⟩

/-- This exclusion is a grammar fact, independent of the executable guard. In conjunction
with the historical finite acceptance counterexample it refutes the old universal claim. -/
theorem noncompound_function_not_syntax (E : List String → Expr → Prop) (N : String → Prop)
    (ts : List String) (f : Function) (notBlock : ∀ items, f.body ≠ .block items) :
    ¬ FunctionSyntax E N ts f := by
  intro h
  obtain ⟨items, body⟩ := functionSyntax_body_compound h
  exact notBlock items body

end GoldbachDirect.Correspondence

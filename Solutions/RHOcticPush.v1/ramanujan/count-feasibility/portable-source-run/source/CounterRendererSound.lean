import CounterGrammar

/-! Generic soundness of guarded printing into the independent C11 character
grammar. Guards reject the renderer's unsupported arbitrary strings and shapes.
No numerical execution result or expected application output is a premise. -/
namespace RHOcticPush.CounterSyntax
open LCMSourcePV.Witness.C
set_option maxHeartbeats 0

instance (name : String) : Decidable (TypeName name) := by
  unfold TypeName
  infer_instance
instance (op : String) : Decidable (BinarySymbol op) := by
  unfold BinarySymbol
  infer_instance
instance (op : String) : Decidable (UnarySymbol op) := by
  unfold UnarySymbol
  infer_instance

def expressionGuard : Nat → Expr → Bool
  | 0, _ => false
  | _+1, .nat n => decide (Decimal (toString n) n)
  | _+1, .var name => decide (Identifier name)
  | n+1, .unary op e => decide (UnarySymbol op) && lvalue e && expressionGuard n e
  | n+1, .binary op a b => decide (BinarySymbol op) &&
      (if op = "=" then lvalue a else true) && expressionGuard n a && expressionGuard n b
  | n+1, .index (.var name) i => expressionGuard n (.var name) && expressionGuard n i
  | n+1, .call (.var name) args => expressionGuard n (.var name) && args.all (expressionGuard n)
  | _+1, _ => false

def declarationGuard (d : Decl) : Bool := decide (TypeName d.type) &&
  decide (BindingName d.name) && match d.value with
    | none => true
    | some e => expressionGuard 1000 e

def statementGuard : Nat → Stmt → Bool
  | 0, _ => false
  | _+1, .skip => true
  | n+1, .sequence body => body.all (fun s => match s with
      | .declare [d] => declarationGuard d
      | .declare _ => false
      | _ => statementGuard n s)
  | _+1, .eval e | _+1, .returnStmt e => expressionGuard 1000 e
  | n+1, .branch c a b => expressionGuard 1000 c && statementGuard n a && statementGuard n b
  | n+1, .whileLoop c body => expressionGuard 1000 c && statementGuard n body
  | n+1, .forLoop (.declare [d]) condition step body => declarationGuard d &&
      (match condition with | none => true | some e => expressionGuard 1000 e) &&
      expressionGuard 1000 step && statementGuard n body
  | _+1, _ => false

def parameterGuard (p : String × String) : Bool :=
  decide (TypeName p.1) && decide (BindingName p.2)

def functionGuard (f : Function) : Bool := decide (TypeName f.returnType) &&
  decide (BindingName f.name) && f.parameters.all parameterGuard &&
    match f.body with
    | .sequence _ => statementGuard 1000 f.body
    | _ => false

theorem mapM_separated {α : Type} (sep : String) (f : α → Option String)
    (g : α → Bool) (P : String → α → Prop)
    (sound : ∀ a text,f a = some text → g a = true → P text a)
    {xs : List α} {ys : List String} (guard : xs.all g = true)
    (printed : xs.mapM f = some ys) : Separated sep P (String.intercalate sep ys) xs := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil,Option.pure_def,Option.some.injEq] at printed
    subst ys
    exact Separated.nil
  | cons a xs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at guard
    cases hh : f a with
    | none => simp [List.mapM_cons,hh] at printed
    | some head =>
      cases ht : xs.mapM f with
      | none => simp [List.mapM_cons,hh,ht] at printed
      | some tail =>
        have he : head::tail = ys := by simpa [List.mapM_cons,hh,ht] using printed
        subst ys
        have hp := sound a head hh guard.1
        have hrest := ih guard.2 ht
        cases xs with
        | nil =>
          simp only [List.mapM_nil,Option.pure_def,Option.some.injEq] at ht
          subst tail
          simpa using Separated.singleton hp
        | cons b bs =>
          have hn : tail ≠ [] := by
            intro h
            subst tail
            cases hfb : f b with
            | none => simp [List.mapM_cons,hfb] at ht
            | some value =>
              cases hbs : bs.mapM f <;> simp [List.mapM_cons,hfb,hbs] at ht
          rw [String.intercalate_cons_of_ne_nil hn]
          exact Separated.cons hp hrest (by simp)

/-- Soundness is general over fuel, expressions and successful output text;
the target is the separately specified grammar, not an equality to printing. -/
theorem expression_sound {fuel : Nat} {e : Expr} {text : String}
    (printed : renderExpr fuel e = some text) (guard : expressionGuard fuel e = true) :
    Expression text e := by
  induction fuel generalizing e text with
  | zero => simp [renderExpr] at printed
  | succ fuel ih =>
    cases e with
    | nat n =>
      simp only [renderExpr,Option.some.injEq] at printed
      subst text
      exact Expression.natural (by simpa only [expressionGuard,decide_eq_true_eq] using guard)
    | var name =>
      simp only [renderExpr,Option.some.injEq] at printed
      subst text
      exact Expression.variable (by simpa only [expressionGuard,decide_eq_true_eq] using guard)
    | unary op e =>
      simp only [expressionGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
      cases ha : renderExpr fuel e with
      | none => simp [renderExpr,ha] at printed
      | some value =>
        have he : "("++op++value++")" = text := by simpa [renderExpr,ha] using printed
        subst text
        exact Expression.unary guard.1.1 guard.1.2 (ih ha guard.2)
    | binary op a b =>
      simp only [expressionGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
      cases hl : renderExpr fuel a with
      | none => simp [renderExpr,hl] at printed
      | some left =>
        cases hr : renderExpr fuel b with
        | none => simp [renderExpr,hl,hr] at printed
        | some right =>
          have he : "("++left++op++right++")" = text := by
            simpa [renderExpr,hl,hr] using printed
          subst text
          apply Expression.binary guard.1.1.1
          · intro he
            simpa only [he,↓reduceIte] using guard.1.1.2
          · exact ih hl guard.1.2
          · exact ih hr guard.2
    | index object i =>
      cases object <;> try { simp [expressionGuard] at guard }
      rename_i name
      simp only [expressionGuard,Bool.and_eq_true] at guard
      cases hb : renderExpr fuel (.var name) with
      | none => simp [renderExpr,hb] at printed
      | some base =>
        cases hi : renderExpr fuel i with
        | none => simp [renderExpr,hb,hi] at printed
        | some index =>
          have he : "("++base++"["++index++"])" = text := by
            simpa [renderExpr,hb,hi] using printed
          subst text
          have ho := ih hb guard.1
          cases ho with
          | «variable» hn => exact Expression.index hn (ih hi guard.2)
    | call function args =>
      cases function <;> try { simp [expressionGuard] at guard }
      rename_i name
      simp only [expressionGuard,Bool.and_eq_true] at guard
      cases hb : renderExpr fuel (.var name) with
      | none => simp [renderExpr,hb] at printed
      | some base =>
        cases hp : args.mapM (renderExpr fuel) with
        | none => simp [renderExpr,hb,hp] at printed
        | some parts =>
          have he : base++"("++join parts++")" = text := by
            simpa [renderExpr,hb,hp] using printed
          subst text
          have hf := ih hb guard.1
          cases hf with
          | «variable» hn =>
            exact Expression.call hn (mapM_separated "," (renderExpr fuel) (expressionGuard fuel)
              Expression (fun a t h g => ih h g) guard.2 hp)
    | post op e | cast ty e | field op e name | record xs =>
      simp [expressionGuard] at guard

theorem declaration_sound {d : Decl} {text : String}
    (printed : renderDecl d = some text) (guard : declarationGuard d = true) :
    Declaration text d := by
  rcases d with ⟨ty,name,value⟩
  cases value with
  | none =>
    simp only [declarationGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
    have he : ty++" "++name = text := by simpa [renderDecl] using printed
    subst text
    exact Declaration.uninitialized guard.1.1 guard.1.2
  | some e =>
    simp only [declarationGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
    cases he : renderExpr 1000 e with
    | none => simp [renderDecl,he] at printed
    | some value =>
      have ht : ty++" "++name++"="++value = text := by
        simpa [renderDecl,he,String.append_assoc] using printed
      subst text
      exact Declaration.initialized guard.1.1 guard.1.2 (expression_sound he guard.2)

theorem single_declaration_sound {fuel : Nat} {d : Decl} {text : String}
    (printed : renderStmt fuel (.declare [d]) = some text)
    (guard : declarationGuard d = true) :
    ∃ inner, Declaration inner d ∧ text = inner++";" := by
  cases fuel with
  | zero => simp [renderStmt] at printed
  | succ fuel =>
    cases hd : renderDecl d with
    | none => simp [renderStmt,List.mapM_cons,hd] at printed
    | some inner =>
      have he : inner++";" = text := by simpa [renderStmt,List.mapM_cons,hd] using printed
      exact ⟨inner,declaration_sound hd guard,he.symm⟩

def itemGuard (fuel : Nat) (s : Stmt) : Bool := match s with
  | .declare [d] => declarationGuard d
  | .declare _ => false
  | _ => statementGuard fuel s

def conditionGuard : Option Expr → Bool
  | none => true
  | some e => expressionGuard 1000 e

def printCondition : Option Expr → Option String
  | none => some ""
  | some e => renderExpr 1000 e

theorem condition_sound {c : Option Expr} {text : String}
    (printed : printCondition c = some text) (guard : conditionGuard c = true) :
    Condition text c := by
  cases c with
  | none => simp [printCondition] at printed; subst text; exact Condition.omitted
  | some e => exact Condition.present (expression_sound printed guard)

/-- Every successful guarded ordinary statement prints a matched C11 statement.
Block declarations and for-declaration initializers are handled separately. -/
theorem statement_sound {fuel : Nat} {s : Stmt} {text : String}
    (printed : renderStmt fuel s = some text) (guard : statementGuard fuel s = true) :
    Statement text s := by
  induction fuel generalizing s text with
  | zero => simp [renderStmt] at printed
  | succ fuel ih =>
    cases s with
    | skip => simp [renderStmt] at printed; subst text; exact Statement.skip
    | declare ds => simp [statementGuard] at guard
    | sequence body =>
      change body.all (itemGuard fuel) = true at guard
      have itemSound (s : Stmt) (src : String) (hr : renderStmt fuel s = some src)
          (hg : itemGuard fuel s = true) : BlockItem src s := by
        cases s <;> try { exact BlockItem.statement (ih hr (by simpa [itemGuard] using hg)) }
        case declare ds =>
          cases ds with
          | nil => simp [itemGuard] at hg
          | cons d ds =>
            cases ds with
            | nil =>
              obtain ⟨inner,hd,he⟩ := single_declaration_sound hr (by simpa [itemGuard] using hg)
              rw [he]
              exact BlockItem.declaration hd
            | cons d' rest => simp [itemGuard] at hg
      cases hb : body.mapM (renderStmt fuel) with
      | none => simp [renderStmt,hb] at printed
      | some parts =>
        have he : "{"++String.intercalate "\n" parts++"}" = text := by
          simpa [renderStmt,hb] using printed
        subst text
        exact Statement.block (mapM_separated "\n" (renderStmt fuel) (itemGuard fuel)
          BlockItem itemSound guard hb)
    | eval e =>
      cases he : renderExpr 1000 e with
      | none => simp [renderStmt,he] at printed
      | some value =>
        have ht : value++";" = text := by simpa [renderStmt,he] using printed
        subst text
        exact Statement.evaluate (expression_sound he guard)
    | returnStmt e =>
      cases he : renderExpr 1000 e with
      | none => simp [renderStmt,he] at printed
      | some value =>
        have ht : "return "++value++";" = text := by simpa [renderStmt,he] using printed
        subst text
        exact Statement.returnValue (expression_sound he guard)
    | branch c a b =>
      simp only [statementGuard,Bool.and_eq_true] at guard
      cases hc : renderExpr 1000 c with
      | none => simp [renderStmt,hc] at printed
      | some condition =>
        cases ha : renderStmt fuel a with
        | none => simp [renderStmt,hc,ha] at printed
        | some yes =>
          cases hb : renderStmt fuel b with
          | none => simp [renderStmt,hc,ha,hb] at printed
          | some no =>
            have he : "if("++condition++")"++yes++"else "++no = text := by
              simpa [renderStmt,hc,ha,hb] using printed
            subst text
            exact Statement.branch (expression_sound hc guard.1.1)
              (ih ha guard.1.2) (ih hb guard.2)
    | whileLoop c body =>
      simp only [statementGuard,Bool.and_eq_true] at guard
      cases hc : renderExpr 1000 c with
      | none => simp [renderStmt,hc] at printed
      | some condition =>
        cases hb : renderStmt fuel body with
        | none => simp [renderStmt,hc,hb] at printed
        | some inner =>
          have he : "while("++condition++")"++inner = text := by
            simpa [renderStmt,hc,hb] using printed
          subst text
          exact Statement.whileLoop (expression_sound hc guard.1) (ih hb guard.2)
    | forLoop initial condition step body =>
      cases initial <;> try { simp [statementGuard] at guard }
      rename_i ds
      cases ds with
      | nil => simp [statementGuard] at guard
      | cons d ds =>
        cases ds with
        | cons d' rest => simp [statementGuard] at guard
        | nil =>
          change (declarationGuard d && conditionGuard condition &&
            expressionGuard 1000 step && statementGuard fuel body) = true at guard
          simp only [Bool.and_eq_true] at guard
          have printed' : (do
              let init ← renderStmt fuel (.declare [d])
              let cond ← printCondition condition
              let increment ← renderExpr 1000 step
              let inner ← renderStmt fuel body
              pure ("for("++init++cond++";"++increment++")"++inner)) = some text := by
            cases condition <;> simpa [renderStmt,printCondition] using printed
          cases hi : renderStmt fuel (.declare [d]) with
          | none => simp [hi] at printed'
          | some init =>
            obtain ⟨decl,hd,he⟩ := single_declaration_sound hi guard.1.1.1
            cases hc : printCondition condition with
            | none => simp [hi,hc] at printed'
            | some cond =>
              cases hs : renderExpr 1000 step with
              | none => simp [hi,hc,hs] at printed'
              | some increment =>
                cases hb : renderStmt fuel body with
                | none => simp [hi,hc,hs,hb] at printed'
                | some inner =>
                  have ht : "for("++init++cond++";"++increment++")"++inner = text := by
                    simpa [hi,hc,hs,hb] using printed'
                  subst text
                  rw [he]
                  simpa only [String.append_assoc] using Statement.forLoop hd
                    (condition_sound hc guard.1.1.2) (expression_sound hs guard.1.2)
                    (ih hb guard.2)

theorem parameters_sound {ps : List (String × String)} (guard : ps.all parameterGuard = true) :
    Separated "," Parameter (join (ps.map fun (ty,name) => ty++" "++name)) ps := by
  have typed : ∀ (p : String × String) text,
      some (p.1++" "++p.2) = some text → parameterGuard p = true → Parameter text p := by
    intro p text hp hg
    simp only [Option.some.injEq] at hp
    subst text
    have hh : TypeName p.1 ∧ BindingName p.2 := by
      simpa only [parameterGuard,Bool.and_eq_true,decide_eq_true_eq] using hg
    exact Parameter.typed hh.1 hh.2
  exact mapM_separated "," (fun (p : String × String) => some (p.1++" "++p.2))
    parameterGuard Parameter typed guard (by induction ps <;> simp_all [List.mapM_cons])

theorem function_sound {f : Function} {text : String}
    (printed : renderFunction f = some text) (guard : functionGuard f = true) :
    FunctionSyntax text f := by
  rcases f with ⟨ty,name,parameters,body⟩
  cases body <;> try { simp [functionGuard] at guard }
  rename_i items
  simp only [functionGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
  cases hb : renderStmt 1000 (.sequence items) with
  | none => simp [renderFunction,hb] at printed
  | some inner =>
    have he : ty++" "++name++"("++join (parameters.map fun (t,n) => t++" "++n)++")"++
        inner++"\n" = text := by simpa [renderFunction,hb] using printed
    subst text
    exact FunctionSyntax.definition guard.1.1.1 guard.1.1.2
      (parameters_sound guard.1.2) (statement_sound hb guard.2) rfl

theorem functions_sound {fs : List Function} {text : String}
    (printed : renderFunctions fs = some text) (guard : fs.all functionGuard = true) :
    Separated "\n" FunctionSyntax text fs := by
  cases hp : fs.mapM renderFunction with
  | none => simp [renderFunctions,hp] at printed
  | some texts =>
    have he : String.intercalate "\n" texts = text := by
      simpa [renderFunctions,hp] using printed
    subst text
    exact mapM_separated "\n" renderFunction functionGuard FunctionSyntax
      (fun _ _ hp hg => function_sound hp hg) guard hp

open RamanujanPV.QuotientDriverSource

def prototypeGuard (p : Prototype) : Bool := decide (TypeName p.returnType) &&
  decide (BindingName p.name) && p.parameters.all parameterGuard

theorem prototype_sound (p : Prototype) (guard : prototypeGuard p = true) :
    PrototypeSyntax (renderPrototype p) p := by
  rcases p with ⟨ty,name,params⟩
  simp only [prototypeGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
  exact PrototypeSyntax.external guard.1.1 guard.1.2 (parameters_sound guard.2)

def arrayGuard (a : StaticArray) : Bool := decide (BindingName a.name) &&
  decide (Decimal (toString a.count) a.count) && decide (0 < a.count)

theorem array_sound (a : StaticArray) (guard : arrayGuard a = true) :
    ArraySyntax (renderArray a) a := by
  rcases a with ⟨name,element,count⟩
  cases element
  simp only [arrayGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
  exact ArraySyntax.u64 guard.1.1 guard.1.2 guard.2

theorem globals_sound {xs : List StaticArray} (guard : xs.all arrayGuard = true) :
    GlobalsSyntax (String.join (xs.map renderArray)) xs := by
  induction xs with
  | nil => exact GlobalsSyntax.nil
  | cons a xs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at guard
    simpa using GlobalsSyntax.cons (array_sound a guard.1) (ih guard.2)

def copyrightBody : String :=
  "\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n"

def counterPrelude : String := "/*"++copyrightBody++"*/\n#include <stdint.h>\n\n"
def driverPrelude : String :=
  "/*"++copyrightBody++"*/\n#include <stdint.h>\n#include <stdio.h>\n\n"

theorem counter_prelude : Prelude counterPrelude false :=
  Prelude.counter (by
    constructor
    · decide +kernel
    · rw [String.contains_string_eq_internal]; decide +kernel)
theorem driver_prelude : Prelude driverPrelude true :=
  Prelude.driver (by
    constructor
    · decide +kernel
    · rw [String.contains_string_eq_internal]; decide +kernel)

def counterRender (fs : List Function) : Option String := do
  return counterPrelude++(←renderFunctions fs)

theorem counter_render_sound {fs : List Function} {source : String}
    (printed : counterRender fs = some source) (guard : fs.all functionGuard = true)
    (nonempty : fs ≠ []) : CounterProgram source fs := by
  cases hp : renderFunctions fs with
  | none => simp [counterRender,hp] at printed
  | some text =>
    have he : counterPrelude++text = source := by simpa [counterRender,hp] using printed
    subst source
    exact CounterProgram.translationUnit counter_prelude (functions_sound hp guard) nonempty

def driverGuard (u : TranslationUnit) : Bool := prototypeGuard u.prototype &&
  u.globals.all arrayGuard && functionGuard u.main && decide (u.main.returnType = "int") &&
  decide (u.main.name = "main") && decide (u.main.parameters = [])

theorem driver_render_sound {u : TranslationUnit} {source : String}
    (printed : render u = some source) (guard : driverGuard u = true) :
    DriverProgram source u := by
  simp only [driverGuard,Bool.and_eq_true,decide_eq_true_eq] at guard
  cases hp : renderFunction u.main with
  | none => simp [render,hp] at printed
  | some text =>
    have he : driverPrelude++renderPrototype u.prototype++
        String.join (u.globals.map renderArray)++"\n"++text = source := by
      simpa [render,driverPrelude,copyrightBody,hp] using printed
    subst source
    exact DriverProgram.translationUnit driver_prelude
      (prototype_sound u.prototype guard.1.1.1.1.1)
      (globals_sound guard.1.1.1.1.2) (function_sound hp guard.1.1.1.2)
      guard.1.1.2 guard.1.2 guard.2

/-- Strict byte-and-profile acceptance supplements the original token checker.
The independent target grammar was specified before this check and never refers
back to acceptance or rendering. Original numerical source bytes are preserved. -/
def checkedCounter (source : String) (fs : List Function) : Bool :=
  (!fs.isEmpty) && fs.all functionGuard && decide (counterRender fs = some source)
def checkedDriver (source : String) (u : TranslationUnit) : Bool :=
  driverGuard u && decide (render u = some source)

theorem checkedCounter_sound {source fs} (accepted : checkedCounter source fs = true) :
    CounterProgram source fs := by
  simp only [checkedCounter,Bool.and_eq_true,decide_eq_true_eq] at accepted
  apply counter_render_sound accepted.2 accepted.1.2
  intro h
  subst fs
  simp at accepted

theorem checkedDriver_sound {source u} (accepted : checkedDriver source u = true) :
    DriverProgram source u := by
  simp only [checkedDriver,Bool.and_eq_true,decide_eq_true_eq] at accepted
  exact driver_render_sound accepted.2 accepted.1

#print axioms expression_sound
#print axioms statement_sound
#print axioms function_sound
#print axioms prototype_sound
#print axioms array_sound
#print axioms globals_sound
#print axioms counter_render_sound
#print axioms driver_render_sound
#print axioms checkedCounter_sound
#print axioms checkedDriver_sound
end RHOcticPush.CounterSyntax

import GoldbachDirect.SourceLocalOnly

set_option autoImplicit false

namespace GoldbachDirect.SourceNoAlloc
open Semantics SourceLocals

/-- A checked syntactic fragment with pure expressions and no births or calls.
Indirect scalar/array stores are allowed; no claim about their numerical data
or their target being private occurs in this predicate. -/
def Only : Stmt → Prop
  | .block body => ∀ statement ∈ body, Only statement
  | .assign destination expression => SourcePure.CallFree destination ∧ SourcePure.CallFree expression
  | .expression expression => SourcePure.CallFree expression
  | .ite condition yes no => SourcePure.CallFree condition ∧ Only yes ∧ ∀ statement ∈ no, Only statement
  | .whileLoop condition body => SourcePure.CallFree condition ∧ Only body
  | .returnValue none | .breakLoop | .continueLoop | .label _ | .gotoLabel _ => True
  | .returnValue (some expression) => SourcePure.CallFree expression
  | _ => False

structure Effect {F : Type} (before after : State F) : Prop where
  well : WellScoped after
  environment : after.environment=before.environment
  scope : after.scope=before.scope
  nextObject : after.nextObject=before.nextObject
  nextScope : before.nextScope≤after.nextScope
  mode : after.mode=before.mode
  foreign : after.foreign=before.foreign

theorem Effect.refl {F : Type} {state : State F} (well : WellScoped state) : Effect state state :=
  ⟨well,rfl,rfl,rfl,le_refl _,rfl,rfl⟩

theorem Effect.trans {F : Type} {a b c : State F} (first : Effect a b) (second : Effect b c) : Effect a c :=
  ⟨second.well,second.environment.trans first.environment,second.scope.trans first.scope,
    second.nextObject.trans first.nextObject,first.nextScope.trans second.nextScope,
    second.mode.trans first.mode,second.foreign.trans first.foreign⟩

theorem store_effect {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (well : WellScoped before) (written : before.store pointer value=some after) : Effect before after := by
  obtain ⟨environment,mode,scope,nextScope,nextObject,_⟩ := store_frame written
  exact ⟨wellScoped_store well written,environment,scope,nextObject,by rw [nextScope],mode,store_foreign written⟩

theorem close_effect {F : Type} {before middle : State F} (well : WellScoped before)
    (body : Effect before.enterScope middle) :
    Effect before {middle.leaveScope before.nextScope before.environment with scope:=before.scope} := by
  have scopes : before.nextScope+1≤middle.nextScope := body.nextScope
  have current := well.current
  exact ⟨wellScoped_scope (wellScoped_leave body.well _ _) (by change before.scope<middle.nextScope; omega),rfl,rfl,
    body.nextObject,by change before.nextScope≤middle.nextScope; omega,body.mode,body.foreign⟩

theorem exec_effect {F : Type} {context : Context F} {before after : State F} {statement : Stmt} {flow : Flow}
    (run : Exec context before statement flow after) : Only statement → WellScoped before → Effect before after := by
  apply Exec.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun before statement _ after _ => Only statement → WellScoped before → Effect before after)
    (motive_6 := fun before statements _ after _ =>
      (∀ statement ∈ statements,Only statement) → WellScoped before → Effect before after)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True) (t:=run)
  all_goals try solve | intros; trivial
  case block =>
    intro start body flow middle after before entered bodyRun finished ih only well
    simp only [Only] at only
    subst_vars
    exact close_effect well (ih only (wellScoped_enter well))
  case declareNone => intros; simp_all only [Only]
  case declareSome => intros; simp_all only [Only]
  case assign =>
    intro before expression value middle destination pointer assigned after right left written _ _ only well
    simp only [Only] at only
    have same := SourcePure.eval_state right only.2
    have assignedSame := SourcePure.place_state left only.1
    subst_vars
    exact store_effect well written
  case assignOp => intros; simp_all only [Only]
  case expression =>
    intro before expression value after evaluated _ only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only
    subst_vars
    exact Effect.refl well
  case callTerminated => intros; simp_all only [Only,SourcePure.CallFree]
  case ifTrue =>
    intro before condition value middle yes flow after no evaluated truth body _ ih only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact ih only.2.1 well
  case ifFalse =>
    intro before condition value after yes evaluated truth _ only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact Effect.refl well
  case ifElse =>
    intro before condition value middle no flow after yes evaluated truth body _ ih only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact ih (only.2.2 no (by simp)) well
  case whileFalse =>
    intro before condition value after body evaluated truth _ only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact Effect.refl well
  case whileNext =>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    have first := bodyIH only.2 well
    exact first.trans (restIH (by simpa only [Only] using only) first.well)
  case whileContinue =>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    have first := bodyIH only.2 well
    exact first.trans (restIH (by simpa only [Only] using only) first.well)
  case whileBreak =>
    intro before condition value tested body after evaluated truth bodyRun _ bodyIH only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact bodyIH only.2 well
  case whileExit =>
    intro before condition value tested body flow after evaluated truth bodyRun abrupt _ bodyIH only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact bodyIH only.2 well
  case returnSome =>
    intro before expression value after evaluated _ only well
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only
    subst_vars
    exact Effect.refl well
  case launch => intros; simp_all only [Only]
  all_goals first
    | (intro state only well; exact Effect.refl well)
    | (intro state name only well; exact Effect.refl well)
    | (intro before statement middle statements flow after first rest firstIH restIH only well
       have head := firstIH (only statement (by simp)) well
       exact head.trans (restIH (fun statement member=>only statement (by simp [member])) head.well))
    | (intro before statement flow after statements first abrupt firstIH only well
       exact firstIH (only statement (by simp)) well)

end GoldbachDirect.SourceNoAlloc

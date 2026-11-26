import GoldbachDirect.SourceBindings

set_option autoImplicit false

namespace GoldbachDirect.SourceLocalOnly
open Semantics SourceLocals

/-- Syntactic source fragment with no calls and no indirect stores. Every
assignment targets an addressable local name, while reads may use caller data. -/
def Only : Stmt → Prop
  | .block body => ∀ statement ∈ body, Only statement
  | .declare _ _ none => True
  | .declare _ _ (some expression) => SourcePure.CallFree expression
  | .assign (.variable _) expression => SourcePure.CallFree expression
  | .expression expression => SourcePure.CallFree expression
  | .ite condition yes no => SourcePure.CallFree condition ∧ Only yes ∧ ∀ statement ∈ no, Only statement
  | .whileLoop condition body => SourcePure.CallFree condition ∧ Only body
  | .returnValue none | .breakLoop | .continueLoop | .label _ | .gotoLabel _ => True
  | .returnValue (some expression) => SourcePure.CallFree expression
  | _ => False

structure Fresh {F : Type} (cutoff : Nat) (state : State F) : Prop where
  well : WellScoped state
  next : cutoff ≤ state.nextObject
  names : ∀ name pointer, state.environment.lookup name = some pointer → cutoff ≤ pointer.object

structure Effect {F : Type} (cutoff : Nat) (before after : State F) : Prop where
  fresh : Fresh cutoff after
  scope : after.scope = before.scope
  nextObject : before.nextObject ≤ after.nextObject
  nextScope : before.nextScope ≤ after.nextScope
  mode : after.mode = before.mode
  foreign : after.foreign = before.foreign
  old : ∀ id, id < cutoff → after.objects id = before.objects id

theorem Effect.refl {F : Type} {cutoff : Nat} {state : State F} (fresh : Fresh cutoff state) :
    Effect cutoff state state := ⟨fresh,rfl,le_refl _,le_refl _,rfl,rfl,fun _ _ => rfl⟩

theorem Effect.trans {F : Type} {cutoff : Nat} {a b c : State F}
    (first : Effect cutoff a b) (second : Effect cutoff b c) : Effect cutoff a c :=
  ⟨second.fresh,second.scope.trans first.scope,first.nextObject.trans second.nextObject,
    first.nextScope.trans second.nextScope,second.mode.trans first.mode,
    second.foreign.trans first.foreign,fun id old => (second.old id old).trans (first.old id old)⟩

theorem Fresh.enter {F : Type} {cutoff : Nat} {state : State F} (fresh : Fresh cutoff state) :
    Fresh cutoff state.enterScope := ⟨wellScoped_enter fresh.well,fresh.next,fresh.names⟩

theorem declare_effect {F : Type} {cutoff : Nat} {before after : State F} {type : CType}
    {name : String} {value : Option Value} (fresh : Fresh cutoff before)
    (declared : before.declare type name value = some after) : Effect cutoff before after := by
  have freshNext := fresh.next
  obtain ⟨scope,nextScope,nextObject,mode,outside⟩ := declare_frame declared
  have environment := declare_environment declared
  refine ⟨⟨wellScoped_declare fresh.well declared,by omega,?_⟩,scope,by omega,by omega,mode,declare_foreign declared,?_⟩
  · intro key pointer present
    rw [environment] at present
    by_cases same : key=name
    · subst key
      simp [List.lookup] at present
      cases present
      exact fresh.next
    · have old : before.environment.lookup key = some pointer := by simpa [List.lookup,show (key == name) = false from by simp [same]] using present
      exact fresh.names key pointer old
  · intro id old
    exact outside id (by omega)

theorem store_effect {F : Type} {cutoff : Nat} {before after : State F}
    {pointer : Pointer} {value : Value} (fresh : Fresh cutoff before) (localBound : cutoff ≤ pointer.object)
    (written : before.store pointer value = some after) : Effect cutoff before after := by
  have freshNext := fresh.next
  obtain ⟨environment,mode,scope,nextScope,nextObject,outside⟩ := store_frame written
  refine ⟨⟨wellScoped_store fresh.well written,by simpa [nextObject] using fresh.next,?_⟩,
    scope,by omega,by omega,mode,store_foreign written,?_⟩
  · intro name pointer present
    rw [environment] at present
    exact fresh.names name pointer present
  · intro id old
    exact outside id (by omega)

theorem block_effect {F : Type} {cutoff : Nat} {before middle : State F}
    (fresh : Fresh cutoff before) (body : Effect cutoff before.enterScope middle) :
    Effect cutoff before {middle.leaveScope before.nextScope before.environment with scope:=before.scope} := by
  have scopes : before.nextScope+1 ≤ middle.nextScope := body.nextScope
  have current := fresh.well.current
  have bound : before.scope < middle.nextScope := by omega
  have closedWell := wellScoped_scope
    (wellScoped_leave body.fresh.well before.nextScope before.environment) bound
  refine ⟨⟨closedWell,body.fresh.next,fresh.names⟩,
    rfl,body.nextObject,by change before.nextScope ≤ middle.nextScope; omega,body.mode,body.foreign,?_⟩
  intro id old
  change ((middle.objects id).map _) = _
  have same : middle.objects id = before.objects id := body.old id old
  rw [same]
  cases present : before.objects id with
  | none => rfl
  | some object =>
    have different : object.storage ≠ .automatic before.nextScope := by
      intro same
      have := fresh.well.automatic id object before.nextScope present same
      omega
    simp [different]

/-- Operational frame for the entire local-only source fragment, including
nested scopes and arbitrary finite while executions. The cutoff comes from
actual fresh local births, not a supplied application representation. -/
theorem exec_effect {F : Type} {context : Context F} {cutoff : Nat} {before after : State F}
    {statement : Stmt} {flow : Flow} (run : Exec context before statement flow after) :
    Only statement → Fresh cutoff before → Effect cutoff before after := by
  apply Exec.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun before statement _ after _ => Only statement → Fresh cutoff before → Effect cutoff before after)
    (motive_6 := fun before statements _ after _ =>
      (∀ statement ∈ statements, Only statement) → Fresh cutoff before → Effect cutoff before after)
    (motive_7 := fun _ _ _ _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True) (t := run)
  all_goals try solve | intros; trivial
  case block =>
    intro start body flow middle after before entered bodyRun finished ih only fresh
    simp only [Only] at only
    subst_vars
    exact block_effect fresh (ih only fresh.enter)
  case declareNone =>
    intro after before type name declared only fresh
    simp only [Only] at only
    exact declare_effect fresh declared
  case declareSome =>
    intro before expression value middle type name after evaluated declared _ only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only
    subst_vars
    exact declare_effect fresh declared
  case assign =>
    intro before expression value middle destination pointer assigned after right left written _ _ only fresh
    cases destination <;> simp only [Only] at only
    rename_i name
    have same := SourcePure.eval_state right only
    subst_vars
    cases left with
    | «variable» present => exact store_effect fresh (fresh.names name pointer present) written
  case assignOp =>
    intros
    simp_all only [Only,SourcePure.CallFree]
  case expression =>
    intro before expression value after evaluated _ only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only
    subst_vars
    exact Effect.refl fresh
  case callTerminated =>
    intros
    simp_all only [Only,SourcePure.CallFree]
  case ifTrue =>
    intro before condition value middle yes flow after no evaluated truth body _ ih only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact ih only.2.1 fresh
  case ifFalse =>
    intro before condition value after yes evaluated truth _ only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact Effect.refl fresh
  case ifElse =>
    intro before condition value middle no flow after yes evaluated truth body _ ih only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact ih (only.2.2 no (by simp)) fresh
  case whileFalse =>
    intro before condition value after body evaluated truth _ only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact Effect.refl fresh
  case whileNext =>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    have first := bodyIH only.2 fresh
    exact first.trans (restIH (by simpa only [Only] using only) first.fresh)
  case whileContinue =>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    have first := bodyIH only.2 fresh
    exact first.trans (restIH (by simpa only [Only] using only) first.fresh)
  case whileBreak =>
    intro before condition value tested body after evaluated truth bodyRun _ bodyIH only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact bodyIH only.2 fresh
  case whileExit =>
    intro before condition value tested body flow after evaluated truth bodyRun abrupt _ bodyIH only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only.1
    subst_vars
    exact bodyIH only.2 fresh
  case returnNone =>
    intro state only fresh
    simp only [Only] at only
    exact Effect.refl fresh
  case returnSome =>
    intro before expression value after evaluated _ only fresh
    simp only [Only] at only
    have same := SourcePure.eval_state evaluated only
    subst_vars
    exact Effect.refl fresh
  case breakLoop =>
    intro state only fresh
    simp only [Only] at only
    exact Effect.refl fresh
  case continueLoop =>
    intro state only fresh
    simp only [Only] at only
    exact Effect.refl fresh
  case label =>
    intro state name only fresh
    simp only [Only] at only
    exact Effect.refl fresh
  case gotoLabel =>
    intro state name only fresh
    simp only [Only] at only
    exact Effect.refl fresh
  case launch =>
    intros
    simp_all only [Only,SourcePure.CallFree]
  all_goals first
    | (intro state only fresh; exact Effect.refl fresh)
    | (intro before statement middle statements flow after first rest firstIH restIH only fresh
       exact (firstIH (only statement (by simp)) fresh).trans
         (restIH (fun statement member => only statement (by simp [member]))
           (firstIH (only statement (by simp)) fresh).fresh))
    | (intro before statement flow after statements first abrupt firstIH only fresh
       exact firstIH (only statement (by simp)) fresh)

theorem list_effect {F : Type} {context : Context F} {cutoff : Nat} {before after : State F}
    {statements : List Stmt} {flow : Flow}
    (run : ExecList context before statements flow after)
    (only : ∀ statement ∈ statements, Only statement) (fresh : Fresh cutoff before) :
    Effect cutoff before after := by
  induction statements generalizing before after flow with
  | nil => cases run; exact Effect.refl fresh
  | cons statement statements ih =>
    cases run with
    | cons first rest =>
      have head := exec_effect first (only statement (by simp)) fresh
      exact head.trans (ih rest (fun statement member => only statement (by simp [member])) head.fresh)
    | abrupt first abrupt => exact exec_effect first (only statement (by simp)) fresh

theorem list_wellScoped {F : Type} {context : Context F} {before after : State F}
    {statements : List Stmt} {flow : Flow} (run : ExecList context before statements flow after)
    (only : ∀ statement ∈ statements, Only statement) (well : WellScoped before) : WellScoped after :=
  (list_effect run only ⟨well,Nat.zero_le _,fun _ _ _ => Nat.zero_le _⟩).fresh.well

end GoldbachDirect.SourceLocalOnly

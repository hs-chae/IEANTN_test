import GoldbachDirect.SourceNoAlloc

set_option autoImplicit false

namespace GoldbachDirect.SourceArrayFrame
open Semantics SourceLocals ScanFrame

structure ArrayBinding where
  name : String
  cell : Pointer
  base : Pointer

def writes (locals : List (String×Pointer)) (arrays : List ArrayBinding) : List Nat :=
  locals.map (fun item=>item.2.object) ++ arrays.map (fun item=>item.base.object)

/-- Actual source name/address associations. The array pointer cells themselves
are outside the set of writes; no table contents or postcondition occurs here. -/
structure Bindings {F : Type} (state : State F) (locals : List (String×Pointer))
    (arrays : List ArrayBinding) : Prop where
  named : ∀ name pointer,(name,pointer)∈locals → state.environment.lookup name=some pointer
  arrayValues : ∀ item∈arrays,state.environment.lookup item.name=some item.cell ∧
    state.load item.cell=some (.pointer item.base)
  protectedCells : ∀ item∈arrays,item.cell.object∉writes locals arrays

theorem Bindings.enter {F : Type} {state : State F} {locals : List (String×Pointer)} {arrays : List ArrayBinding}
    (bindings : Bindings state locals arrays) : Bindings state.enterScope locals arrays :=
  ⟨bindings.named,bindings.arrayValues,bindings.protectedCells⟩

theorem Bindings.frame {F : Type} {before after : State F}
    {locals : List (String×Pointer)} {arrays : List ArrayBinding}
    (bindings : Bindings before locals arrays) (effect : Frame before after (writes locals arrays)) :
    Bindings after locals arrays := by
  refine ⟨?_,?_,bindings.protectedCells⟩
  · intro name pointer member
    rw [effect.environment]
    exact bindings.named name pointer member
  · intro item member
    obtain ⟨name,read⟩ := bindings.arrayValues item member
    refine ⟨by rw [effect.environment]; exact name,?_⟩
    have same : after.load item.cell=before.load item.cell := by
      unfold State.load
      rw [effect.outside item.cell.object (bindings.protectedCells item member)]
      simp only [State.accessible,effect.mode]
      rfl
    exact same.trans read

def Writable (locals : List (String×Pointer)) (arrays : List ArrayBinding) : Expr → Prop
  | .variable name => ∃ pointer,(name,pointer)∈locals
  | .index (.variable name) _ | .unary .dereference (.variable name) =>
      ∃ item∈arrays,item.name=name
  | _=>False

def Only (locals : List (String×Pointer)) (arrays : List ArrayBinding) : Stmt → Prop
  | .block body => ∀ statement∈body,Only locals arrays statement
  | .assign destination _=>Writable locals arrays destination
  | .expression _ | .returnValue _ | .breakLoop | .continueLoop | .label _ | .gotoLabel _=>True
  | .ite _ yes no=>Only locals arrays yes ∧ ∀ statement∈no,Only locals arrays statement
  | .whileLoop _ body=>Only locals arrays body
  | _=>False

theorem pointer_add_object {F : Type} {state : State F} {before after : Pointer} {offset : Int}
    (added : state.pointerAdd before offset=some after) : after.object=before.object := by
  cases width : before.element.byteSize with
  | none=>simp [State.pointerAdd,width] at added
  | some width=>
      simp [State.pointerAdd,width] at added
      exact (congrArg Pointer.object added.2.2).symm

theorem place_member {F : Type} {context : Context F} {before after : State F}
    {destination : Expr} {pointer : Pointer} {locals : List (String×Pointer)} {arrays : List ArrayBinding}
    (bindings : Bindings before locals arrays) (writable : Writable locals arrays destination)
    (closed : SourcePure.CallFree destination) (run : Place context before destination pointer after) :
    pointer.object∈writes locals arrays := by
  cases destination with
  | «variable» name=>
      obtain ⟨expected,member⟩ := writable
      cases run with
      | «variable» present=>
          have same := Option.some.inj (present.symm.trans (bindings.named name expected member))
          cases same
          exact List.mem_append_left _ (List.mem_map.mpr ⟨_,member,rfl⟩)
  | index base index=>
      cases base <;> simp only [Writable] at writable
      rename_i name
      obtain ⟨item,member,sameName⟩ := writable
      cases run with
      | index baseRun indexRun added=>
          have actual := (PureEval.eval_sound baseRun (by trivial)).2
          obtain ⟨named,read⟩ := bindings.arrayValues item member
          have computed : PureEval.eval context before (.variable name)=some (.pointer item.base) := by
            simp [PureEval.eval,←sameName,named,read]
          have same := Option.some.inj (actual.symm.trans computed)
          cases same
          rw [pointer_add_object added]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨item,member,rfl⟩)
  | unary op expression=>
      cases op <;> cases expression <;> simp only [Writable] at writable
      rename_i name
      obtain ⟨item,member,sameName⟩ := writable
      cases run with
      | dereference evaluated=>
          have actual := (PureEval.eval_sound evaluated (by trivial)).2
          obtain ⟨named,read⟩ := bindings.arrayValues item member
          have computed : PureEval.eval context before (.variable name)=some (.pointer item.base) := by
            simp [PureEval.eval,←sameName,named,read]
          have same := Option.some.inj (actual.symm.trans computed)
          cases same
          exact List.mem_append_right _ (List.mem_map.mpr ⟨item,member,rfl⟩)
  | literal value=>exact False.elim writable
  | paren value=>exact False.elim writable
  | cast type value=>exact False.elim writable
  | binary op left right=>exact False.elim writable
  | member base name pointer=>exact False.elim writable
  | call name args=>exact False.elim writable
  | conditional test yes no=>exact False.elim writable

theorem exec_frame {F : Type} {context : Context F} {before after : State F} {statement : Stmt} {flow : Flow}
    {locals : List (String×Pointer)} {arrays : List ArrayBinding}
    (run : Exec context before statement flow after) :
    Only locals arrays statement → SourceNoAlloc.Only statement → WellScoped before →
      Bindings before locals arrays → Frame before after (writes locals arrays) := by
  apply Exec.rec
    (motive_1:=fun _ _ _ _ _=>True) (motive_2:=fun _ _ _ _ _=>True)
    (motive_3:=fun _ _ _ _ _=>True) (motive_4:=fun _ _ _ _ _=>True)
    (motive_5:=fun before statement _ after _=>Only locals arrays statement → SourceNoAlloc.Only statement →
      WellScoped before → Bindings before locals arrays → Frame before after (writes locals arrays))
    (motive_6:=fun before statements _ after _=>(∀statement∈statements,Only locals arrays statement) →
      (∀statement∈statements,SourceNoAlloc.Only statement) → WellScoped before →
      Bindings before locals arrays → Frame before after (writes locals arrays))
    (motive_7:=fun _ _ _ _ _ _=>True) (motive_8:=fun _ _ _ _ _ _=>True) (t:=run)
  all_goals try solve | intros; trivial
  case block=>
    intro start body flow middle after before entered bodyRun finished ih only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    subst_vars
    exact Frame.close well (ih only closed (wellScoped_enter well) bindings.enter)
  case declareNone=>intros; simp_all only [Only]
  case declareSome=>intros; simp_all only [Only]
  case assign=>
    intro before expression value middle destination pointer assigned after right left written _ _ only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state right closed.2
    have assignedSame := SourcePure.place_state left closed.1
    subst_vars
    exact Frame.store (place_member bindings only closed.1 left) written
  case assignOp=>intros; simp_all only [Only]
  case expression=>
    intro before expression value after evaluated _ only closed well bindings
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed
    subst_vars
    exact Frame.refl _ _
  case callTerminated=>intros; simp_all only [Only,SourceNoAlloc.Only,SourcePure.CallFree]
  case ifTrue=>
    intro before condition value middle yes flow after no evaluated truth body _ ih only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact ih only.1 closed.2.1 well bindings
  case ifFalse=>
    intro before condition value after yes evaluated truth _ only closed well bindings
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact Frame.refl _ _
  case ifElse=>
    intro before condition value middle no flow after yes evaluated truth body _ ih only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact ih (only.2 no (by simp)) (closed.2.2 no (by simp)) well bindings
  case whileFalse=>
    intro before condition value after body evaluated truth _ only closed well bindings
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact Frame.refl _ _
  case whileNext=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    have first := bodyIH only closed.2 well bindings
    exact first.trans (restIH (by simpa only [Only] using only) (by simpa only [SourceNoAlloc.Only] using closed)
      (SourceNoAlloc.exec_effect bodyRun closed.2 well).well (bindings.frame first))
  case whileContinue=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    have first := bodyIH only closed.2 well bindings
    exact first.trans (restIH (by simpa only [Only] using only) (by simpa only [SourceNoAlloc.Only] using closed)
      (SourceNoAlloc.exec_effect bodyRun closed.2 well).well (bindings.frame first))
  case whileBreak=>
    intro before condition value tested body after evaluated truth bodyRun _ bodyIH only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact bodyIH only closed.2 well bindings
  case whileExit=>
    intro before condition value tested body flow after evaluated truth bodyRun abrupt _ bodyIH only closed well bindings
    simp only [Only] at only
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed.1
    subst_vars
    exact bodyIH only closed.2 well bindings
  case returnSome=>
    intro before expression value after evaluated _ only closed well bindings
    simp only [SourceNoAlloc.Only] at closed
    have same := SourcePure.eval_state evaluated closed
    subst_vars
    exact Frame.refl _ _
  case launch=>intros; simp_all only [Only]
  all_goals first
    | (intros; exact Frame.refl _ _)
    | (intro before statement middle statements flow after first rest firstIH restIH only closed well bindings
       have head := firstIH (only statement (by simp)) (closed statement (by simp)) well bindings
       exact head.trans (restIH (fun statement member=>only statement (by simp [member]))
         (fun statement member=>closed statement (by simp [member]))
         (SourceNoAlloc.exec_effect first (closed statement (by simp)) well).well (bindings.frame head)))
    | (intro before statement flow after statements first abrupt firstIH only closed well bindings
       exact firstIH (only statement (by simp)) (closed statement (by simp)) well bindings)

end GoldbachDirect.SourceArrayFrame

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CompareSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem binary64_lt (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .lt (integer64 a) (integer64 b)=some (.boolean (decide (a<b))) := by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt<(Integer.cast .u64 (b:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

theorem binary64_gt (a b : Nat) (ha : a<2^64) (hb : b<2^64) :
    Integer.binary .gt (integer64 a) (integer64 b)=some (.boolean (decide (b<a))) := by
  change some (Integer.boolean ((Integer.cast .u64 (b:Int)).toInt<(Integer.cast .u64 (a:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  congr 2
  simp

section ViewEvaluation
variable {F : Type} (context : Context F) {state : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View state ao al ast bo bl bst owner li a b j)
include h

theorem condition_eval : Eval context state condition
    (.integer (.boolean (decide (0<j)))) state := by
  exact .binaryLR (.variable (h.locals.lookup Var.j) (h.locals.read Var.j))
    (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (by simp only [values,binary,binary64_gt j 0 (by have hj:=h.active; omega) (by norm_num),Option.map_some])

theorem left_eval (hj : j<5) : Eval context state (index .a)
    (.integer (integer64 (a (ast+j)))) state := by
  have hi : ast+j<al := by have hb:=h.leftBound; omega
  exact .load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
    (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) (slice_pointer_add h.left hi))
    (word_load h.left hi)

theorem right_eval (hj : j<5) : Eval context state (index .b)
    (.integer (integer64 (b (bst+j)))) state := by
  have hi : bst+j<bl := by have hb:=h.rightBound; omega
  exact .load (.index (.variable (h.locals.lookup Var.b) (h.locals.read Var.b))
    (.variable (h.locals.lookup Var.j) (h.locals.read Var.j)) (slice_pointer_add h.right hi))
    (word_load h.right hi)

theorem gt_eval (hj : j<5) : Eval context state (comparison .gt)
    (.integer (.boolean (decide (b (bst+j)<a (ast+j))))) state := by
  have ha64 := h.left.2.2 (ast+j) (by have hb:=h.leftBound; omega)
  have hb64 := h.right.2.2 (bst+j) (by have hb:=h.rightBound; omega)
  exact .binaryLR (left_eval context h hj) (right_eval context h hj)
    (by simp only [binary,binary64_gt _ _ ha64 hb64,Option.map_some])

theorem lt_eval (hj : j<5) : Eval context state (comparison .lt)
    (.integer (.boolean (decide (a (ast+j)<b (bst+j))))) state := by
  have ha64 := h.left.2.2 (ast+j) (by have hb:=h.leftBound; omega)
  have hb64 := h.right.2.2 (bst+j) (by have hb:=h.rightBound; omega)
  exact .binaryLR (left_eval context h hj) (right_eval context h hj)
    (by simp only [binary,binary64_lt _ _ ha64 hb64,Option.map_some])
end ViewEvaluation

private theorem wordArray_leave {F : Type} {state : State F} {object size scope restore : Nat}
    {environment : List (String×Pointer)} {data : Nat → Nat}
    (h : WordArrayRep state object size data) :
    WordArrayRep {state.leaveScope scope environment with scope:=restore} object size data := by
  refine ⟨h.1,?_,h.2.2⟩
  change (state.objects object).map _=some (wordObject size data)
  rw [h.2.1]
  simp [wordObject]

theorem close_view {F : Type} {context : Context F} {before middle : State F}
    {ao al ast bo bl bst owner j k : Nat} {li : Var → Nat} {a b : Nat → Nat}
    {body : List Stmt} {flow : Flow}
    (h : View before ao al ast bo bl bst owner li a b j)
    (hm : View middle ao al ast bo bl bst owner li a b k)
    (run : ExecList context before.enterScope body flow middle)
    (only : SourceNoAlloc.Only (.block body)) :
    View {middle.leaveScope before.nextScope before.environment with scope:=before.scope}
      ao al ast bo bl bst owner li a b k := by
  have blockRun : Exec context before (.block body) flow
      {middle.leaveScope before.nextScope before.environment with scope:=before.scope} :=
    .block (by rfl) run (by rfl)
  have effect := SourceNoAlloc.exec_effect blockRun only h.well
  have different : before.nextScope≠owner := by have ho:=h.locals.bound; omega
  exact ⟨wordArray_leave hm.left,wordArray_leave hm.right,
    hm.locals.leave different before.environment h.locals.lookup before.scope,
    hm.separate,hm.leftBound,hm.rightBound,hm.active,effect.well⟩

theorem return_block {F : Type} (context : Context F) {before : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View before ao al ast bo bl bst owner li a b j) (n : Nat) (hn : n≤2) :
    ∃after,Exec context before (.block [returnStmt n]) (.returned (.integer (integer64 n))) after ∧
      View after ao al ast bo bl bst owner li a b j := by
  have run : ExecList context before.enterScope [returnStmt n] (.returned (.integer (integer64 n))) before.enterScope :=
    .abrupt (.returnSome (.literal (.integer n "ULL") _ (.integer (integer64 n)) (by interval_cases n <;> rfl))) (by intro h; cases h)
  refine ⟨{before.enterScope.leaveScope before.nextScope before.environment with scope:=before.scope},
    .block (by rfl) run (by rfl),?_⟩
  exact close_view h h.enter run (by simp [returnStmt,SourceNoAlloc.Only,SourcePure.CallFree])

def stepFlow (a b : Nat → Nat) (j : Nat) : Flow :=
  if b j<a j then .returned (.integer (integer64 2))
  else if a j<b j then .returned (.integer (integer64 0)) else .normal

/-- Full actual source loop body, including decrement, ordered comparisons,
branch short-circuiting, returned values and all nested scope exits. -/
theorem loop_body_execution {F : Type} (context : Context F) {before : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View before ao al ast bo bl bst owner li a b (j+1)) :
    ∃after,Exec context before loopBody (stepFlow (fun i=>a (ast+i)) (fun i=>b (bst+i)) j) after ∧
      View after ao al ast bo bl bst owner li a b j := by
  obtain ⟨middle,dec,hm⟩ := decrement_execution context h.enter
  have hj : j<5 := by have hh:=h.active; omega
  have noalloc : SourceNoAlloc.Only loopBody := by
    simp [loopBody,decrement,branch,comparison,index,returnStmt,SourceNoAlloc.Only,SourcePure.CallFree]
  by_cases hgt : b (bst+j)<a (ast+j)
  · obtain ⟨last,returned,hlast⟩ := return_block context hm 2 (by norm_num)
    have run : ExecList context before.enterScope [decrement,branch .gt 2,branch .lt 0]
        (.returned (.integer (integer64 2))) last :=
      .cons dec (.abrupt (.ifTrue (gt_eval context hm hj)
        (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hgt]) returned)
        (by intro h; cases h))
    refine ⟨{last.leaveScope before.nextScope before.environment with scope:=before.scope},?_,close_view h hlast run noalloc⟩
    simpa only [loopBody,stepFlow,if_pos hgt] using (Exec.block (by rfl) run (by rfl))
  · have first : Exec context middle (branch .gt 2) .normal middle :=
      .ifFalse (gt_eval context hm hj) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hgt])
    by_cases hlt : a (ast+j)<b (bst+j)
    · obtain ⟨last,returned,hlast⟩ := return_block context hm 0 (by norm_num)
      have run : ExecList context before.enterScope [decrement,branch .gt 2,branch .lt 0]
          (.returned (.integer (integer64 0))) last :=
        .cons dec (.cons first (.abrupt (.ifTrue (lt_eval context hm hj)
          (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hlt]) returned)
          (by intro h; cases h)))
      refine ⟨{last.leaveScope before.nextScope before.environment with scope:=before.scope},?_,close_view h hlast run noalloc⟩
      simpa only [loopBody,stepFlow,if_neg hgt,if_pos hlt] using (Exec.block (by rfl) run (by rfl))
    · have second : Exec context middle (branch .lt 0) .normal middle :=
        .ifFalse (lt_eval context hm hj) (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hlt])
      have run : ExecList context before.enterScope [decrement,branch .gt 2,branch .lt 0] .normal middle :=
        .cons dec (.cons first (.cons second .nil))
      refine ⟨{middle.leaveScope before.nextScope before.environment with scope:=before.scope},?_,close_view h hm run noalloc⟩
      simpa only [loopBody,stepFlow,if_neg hgt,if_neg hlt] using (Exec.block (by rfl) run (by rfl))

/-- Early source returns preserve their actual ordering; equality means the
while loop exits normally and the enclosing function returns one. -/
def comparedFlow (a b : Nat → Nat) : Nat → Flow
  | 0 => .normal
  | j+1 => if b j<a j then .returned (.integer (integer64 2))
      else if a j<b j then .returned (.integer (integer64 0)) else comparedFlow a b j

theorem comparedFlow_eq (a b : Nat → Nat) (j : Nat) :
    comparedFlow a b j = if FFT.Limbs.compareDigits a b j=1 then .normal
      else .returned (.integer (integer64 (FFT.Limbs.compareDigits a b j))) := by
  induction j with
  | zero => simp [comparedFlow,FFT.Limbs.compareDigits]
  | succ j ih =>
    by_cases hg : b j<a j
    · simp [comparedFlow,FFT.Limbs.compareDigits,hg]
    · by_cases hl : a j<b j
      · simp [comparedFlow,FFT.Limbs.compareDigits,hg,hl]
      · simpa only [comparedFlow,FFT.Limbs.compareDigits,if_neg hg,if_neg hl] using ih

/-- Every actual loop iteration is proved, including early returns. No array
word changes and no successful-effects or output premise is supplied. -/
theorem loop_execution {F : Type} (context : Context F) (j : Nat) {before : State F}
    {ao al ast bo bl bst owner : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View before ao al ast bo bl bst owner li a b j) :
    ∃after k,Exec context before loop (comparedFlow (fun i=>a (ast+i)) (fun i=>b (bst+i)) j) after ∧
      View after ao al ast bo bl bst owner li a b k := by
  induction j generalizing before with
  | zero =>
    refine ⟨before,0,?_,h⟩
    exact .whileFalse (condition_eval context h)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed])
  | succ j ih =>
    obtain ⟨middle,first,hm⟩ := loop_body_execution context h
    have hcond := condition_eval context h
    have htrue : (Value.integer (.boolean (decide (0<j+1)))).truth=some true := by
      simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed]
    by_cases hg : b (bst+j)<a (ast+j)
    · refine ⟨middle,j,?_,hm⟩
      have hf : Exec context before loop (.returned (.integer (integer64 2))) middle :=
        .whileExit hcond htrue (by simpa only [stepFlow,if_pos hg] using first)
          (by simp)
      simpa only [comparedFlow,if_pos hg] using hf
    · by_cases hl : a (ast+j)<b (bst+j)
      · refine ⟨middle,j,?_,hm⟩
        have hf : Exec context before loop (.returned (.integer (integer64 0))) middle :=
          .whileExit hcond htrue (by simpa only [stepFlow,if_neg hg,if_pos hl] using first)
            (by simp)
        simpa only [comparedFlow,if_neg hg,if_pos hl] using hf
      · obtain ⟨after,k,rest,hk⟩ := ih hm
        refine ⟨after,k,?_,hk⟩
        have hf : Exec context before loop (comparedFlow (fun i=>a (ast+i)) (fun i=>b (bst+i)) j) after :=
          .whileNext hcond htrue (by simpa only [stepFlow,if_neg hg,if_neg hl] using first) rest
        simpa only [comparedFlow,if_neg hg,if_neg hl] using hf

def localWrites (li : Var → Nat) : List (String×Pointer) :=
  [("j",scalarPointer (li Var.j) .u64)]

/-- The complete actual loop frames every object except its fresh local j.
In particular both compared arrays and every other caller allocation remain
unchanged, even when the two source slices alias. -/
theorem loop_frame {F : Type} {context : Context F} {before after : State F}
    {ao al ast bo bl bst owner j : Nat} {li : Var → Nat} {a b : Nat → Nat}
    (h : View before ao al ast bo bl bst owner li a b j) {flow : Flow}
    (run : Exec context before loop flow after) : ScanFrame.Frame before after [li Var.j] := by
  have bindings : SourceArrayFrame.Bindings before (localWrites li) [] := by
    constructor
    · intro cname pointer member
      simp only [localWrites,List.mem_singleton,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩
      exact h.locals.lookup Var.j
    · intro item member
      cases member
    · intro item member
      cases member
  have writes : SourceArrayFrame.Only (localWrites li) [] loop := by
    simp [loop,loopBody,condition,decrement,branch,comparison,index,returnStmt,
      SourceArrayFrame.Only,SourceArrayFrame.Writable,localWrites]
  have noalloc : SourceNoAlloc.Only loop := by
    simp [loop,loopBody,condition,decrement,branch,comparison,index,returnStmt,
      SourceNoAlloc.Only,SourcePure.CallFree]
  have frame := SourceArrayFrame.exec_frame run writes noalloc h.well bindings
  simpa [SourceArrayFrame.writes,localWrites,scalarPointer] using frame

#print axioms condition_eval
#print axioms gt_eval
#print axioms lt_eval
#print axioms loop_body_execution
#print axioms loop_execution
#print axioms loop_frame
end RH080Next.FFTPV.CompareSource

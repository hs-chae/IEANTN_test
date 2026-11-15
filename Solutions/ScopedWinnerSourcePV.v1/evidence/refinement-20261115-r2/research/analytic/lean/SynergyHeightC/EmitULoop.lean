/- All eight iterations of the actual C words[i]=(uint64_t)(x>>(64*i)) loop. -/
import SynergyHeightC.EmitULoopStep
namespace SynergyHeightC.EmitULoop
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyHeightC.EmitUStorage SynergyHeightC.EmitUExpressions
open SynergyHeightC.EmitULoopStep
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def body : Stmt := .sequence [store,increment]

theorem guard_true (call : Machine.Call) (caller : State) (x : Int)
    (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call 2 (frame caller x i) guard=
      some (Machine.boolean SynergyC.Header.layout true,frame caller x i) := by
  apply ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (eval_i call 0 caller x i) rfl
  interval_cases i <;> rfl

theorem guard_false (call : Machine.Call) (caller : State) (x : Int) :
    evalExpr SynergyC.Header.layout call 2 (frame caller x 8) guard=
      some (Machine.boolean SynergyC.Header.layout false,frame caller x 8) := by
  exact ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (eval_i call 0 caller x 8) rfl rfl

theorem pop_frames (caller : State) (x : Int) (i j : Nat) :
    Machine.popScope (frame caller x i) (frame caller x j)=frame caller x j := by
  have hl : (frame caller x i).heap.length=(frame caller x j).heap.length := by
    simp [heap_shape]
  have he : (frame caller x i).env=(frame caller x j).env := by simp [env_shape]
  simp only [Machine.popScope,hl,List.take_length,he]

theorem world_iteration (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    (caller : State) (x : Int) (hx : SynergyC.Word512.Range x) (i : Nat) (hi : i<8) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout pure service platform body
      ⟨frame caller x i,stream⟩ (.continuing ⟨frame caller x (i+1),stream⟩) := by
  apply Loops.StmtRun.sequence
  · exact Loops.SeqRun.next
      (Loops.StmtRun.evaluate (ScopedIO.WorldSource.Eval.pure
        (actual_store pure caller x hx i hi)))
      (Loops.SeqRun.next
        (Loops.StmtRun.evaluate (ScopedIO.WorldSource.Eval.pure
          (actual_increment pure caller x i hi))) (Loops.SeqRun.nil _))
  · change (⟨frame caller x (i+1),stream⟩ : ScopedIO.WorldIO.World)=
      ⟨Machine.popScope (frame caller x i) (frame caller x (i+1)),stream⟩
    rw [pop_frames]

theorem world_loop_from (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    (caller : State) (x : Int) (hx : SynergyC.Word512.Range x)
    (remaining i : Nat) (count : i+remaining=8) :
    Loops.WhileRun (ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform)
      (ScopedIO.WorldSource.Declare SynergyC.Header.layout pure) truth ScopedIO.WorldSource.Scope
      guard body ⟨frame caller x i,stream⟩ (.continuing ⟨frame caller x 8,stream⟩) := by
  induction remaining generalizing i with
  | zero =>
      have same : i=8 := by omega
      subst i
      exact Loops.WhileRun.done
        (ScopedIO.WorldSource.Eval.pure (guard_false pure caller x)) rfl
  | succ remaining ih =>
      have hi : i<8 := by omega
      exact Loops.WhileRun.next
        (ScopedIO.WorldSource.Eval.pure (guard_true pure caller x i hi)) rfl
        (world_iteration pure service platform stream caller x hx i hi)
        (ih (i+1) (by omega))

theorem actual_world_loop (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (stream : ScopedIO.Stream)
    (caller : State) (x : Int) (hx : SynergyC.Word512.Range x) :
    ScopedIO.WorldSource.Run SynergyC.Header.layout pure service platform
      (.whileLoop guard body) ⟨EmitUFrames.initial caller x,stream⟩
      (.continuing ⟨frame caller x 8,stream⟩) := by
  rw [←first_frame]
  exact Loops.StmtRun.whileLoop
    (world_loop_from pure service platform stream caller x hx 8 0 rfl)

#print axioms pop_frames
#print axioms world_iteration
#print axioms actual_world_loop
end SynergyHeightC.EmitULoop

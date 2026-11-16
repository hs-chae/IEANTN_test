/- Actual first-loop prefix: bound source input declarations, live c/D
buffers, actual pointHeight expression, and readback from that SAME run. -/
import SynergyHeightC.FullMainPoint0Instance
import SynergyHeightC.FullMainPoint0Expression
namespace SynergyHeightC.FullMainPoint0Flow
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem model_result_of_checked {base : State} {input : ProofBox}
    (h : FullContractPointExecute.checkedModel base input=true) :
    ∃ c d after, PointExecuteAPI.modelOutputs input=some (c,d) ∧
      FullContractPointExecute.run base input=some (.unit,after) ∧
      Machine.read SynergyC.Header.layout after (PointExecuteAPI.cAddress base)=
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after (PointExecuteAPI.dAddress base)=
        some (SynergyC.SourceIntervalMath.represented d) := by
  cases hm : PointExecuteAPI.modelOutputs input with
  | none => simp [FullContractPointExecute.checkedModel,hm] at h
  | some pair =>
    rcases pair with ⟨c,d⟩
    have checked : FullContractPointExecute.checked base input c d=true := by
      simpa only [FullContractPointExecute.checkedModel,hm] using h
    obtain ⟨after,hr,hc,hd,_⟩ := FastPointExecute.resultCheck_sound checked
    exact ⟨c,d,after,rfl,hr,hc,hd⟩

theorem seq_append {cfg : Layout} {call : Call} {ss tt : List Stmt}
    {s middle : State} {out : Loops.Flow State Value}
    (first : Loops.SeqRun (ArraySourceCalls.Eval cfg call) (ArraySourceCalls.Declare cfg call)
      truth ArraySourceCalls.Scope ss s (.continuing middle))
    (rest : Loops.SeqRun (ArraySourceCalls.Eval cfg call) (ArraySourceCalls.Declare cfg call)
      truth ArraySourceCalls.Scope tt middle out) :
    Loops.SeqRun (ArraySourceCalls.Eval cfg call) (ArraySourceCalls.Declare cfg call)
      truth ArraySourceCalls.Scope (ss++tt) s out := by
  induction ss generalizing s with
  | nil => cases first; exact rest
  | cons head tail ih =>
      cases first with
      | next hhead htail => exact Loops.SeqRun.next hhead (ih htail)

theorem actual_loop_prefix : PointExecuteAPI.loopStatements.take 4 =
    FullMainEdge.statements ++ [.declare PointExecuteAPI.declarations,
      .eval FullMainPoint0Expression.expression] := by rfl

def guard : Expr := .binary "<" (.var "i") (.var "cells")
theorem actual_guard (call : Call) :
    evalExpr SynergyC.Header.layout call 128 FullMainPrefix.prefixState guard=
      some (Machine.boolean SynergyC.Header.layout true,FullMainPrefix.prefixState) := by rfl

/-- The records in the conclusion come from the actual first source call
at source-generated right endpoint, not a second independent numerical fact. -/
theorem actual_first_loop_prefix :
    ∃ c d after, PointExecuteAPI.modelOutputs FullMainEdge.right=some (c,d) ∧
      Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
        (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
        (PointExecuteAPI.loopStatements.take 4) FullMainPrefix.prefixState (.continuing after) ∧
      Machine.read SynergyC.Header.layout after ⟨21,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after ⟨22,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented d) := by
  obtain ⟨c,d,after,hm,hr,hc,hd⟩ := model_result_of_checked
    (base:=FullMainEdge.afterRight) (input:=FullMainEdge.right) FullMainPoint0.checked_source_main_point
  have buffers : ArraySourceCalls.Run SynergyC.Header.layout FullMainPrefix.service
      (.declare PointExecuteAPI.declarations) FullMainEdge.afterRight
      (.continuing (PointExecuteAPI.buffers FullMainEdge.afterRight)) :=
    Loops.StmtRun.declare (PointExecuteAPI.buffers_from_actual_declaration _ _)
  have call := FullMainPoint0Expression.statement_of_run hr
  have tail := Loops.SeqRun.next buffers (Loops.SeqRun.next call (Loops.SeqRun.nil after))
  have sequence := seq_append FullMainEdge.actual_source_edges tail
  rw [←actual_loop_prefix] at sequence
  exact ⟨c,d,after,hm,sequence,hc,hd⟩

/-- Numerical meaning of the SAME intervals read at actual source pointers. -/
theorem actual_first_loop_enclosures {x : ℝ}
    (hx : SynergyBasis.RealBox.Contains 128 FullMainEdge.right x) :
    ∃ c d after,
      Loops.SeqRun (ArraySourceCalls.Eval SynergyC.Header.layout FullMainPrefix.service)
        (ArraySourceCalls.Declare SynergyC.Header.layout FullMainPrefix.service) truth ArraySourceCalls.Scope
        (PointExecuteAPI.loopStatements.take 4) FullMainPrefix.prefixState (.continuing after) ∧
      Machine.read SynergyC.Header.layout after ⟨21,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented c) ∧
      Machine.read SynergyC.Header.layout after ⟨22,0,[]⟩=
        some (SynergyC.SourceIntervalMath.represented d) ∧
      SynergyBasis.RealBox.Contains 128 c (SynergyAnalytic.HeightPoint.r184 x) ∧
      SynergyBasis.RealBox.Contains 128 d (SynergyAnalytic.HeightPoint.r186 x) := by
  obtain ⟨c,d,after,hm,run,hc,hd⟩ := actual_first_loop_prefix
  obtain ⟨mc,md⟩ := PointExecuteAPI.model_output_enclosures hm hx
  exact ⟨c,d,after,run,hc,hd,mc,md⟩

#print axioms model_result_of_checked
#print axioms actual_guard
#print axioms actual_first_loop_prefix
#print axioms actual_first_loop_enclosures
end SynergyHeightC.FullMainPoint0Flow

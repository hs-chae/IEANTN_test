/- Actual short-circuit generation guard. The forced first iteration does
not call nz; every later check includes nz's real zero allocation. -/
import ScopedIO.PrintSDigitRHS

namespace ScopedIO.PrintSCondition
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def expression : Expr := .binary "||" (.var "first")
  (.unary "!" (.call (.var "nz") [.var "x"]))

theorem forced (service : Call) (s : State) (a : Value) (ds : List Nat)
    (slot count : Nat) :
    Eval Header.layout service expression (frame s a ds slot count 1)
      (frame s a ds slot count 1) (boolean Header.layout true) := by
  have firstValue := LocalBinding.eval service 0 (PrintSAssignments.first_at s a ds slot count 1)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨2,?_⟩
  rw [expression,evalExpr,firstValue]
  rfl

theorem actual_nz (code : List Function) (nzInstalled : Generated.f_nz ∈ code)
    (nuInstalled : Generated.f_nu ∈ code) (neInstalled : Generated.f_ne ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {c : Cursor} {slot n : Nat}
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top < capacity) (a : Value) (ds : List Nat) (count : Nat) :
    SourceCall Header.layout code 3 "nz" [.natObject slot]
      (frame c.state a ds slot count 0) (PrimitiveCalls.u32 (n==0))
      (frame (next l c 0).state a ds slot count 0) := by
  have call := nz_call code nzInstalled nuInstalled neInstalled keepInstalled
    (PrintSPoolFrames.frame_context ctx a ds slot count 0) room live
  simpa only [PrintSPoolFrames.frame_binary ctx,next] using call

theorem subsequent (service : Call) (l : PoolLayout) (c : Cursor)
    (a : Value) (ds : List Nat) (slot count n : Nat)
    (answer : service "nz" [.natObject slot] (frame c.state a ds slot count 0) =
      some (PrimitiveCalls.u32 (n==0),frame (next l c 0).state a ds slot count 0)) :
    Eval Header.layout service expression (frame c.state a ds slot count 0)
      (frame (next l c 0).state a ds slot count 0)
      (boolean Header.layout (decide (n ≠ 0))) := by
  have xValue := LocalBinding.eval service 0 (PrintSDigitRHS.x_at c.state a ds slot count 0)
    (by decide) (by decide) (by decide) (by decide)
  have nzResult := ExpressionTemplates.call_one Header.layout service xValue answer
  have negative : evalExpr Header.layout service 3 (frame c.state a ds slot count 0)
      (.unary "!" (.call (.var "nz") [.var "x"])) =
      some (boolean Header.layout (decide (n ≠ 0)),
        frame (next l c 0).state a ds slot count 0) := by
    rw [evalExpr,nzResult]
    by_cases zero : n=0 <;> simp [zero,PrimitiveCalls.u32,truth,Scalar.truth]
  have firstValue := LocalBinding.eval service 2 (PrintSAssignments.first_at c.state a ds slot count 0)
    (by decide) (by decide) (by decide) (by decide)
  refine ⟨4,?_⟩
  rw [expression,evalExpr,firstValue]
  change (do let (r,last) ← evalExpr Header.layout service 3
               (frame c.state a ds slot count 0)
               (.unary "!" (.call (.var "nz") [.var "x"]))
             pure (boolean Header.layout (truth r),last)) = _
  rw [negative]
  cases decide (n ≠ 0) <;> rfl

end ScopedIO.PrintSCondition

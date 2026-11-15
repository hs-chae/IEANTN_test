/- The literal nested original printS RHS. Every service answer below is
discharged by the separately proved actual nu/nr/small source calls. -/
import ScopedIO.PrintSDigitCalls
import ScopedIO.PrintSDigitExpression

namespace ScopedIO.PrintSDigitRHS
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSDigitCalls
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def expression : Expr := .cast "char" (.binary "+" (.character 48)
  (.call (.var "small") [.call (.var "nr") [.var "x",.call (.var "nu") [.nat 10]]]))

theorem x_at (s : State) (a : Value) (ds : List Nat) (slot count first : Nat) :
    LocalBinding.At (frame s a ds slot count first) "x" "N" (.natObject slot)
      (s.heap.length+3) := by
  have initial := LocalBinding.allocate_head
    (allocate (buffer s a ds) "unsigned int" "count" (some (unsigned32 count)))
    "x" "N" (.natObject slot) rfl
  have final := LocalBinding.allocate_other initial "first" "unsigned int"
    (some (unsigned32 first)) (by decide)
  simpa [frame,buffer,parameter,allocate,Nat.add_assoc] using final

theorem actual_expression (service : Call) (l : PoolLayout) (c : Cursor)
    (a : Value) (ds : List Nat) (slot count first n : Nat)
    (nuAnswer : service "nu" [DecimalDigits.integer 10]
      (frame c.state a ds slot count first) =
      some (.natObject c.state.nats.values.length,frame (c1 l c).state a ds slot count first))
    (nrAnswer : service "nr" [.natObject slot,.natObject c.state.nats.values.length]
      (frame (c1 l c).state a ds slot count first) =
      some (.natObject (c1 l c).state.nats.values.length,
        frame (c2 l c n).state a ds slot count first))
    (smallAnswer : service "small" [.natObject (c1 l c).state.nats.values.length]
      (frame (c2 l c n).state a ds slot count first) =
      some (unsigned32 (n%10),frame (c3 l c n).state a ds slot count first)) :
    evalExpr Header.layout service 6 (frame c.state a ds slot count first) expression =
      some (DecimalDigits.digit (n%10),frame (c3 l c n).state a ds slot count first) := by
  have nx := LocalBinding.eval service 1 (x_at c.state a ds slot count first)
    (by decide) (by decide) (by decide) (by decide)
  have nuResult := ExpressionTemplates.call_one Header.layout service
    (show evalExpr Header.layout service 1 (frame c.state a ds slot count first) (.nat 10) =
      some (DecimalDigits.integer 10,frame c.state a ds slot count first) from rfl) nuAnswer
  have nrResult := ExpressionTemplates.call_two Header.layout service nx nuResult nrAnswer
  have smallResult := ExpressionTemplates.call_one Header.layout service nrResult smallAnswer
  have sumResult := ExpressionTemplates.binary Header.layout service
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (show evalExpr Header.layout service 4 (frame c.state a ds slot count first)
      (.character 48) = some (DecimalDigits.char 48,frame c.state a ds slot count first)
      from rfl) smallResult
    (PrintSDigitExpression.digit_sum (frame (c3 l c n).state a ds slot count first)
      (n%10) (by omega))
  exact ExpressionTemplates.cast Header.layout service sumResult
    (PrintSDigitExpression.digit_conversion _ (n%10) (by omega))

end ScopedIO.PrintSDigitRHS

/- The exact original '0'+small(...) promotion, char conversion and physical
array lvalue/store. The nested small/nr/nu source calls are joined separately. -/
import ScopedIO.PrintSBuffer

namespace ScopedIO.PrintSDigitExpression
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem digit_sum (s : State) (d : Nat) (decimal : d < 10) :
    binaryValue Header.layout s "+" (DecimalDigits.char 48) (unsigned32 d) =
      some (unsigned32 (48+d)) := by
  interval_cases d <;> rfl

theorem digit_conversion (s : State) (d : Nat) (decimal : d < 10) :
    castValue Header.layout s 100 "char" (unsigned32 (48+d)) =
      some (DecimalDigits.digit d) := by
  interval_cases d <;> rfl

theorem index_address (service : Call) (fuel : Nat) (s : State) (a : Value)
    (ds : List Nat) (slot first : Nat) (capacity : ds.length < 1024) :
    evalLValue Header.layout service (fuel+2) (frame s a ds slot ds.length first)
      (.index (.var "digits") (.var "count")) =
      some (⟨s.heap.length+1,ds.length,[]⟩,true,frame s a ds slot ds.length first) := by
  have countValue := LocalBinding.eval service fuel
    (count_at s a ds slot ds.length first) (by decide) (by decide) (by decide) (by decide)
  have size := cells_length (show ds.length ≤ 1024 by omega)
  rw [evalLValue,PrintSRead.array_value]
  simp only [Bind.bind,Option.bind,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [countValue]
  simp [asNat,word,unsigned32,addressType,PrintSRead.buffer_object,size,capacity,typeAt]

theorem store_expression (service : Call) (fuel : Nat) (before s : State) (a : Value)
    (ds : List Nat) (slot first d : Nat) (rhs : Expr)
    (capacity : ds.length < 1024) (decimal : d < 10)
    (right : evalExpr Header.layout service (fuel+3) before rhs =
      some (DecimalDigits.digit d,frame s a ds slot ds.length first)) :
    evalExpr Header.layout service (fuel+4) before
      (.binary "=" (.index (.var "digits") (.var "count")) rhs) =
      some (DecimalDigits.digit d,frame s a (ds++[d]) slot ds.length first) := by
  rw [evalExpr,right]
  simp only [Bind.bind,Option.bind]
  rw [index_address service (fuel+1) s a ds slot first capacity]
  exact PrintSBuffer.write_digit s a ds slot ds.length first d capacity decimal

end ScopedIO.PrintSDigitExpression

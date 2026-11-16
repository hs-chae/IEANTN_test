/- Exact source expressions of the fixed eight-word emitU loop. -/
import SynergyHeightC.EmitUStorage
import SynergyC.WordShiftRight
import ScopedC.ExpressionBinary
namespace SynergyHeightC.EmitUExpressions
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyHeightC.EmitUStorage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def indexValue (i : Nat) : Value := .integer ⟨⟨false,32⟩,(i:Int)⟩
def shiftExpr : Expr := .binary ">>" (.var "x") (.binary "*" (.nat 64) (.var "i"))
def rhs : Expr := .cast "uint64_t" shiftExpr
def guard : Expr := .binary "<" (.var "i") (.nat 8)
def store : Stmt := .eval (.binary "=" (.index (.var "words") (.var "i")) rhs)
def increment : Stmt := .eval (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))

theorem actual_loop : EmitUFrames.statements[2]?=some (.whileLoop guard (.sequence [store,increment])) := by rfl

theorem eval_x (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) :
    evalExpr SynergyC.Header.layout call (fuel+1) (frame caller x i) (.var "x")=
      some (SynergyC.Word512.value x,frame caller x i) := by
  rw [evalExpr]
  simp [get_x,heap_shape,xAddress,Machine.read,Machine.nested,Machine.initialized,SynergyC.Word512.value]

theorem eval_i (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) :
    evalExpr SynergyC.Header.layout call (fuel+1) (frame caller x i) (.var "i")=
      some (indexValue i,frame caller x i) := by
  rw [evalExpr]
  simp [get_i,heap_shape,iAddress,Machine.read,Machine.nested,Machine.initialized,indexValue]

theorem eval_words (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) :
    evalExpr SynergyC.Header.layout call (fuel+1) (frame caller x i) (.var "words")=
      some (.pointer (wordsAddress caller) true,frame caller x i) := by
  rw [evalExpr]
  simp [get_words,heap_shape,wordsAddress,arrayObject]

theorem eval_64 (call : Machine.Call) (fuel : Nat) (s : State) :
    evalExpr SynergyC.Header.layout call (fuel+1) s (.nat 64)=
      some (.integer ⟨⟨true,32⟩,64⟩,s) := by rfl

theorem multiply_64 (s : State) (i : Nat) (hi : i<8) :
    Machine.binaryValue SynergyC.Header.layout s "*" (.integer ⟨⟨true,32⟩,64⟩) (indexValue i)=
      some (indexValue (64*i)) := by
  interval_cases i <;> rfl

theorem eval_times_i (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call (fuel+2) (frame caller x i)
      (.binary "*" (.nat 64) (.var "i"))=some (indexValue (64*i),frame caller x i) := by
  exact ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (eval_64 call fuel (frame caller x i)) (eval_i call fuel caller x i)
    (multiply_64 (frame caller x i) i hi)

theorem eval_shift (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (hx : SynergyC.Word512.Range x)
    (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call (fuel+3) (frame caller x i) shiftExpr=
      some (SynergyC.Word512.value (x/(2^(64*i):Int)),frame caller x i) := by
  exact ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (eval_x call (fuel+1) caller x i) (eval_times_i call fuel caller x i hi)
    (SynergyC.Word512.binaryValue_shiftRight (frame caller x i) hx (64*i) (by omega))

theorem eval_rhs (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (hx : SynergyC.Word512.Range x)
    (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call (fuel+4) (frame caller x i) rhs=
      some (EmitUWord64.value (EmitUWord64.part x i),frame caller x i) := by
  exact ExpressionTemplates.cast SynergyC.Header.layout call
    (eval_shift call fuel caller x hx i hi) (EmitUWord64.cast_shift_part (frame caller x i) x i)

#print axioms actual_loop
#print axioms eval_words
#print axioms eval_shift
#print axioms eval_rhs
end SynergyHeightC.EmitUExpressions

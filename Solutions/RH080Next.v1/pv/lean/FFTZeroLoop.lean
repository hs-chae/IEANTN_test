/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTSourceSteps
import FFTWordArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- Real automatic scalar objects; the buffer is a separate host allocation. -/
def automaticWord (value : Nat) : Object :=
  {wordObject 1 (fun _=>value) with storage:=.automatic 1}
def automaticPointer : Object :=
  {extent:=8,storage:=.automatic 1,cells:=fun offset=>
    if offset=0 then some (.pointer (wordPointer 0 0)) else none}

def frameState (length filled counter scope nextScope : Nat) : State Unit :=
  {environment:=[("j",wordPointer 3 0),("n",wordPointer 2 0),
      ("a",⟨1,0,.pointer .u64⟩)],
   objects:=fun key=>if key=0 then some (zeroPrefixObject length filled)
     else if key=1 then some automaticPointer
     else if key=2 then some (automaticWord length)
     else if key=3 then some (automaticWord counter) else none,
   nextObject:=4,scope:=scope,nextScope:=nextScope,foreign:=()}

def loopState (length filled scope nextScope : Nat) : State Unit :=
  frameState length filled filled scope nextScope

def condition : Expr := .binary .lt (.variable "j") (.variable "n")
def increment : Stmt := .assign (.variable "j")
  (.paren (.binary .add (.variable "j") (.literal (.integer 1 "ULL"))))
def loopBody : Stmt := .block [zeroStoreStmt,increment]
def loop : Stmt := .whileLoop condition loopBody

theorem loop_is_actual : zero_words_ast.body =
    .block [.declare .u64 "j" (some (.literal (.integer 0 "ULL"))),
      loop,.returnValue (some (.literal (.integer 0 "ULL")))] := by rfl

private theorem read_a (n j s ns : Nat) :
    (loopState n j s ns).load ⟨1,0,.pointer .u64⟩=some (.pointer (wordPointer 0 0)) := by
  simp [loopState,frameState,State.load,automaticPointer,CType.byteSize,State.accessible,
    Value.convert,CType.integer,wordPointer]

private theorem read_n (n j s ns : Nat) (hn : n<2^64) :
    (loopState n j s ns).load (wordPointer 2 0)=some (.integer (integer64 n)) := by
  simp [loopState,frameState,State.load,automaticWord,wordObject,wordPointer,CType.byteSize,
    State.accessible,integer64,IntKind.width]
  exact convert64 n hn

private theorem read_j (n j s ns : Nat) (hj : j<2^64) :
    (loopState n j s ns).load (wordPointer 3 0)=some (.integer (integer64 j)) := by
  simp [loopState,frameState,State.load,automaticWord,wordObject,wordPointer,CType.byteSize,
    State.accessible,integer64,IntKind.width]
  exact convert64 j hj

private theorem binary64_lt (j n : Nat) (hj : j<2^64) (hn : n<2^64) :
    Integer.binary .lt (integer64 j) (integer64 n)=
      some (.boolean (decide (j<n))) := by
  change some (Integer.boolean ((Integer.cast .u64 (j:Int)).toInt<
    (Integer.cast .u64 (n:Int)).toInt))=_
  rw [cast64_exact j hj,cast64_exact n hn,integer64_toInt,integer64_toInt]
  congr 2
  simp

private theorem condition_eval (context : Context Unit) (n j s ns : Nat)
    (hn : n<2^64) (hj : j<2^64) :
    Eval context (loopState n j s ns) condition
      (.integer (.boolean (decide (j<n)))) (loopState n j s ns) := by
  exact .binaryLR (.variable (by rfl) (read_j n j s ns hj))
    (.variable (by rfl) (read_n n j s ns hn))
    (by simp only [binary,binary64_lt j n hj hn,Option.map_some])

private theorem buffer_step (n j s ns : Nat) (hj : j<n) :
    (loopState n j s ns).store (wordPointer 0 j) (.integer (integer64 0))=
      some (frameState n (j+1) j s ns) := by
  have h := zeroPrefix_store (state:=loopState n j s ns) (object:=0)
    (by rfl) (by simp [loopState,frameState]) hj
  convert h using 1
  congr 1
  simp only [loopState,frameState]
  congr 1
  funext key
  by_cases hk : key=0
  · simp [hk,loopState,frameState]
  · simp [hk,loopState,frameState]

private theorem read_counter (n p j s ns : Nat) (hj : j<2^64) :
    (frameState n p j s ns).load (wordPointer 3 0)=some (.integer (integer64 j)) := by
  simp [frameState,State.load,automaticWord,wordObject,wordPointer,CType.byteSize,
    State.accessible,integer64]
  exact convert64 j hj

private theorem counter_step (n p j s ns : Nat) (hj : j+1<2^64) :
    (frameState n p j s ns).store (wordPointer 3 0) (.integer (integer64 (j+1)))=
      some (frameState n p (j+1) s ns) := by
  simp [State.store,frameState,wordPointer,automaticWord,wordObject,
    CType.byteSize,State.accessible,convert64 (j+1) hj]
  funext key
  by_cases h0 : key=0
  · simp [h0]
  by_cases h1 : key=1
  · simp [h1]
  by_cases h2 : key=2
  · simp [h2]
  by_cases h3 : key=3
  · simp [h3]
    congr 1
    funext offset
    by_cases hz : offset=0
    · simp [hz]
    · have hnone : ¬(offset%8=0 ∧ offset<8) := by omega
      simp [hz,hnone,Option.filter]
  · simp [h0,h1,h2,h3]

private theorem increment_exec (context : Context Unit) (n p j s ns : Nat)
    (hj : j+1<2^64) :
    Exec context (frameState n p j s ns) increment .normal
      (frameState n p (j+1) s ns) := by
  apply Exec.assign (value:=.integer (integer64 (j+1))) (Eval.paren (Eval.binaryLR
    (.variable (by rfl) (read_counter n p j s ns (by omega)))
    (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl))
    (by simp only [binary,binary64_add j 1 (by omega) (by norm_num) hj,Option.map_some])))
    (.variable (by rfl))
  exact counter_step n p j s ns hj

private theorem buffer_exec (context : Context Unit) (n j s ns : Nat)
    (hj : j<n) (hn : n<2^64) :
    Exec context (loopState n j s ns) zeroStoreStmt .normal
      (frameState n (j+1) j s ns) := by
  apply Exec.assign (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
    (.index (.variable (by rfl) (read_a n j s ns))
      (.variable (by rfl) (read_j n j s ns (by omega)))
      (zero_array_pointer_add (by rfl) (by simp [loopState,frameState]) hj))
  exact buffer_step n j s ns hj

private theorem leave_loop_body (n j ns : Nat) (hns : 2≤ns) :
    {(loopState n j ns (ns+1)).leaveScope ns (loopState n j 1 ns).environment
      with scope:=1}=loopState n j 1 (ns+1) := by
  have hne : 1≠ns := by omega
  simp only [State.leaveScope,loopState,frameState]
  congr 1
  funext key
  split_ifs <;> simp [zeroPrefixObject,automaticPointer,automaticWord,wordObject,hne]

/-- Actual C block execution, with typed buffer and automatic-counter stores,
ordinary uint64 arithmetic, block entry and block lifetime exit. -/
theorem loop_body_execution (context : Context Unit) (n j ns : Nat)
    (hj : j<n) (hn : n<2^64) (hns : 2≤ns) :
    Exec context (loopState n j 1 ns) loopBody .normal
      (loopState n (j+1) 1 (ns+1)) := by
  apply Exec.block (start:=loopState n j ns (ns+1)) (middle:=loopState n (j+1) ns (ns+1))
    (by rfl)
  · exact .cons (buffer_exec context n j ns (ns+1) hj hn)
      (.cons (increment_exec context n (j+1) j ns (ns+1) (by omega)) .nil)
  · exact (leave_loop_body n (j+1) ns hns).symm

/-- General execution of the actual zero_words source while loop. The theorem
proves every iteration and counter update; it is not a memory-only subtrace.
The entry frame is explicit and caller framing remains a separate obligation. -/
theorem loop_execution (context : Context Unit) (steps n j ns : Nat)
    (remaining : j+steps=n) (hn : n<2^64) (hns : 2≤ns) :
    Exec context (loopState n j 1 ns) loop .normal
      (loopState n n 1 (ns+steps)) := by
  induction steps generalizing j ns with
  | zero =>
    have he : j=n := by omega
    subst j
    simpa only [Nat.add_zero,loop] using Exec.whileFalse
      (condition_eval context n n 1 ns hn hn)
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed])
  | succ steps ih =>
    have hj : j<n := by omega
    have rest := ih (j+1) (ns+1) (by omega) (by omega)
    have he : ns+1+steps=ns+(steps+1) := by omega
    rw [he] at rest
    apply Exec.whileNext (condition_eval context n j 1 ns hn (by omega))
      (by simp [Value.truth,Integer.truth,Integer.boolean,Integer.toInt,IntKind.signed,hj])
      (loop_body_execution context n j ns hj hn hns)
    exact rest

#print axioms loop_body_execution
#print axioms loop_execution

#print axioms buffer_step
#print axioms counter_step

#print axioms loop_is_actual
#print axioms condition_eval
end RH080Next.FFTPV.ZeroLoop

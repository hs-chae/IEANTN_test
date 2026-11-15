/- Pool and Nat-arena effects commute with the actual five printS local
objects. This preserves the physical uninitialized/written char prefix. -/
import ScopedIO.PrintSAssignments
import ScopedIO.PrintSBuffer
import ScopedC.ArrayFrames
import ScopedC.CursorSingleFrames

namespace ScopedIO.PrintSPoolFrames
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedC.PoolCursor ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem parameter_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (ctx : GenericPoolContext l s cells top high) (a : Value) :
    GenericPoolContext l (parameter s a) cells top high :=
  OneFrames.context_frame ctx "S" "a" a

theorem buffer_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (ctx : GenericPoolContext l s cells top high)
    (a : Value) (ds : List Nat) :
    GenericPoolContext l (buffer s a ds) cells top high :=
  ArrayFrames.context_frame (parameter_context ctx a) "char" "digits" (digitCells ds)

theorem frame_context {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (ctx : GenericPoolContext l s cells top high)
    (a : Value) (ds : List Nat) (slot count first : Nat) :
    GenericPoolContext l (frame s a ds slot count first) cells top high :=
  AllocatedFrames.context_allocate
    (AllocatedFrames.context_allocate
      (AllocatedFrames.context_allocate (buffer_context ctx a ds)
        "unsigned int" "count" (unsigned32 count)) "N" "x" (.natObject slot))
    "unsigned int" "first" (unsigned32 first)

theorem buffer_binary {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (ctx : GenericPoolContext l s cells top high)
    (a : Value) (ds : List Nat) (n : Nat) :
    binaryResult l (buffer s a ds) cells top high n =
      buffer (binaryResult l s cells top high n) a ds := by
  change binaryResult l (ArrayFrames.frame (parameter s a) "char" "digits" (digitCells ds))
    cells top high n = _
  rw [ArrayFrames.binary_frame (parameter_context ctx a)]
  rw [show binaryResult l (parameter s a) cells top high n =
      parameter (binaryResult l s cells top high n) a from
    binary_result_one_frame ctx "S" "a" a]
  rfl

theorem frame_binary {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (ctx : GenericPoolContext l s cells top high)
    (a : Value) (ds : List Nat) (slot count first n : Nat) :
    binaryResult l (frame s a ds slot count first) cells top high n =
      frame (binaryResult l s cells top high n) a ds slot count first := by
  have cb := buffer_context ctx a ds
  have cc := AllocatedFrames.context_allocate cb "unsigned int" "count" (unsigned32 count)
  have cx := AllocatedFrames.context_allocate cc "N" "x" (.natObject slot)
  unfold frame
  rw [AllocatedFrames.binary_allocate cx,AllocatedFrames.binary_allocate cc,
    AllocatedFrames.binary_allocate cb,buffer_binary ctx]

def framed (c : Cursor) (a : Value) (ds : List Nat) (slot count first : Nat) : Cursor :=
  {c with state := frame c.state a ds slot count first}

theorem next_framed {l : PoolLayout} {c : Cursor} (ctx : Valid l c)
    (a : Value) (ds : List Nat) (slot count first n : Nat) :
    next l (framed c a ds slot count first) n =
      framed (next l c n) a ds slot count first := by
  unfold next framed
  dsimp only
  rw [frame_binary ctx]
  rfl

theorem advance_framed {l : PoolLayout} {c : Cursor} (ctx : Valid l c)
    (a : Value) (ds : List Nat) (slot count first : Nat) (values : List Nat)
    (room : c.top+values.length ≤ capacity) :
    CursorFrames.advance l (framed c a ds slot count first) values =
      framed (CursorFrames.advance l c values) a ds slot count first := by
  induction values generalizing c with
  | nil => rfl
  | cons n ns ih =>
    rw [CursorFrames.advance,CursorFrames.advance,next_framed ctx]
    apply ih (next_valid n ctx (by simp only [List.length_cons] at room; omega))
    change c.top+1+ns.length ≤ capacity
    simp only [List.length_cons] at room
    omega

end ScopedIO.PrintSPoolFrames

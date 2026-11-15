/- Concrete original printS local-object order, including its uninitialized
1024-byte automatic array. No preinitialized digit buffer is assumed. -/
import ScopedC.UnsignedLocalSteps
import ScopedIO.PrintSDecimalModel
import ScopedIO.PrintTextBinding

namespace ScopedIO.PrintSFrames
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def parameter (s : State) (a : Value) : State :=
  allocate {s with env := []} "S" "a" (some a)

def digitCells (ds : List Nat) : List (Option Value) :=
  ds.map (fun d => some (DecimalDigits.digit d)) ++ List.replicate (1024-ds.length) none

def buffer (s : State) (a : Value) (ds : List Nat) : State :=
  let before := parameter s a
  {before with
    heap := before.heap ++ [{type := "char",cells := digitCells ds,isArray := true}]
    env := ("digits",⟨before.heap.length,0,[]⟩)::before.env}

def frame (s : State) (a : Value) (ds : List Nat) (slot count first : Nat) : State :=
  allocate (allocate (allocate (buffer s a ds) "unsigned int" "count"
    (some (unsigned32 count))) "N" "x" (some (.natObject slot)))
    "unsigned int" "first" (some (unsigned32 first))

theorem cells_length {ds : List Nat} (bound : ds.length ≤ 1024) :
    (digitCells ds).length = 1024 := by
  simp only [digitCells,List.length_append,List.length_map,List.length_replicate]
  omega

theorem actual_uninitialized_array (pureCall : Machine.Call) (s : State) (a : Value) :
    Machine.declarations Header.layout pureCall
      [{type := "char",name := "digits",value := none,arrayExtent := some 1024}]
      (parameter s a) = some (buffer s a []) := by
  simp [Machine.declarations,List.foldlM,buffer,digitCells]

theorem count_at (s : State) (a : Value) (ds : List Nat) (slot count first : Nat) :
    LocalBinding.At (frame s a ds slot count first) "count" "unsigned int"
      (word count) (s.heap.length+2) := by
  have initial := LocalBinding.allocate_head (buffer s a ds) "count" "unsigned int"
    (word count) rfl
  have middle := LocalBinding.allocate_other initial "x" "N" (some (.natObject slot))
    (by decide)
  have final := LocalBinding.allocate_other middle "first" "unsigned int"
    (some (word first)) (by decide)
  simpa [frame,buffer,parameter,allocate,word,unsigned32,Nat.add_assoc] using final

theorem decrement_source (pureCall : Machine.Call) (s : State) (a : Value)
    (ds : List Nat) (slot count first : Nat) (positive : 0 < count) (bound : count < 2^32) :
    SourceCalls.Eval Header.layout pureCall
      (.binary "=" (.var "count") (.binary "-" (.var "count") (.nat 1)))
      (frame s a ds slot count first)
      (LocalAssignment.changed (frame s a ds slot count first) (s.heap.length+2)
        "unsigned int" (word (count-1))) (word (count-1)) :=
  UnsignedLocalSteps.decrement pureCall (count_at s a ds slot count first) positive bound
    (by decide) (by decide) (by decide) (by decide)

theorem positive_source (pureCall : Machine.Call) (s : State) (a : Value)
    (ds : List Nat) (slot count first : Nat) (bound : count < 2^32) :
    SourceCalls.Eval Header.layout pureCall (.binary ">" (.var "count") (.nat 0))
      (frame s a ds slot count first) (frame s a ds slot count first)
      (boolean Header.layout (decide (0 < count))) :=
  UnsignedLocalSteps.positive_condition pureCall (count_at s a ds slot count first) bound
    (by decide) (by decide) (by decide) (by decide)

end ScopedIO.PrintSFrames

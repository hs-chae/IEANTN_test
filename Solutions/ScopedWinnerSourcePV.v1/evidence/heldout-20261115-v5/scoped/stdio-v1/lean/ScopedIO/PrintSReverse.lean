/- Original printS reverse-output while loop, with all stdio failures retained.
This development component still needs the generation-loop prefix invariant
and whole-function caller/return composition. -/
import ScopedIO.PrintSRead

namespace ScopedIO.PrintSReverse
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedIO.PrintSFrames ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def condition : Expr := .binary ">" (.var "count") (.nat 0)
def decrement : Expr := .binary "=" (.var "count") (.binary "-" (.var "count") (.nat 1))
def output : Expr := .call (.var "putchar") [.index (.var "digits") (.var "count")]
def iteration : Stmt := .sequence [.eval decrement,.eval output]

theorem changed_count (s : State) (a : Value) (ds : List Nat)
    (slot count first next : Nat) :
    LocalAssignment.changed (frame s a ds slot count first) (s.heap.length+2)
      "unsigned int" (word next) = frame s a ds slot next first := by
  simp [LocalAssignment.changed,storeObject,frame,buffer,parameter,allocate,
    word,unsigned32,List.set_append,Nat.add_assoc]

theorem pop_count_frame (s : State) (a : Value) (ds : List Nat)
    (slot before first after : Nat) :
    popScope (frame s a ds slot before first) (frame s a ds slot after first) =
      frame s a ds slot after first := by
  have sameLength : (frame s a ds slot before first).heap.length =
      (frame s a ds slot after first).heap.length := by
    simp [frame,buffer,parameter,allocate]
  have sameEnv : (frame s a ds slot before first).env =
      (frame s a ds slot after first).env := by
    simp [frame,buffer,parameter,allocate]
  simp [popScope,sameLength,sameEnv]

def nextStream (fault : WorldIO.FaultPolicy) (s : State) (a : Value)
    (ds : List Nat) (slot k first : Nat) (stream : Stream) : Stream :=
  writeBytes stream [48+(ds[k]?).getD 0]
    (fault.succeed "putchar" ⟨frame s a ds slot k first,stream⟩)
    (fault.count "putchar" ⟨frame s a ds slot k first,stream⟩)

def emit (fault : WorldIO.FaultPolicy) (s : State) (a : Value)
    (ds : List Nat) (slot first : Nat) : Nat → Stream → Stream
  | 0,stream => stream
  | k+1,stream => emit fault s a ds slot first k
      (nextStream fault s a ds slot k first stream)

theorem iteration_source (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (pureCall : Machine.Call) (s : State) (a : Value) (ds : List Nat)
    (slot k first : Nat) (hk : k < ds.length) (hd : ds[k] < 10)
    (bound : k+1 < 2^32) (stream : Stream) :
    WorldSource.Run Header.layout pureCall (TextWorldIO.external p fault) p iteration
      ⟨frame s a ds slot (k+1) first,stream⟩
      (.continuing ⟨frame s a ds slot k first,
        nextStream fault s a ds slot k first stream⟩) := by
  obtain ⟨fuel,run⟩ := decrement_source pureCall s a ds slot (k+1) first
    (by omega) bound
  have firstStep : WorldSource.Eval Header.layout pureCall (TextWorldIO.external p fault) p
      decrement ⟨frame s a ds slot (k+1) first,stream⟩
      ⟨frame s a ds slot k first,stream⟩ (word k) := by
    simpa only [decrement,changed_count,Nat.add_sub_cancel] using
      (WorldSource.Eval.pure (call:=TextWorldIO.external p fault) (p:=p)
        (stream:=stream) run)
  have secondStep := PrintSRead.source_putchar p fault pureCall s a ds slot k first hk hd stream
  have secondStep' : WorldSource.Eval Header.layout pureCall (TextWorldIO.external p fault) p
      output ⟨frame s a ds slot k first,stream⟩
      ⟨frame s a ds slot k first,nextStream fault s a ds slot k first stream⟩
      (signed32 (if fault.succeed "putchar" ⟨frame s a ds slot k first,stream⟩
        then 48+ds[k] else -1)) := by
    simpa only [output,nextStream,List.getElem?_eq_getElem hk,Option.getD_some] using secondStep
  apply Loops.StmtRun.sequence
    (Loops.SeqRun.next (Loops.StmtRun.evaluate firstStep)
      (Loops.SeqRun.next (Loops.StmtRun.evaluate secondStep') (Loops.SeqRun.nil _)))
  change (⟨frame s a ds slot k first,nextStream fault s a ds slot k first stream⟩ : World) =
    WorldSource.pop ⟨frame s a ds slot (k+1) first,stream⟩
      ⟨frame s a ds slot k first,nextStream fault s a ds slot k first stream⟩
  simp [WorldSource.pop,pop_count_frame]

theorem loop_source (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (pureCall : Machine.Call) (s : State) (a : Value) (ds : List Nat)
    (slot first : Nat) (capacity : ds.length ≤ 1024)
    (decimal : ∀ d∈ds,d < 10) (count : Nat) (within : count ≤ ds.length)
    (stream : Stream) :
    Loops.WhileRun (WorldSource.Eval Header.layout pureCall (TextWorldIO.external p fault) p)
      (WorldSource.Declare Header.layout pureCall) truth WorldSource.Scope condition iteration
      ⟨frame s a ds slot count first,stream⟩
      (.continuing ⟨frame s a ds slot 0 first,emit fault s a ds slot first count stream⟩) := by
  induction count generalizing stream with
  | zero =>
    obtain ⟨fuel,run⟩ := positive_source pureCall s a ds slot 0 first (by norm_num)
    exact Loops.WhileRun.done (WorldSource.Eval.pure run) rfl
  | succ count ih =>
    have countBound : count+1 < 2^32 := by omega
    obtain ⟨fuel,run⟩ := positive_source pureCall s a ds slot (count+1) first countBound
    have hk : count < ds.length := by omega
    have hd : ds[count] < 10 := decimal _ (List.getElem_mem hk)
    exact Loops.WhileRun.next (WorldSource.Eval.pure run) rfl
      (iteration_source p fault pureCall s a ds slot count first hk hd countBound stream)
      (ih (by omega) (nextStream fault s a ds slot count first stream))

end ScopedIO.PrintSReverse

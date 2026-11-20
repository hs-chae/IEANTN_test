/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCFunction
import RamanujanPV.QuotientDriverInit

/-! Stateful driver/callee and addressable-word/stdio semantics. Internal calls
are checked registry AST executions and carry their updated heap. No function
name is interpreted as a mathematical prime-count oracle. Generic stdio steps
describe both success and failure; successful effects must be derived from the
actual driver's branches. Physical compiler/ABI/stdio association is external. -/
namespace RamanujanPV.QuotientDriverExecution
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientDriverSource QuotientDriverInit
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Registry := String → Option Function

def registry : Registry := fun name =>
  if name = QuotientCSourceV2.countFunction.name then some QuotientCSourceV2.countFunction
  else if name = QuotientCSourceV2.sqrtFunction.name then some QuotientCSourceV2.sqrtFunction
  else none

def argument (type : String) (value : Value) : Option Value :=
  if type = "uint64_t" then uint64 value
  else if type = "uint64_t*" then match value with
    | .ptr address => if address < modulus then some (.ptr address) else none
    | _ => none
  else none

def parameters : List (String × String) → List Value → Env → Option Env
  | [], [], env => some env
  | (type,name)::ps, value::vs, env => do
      if (env name).isSome then none else
        parameters ps vs (bind env name (← argument type value))
  | _, _, _ => none

/-- Generic stateful source call rule. The callee's body is selected by the
registry; typed arguments build its real parameter environment. The post-call
heap is the callee's actual post-heap, never the caller's old heap by fiat. -/
inductive InternalCall (functions : Registry) (service : Service) :
    String → List Value → Heap → Heap → Value → Prop
  | execute {name args before after env value function}
      (lookup : functions name = some function)
      (arguments : parameters function.parameters args emptyEnv = some env)
      (body : Run service function.body ⟨env,before⟩ (.returned after value)) :
      InternalCall functions service name args before after.heap value

theorem driver_arguments (layout : Layout) :
    parameters QuotientCSourceV2.countFunction.parameters
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] emptyEnv =
      some (QuotientCFunctionPrefix.input input capacity layout.smallBase layout.largeBase
        (initializedHeap layout)).env := by
  have hp := source_pointer_values_valid layout
  simp [parameters,argument,QuotientCSourceV2.countFunction,emptyEnv,uint64,Value.scalar,
    input,capacity,modulus,ValidValue] at hp ⊢
  simp [QuotientCFunctionPrefix.input]

theorem driver_buffers (layout : Layout) :
    QuotientCInit.Buffers (initializedHeap layout) layout.smallBase layout.largeBase input.sqrt := by
  exact ⟨layout.distinct,zeroBlock smallArray,zeroBlock largeArray,initialized_small layout,
    initialized_large layout,source_call_domain.2.2.1,source_call_domain.2.2.1⟩

/-- Every completed registry-dispatched actual counter call has the actual
mathematical count, by the source-body proof and source execution determinism. -/
theorem driver_call_correct (layout : Layout) {heap : Heap} {value : Value}
    (call : InternalCall registry QuotientSqrtExecute.service "rpc_quotient_count"
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase]
      (initializedHeap layout) heap value) :
    value = .u64 (Nat.primeCounting input) ∧ Owned heap := by
  cases call with
  | execute lookup arguments body =>
      have hf : _ = QuotientCSourceV2.countFunction := by simpa [registry] using lookup.symm
      subst_vars
      have he := driver_arguments layout
      rw [he] at arguments
      have henv := Option.some.inj arguments
      subst_vars
      have result := QuotientCFunction.completed_execution_correct
        source_call_domain.1 source_call_domain.2.1 source_call_domain.2.2.1
        source_call_domain.2.2.2.2 (initialized_owned layout) (driver_buffers layout) body
      exact ⟨result.1,result.2.2⟩

/-- Byte sequence of one uint64 object under the explicitly selected 8-bit,
little-endian ABI. This is an ABI choice, not a mathematical count premise. -/
def wordBytes (word : Nat) : List Nat := (List.range 8).map (fun i => (word / 256^i) % 256)

theorem wordBytes_length (word : Nat) : (wordBytes word).length = 8 := by simp [wordBytes]

theorem wordBytes_bounded (word : Nat) : ∀ byte ∈ wordBytes word, byte < 256 := by
  intro byte hbyte
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbyte
  exact Nat.mod_lt _ (by norm_num)

/-- Application local-object creation, used by the source uint64 declaration.
The initializer value is stored; zero initialization is not assumed. -/
def localWord (word : Nat) : Block := ⟨1,fun _ => word⟩
def allocateLocal (heap : Heap) (address word : Nat) : Heap :=
  Function.update heap address (some (localWord word))

theorem allocated_local_read {heap : Heap} {address word : Nat}
    (aligned : address%8 = 0) (bounded : address+8 ≤ modulus) (valid : word < modulus) :
    QuotientCMachine.read (allocateLocal heap address word) address 0 = some (.u64 word) := by
  exact read_of_block (by simp [allocateLocal]) aligned (by norm_num [localWord])
    (by simpa using bounded) valid

structure World where
  buffered : List Nat
  committed : List Nat
  deriving Repr, DecidableEq

/-- Generic one-object fwrite contract for an addressable eight-byte uint64
object. Failure is retained and may expose an arbitrary partial write. Success
appends the bytes actually read at the supplied pointer. -/
inductive Fwrite : Heap → Nat → World → World → Nat → Prop
  | complete {heap address before word}
      (read : QuotientCMachine.read heap address 0 = some (.u64 word)) :
      Fwrite heap address before
        ⟨before.buffered ++ wordBytes word,before.committed⟩ 1
  | failed (heap : Heap) (address : Nat) (before after : World) :
      Fwrite heap address before after 0

/-- Generic fflush contract: only a successful explicit flush commits the
buffer. Negative C error results are represented as signed integers. -/
inductive Fflush : World → World → Int → Prop
  | complete (before : World) : Fflush before ⟨[],before.committed ++ before.buffered⟩ 0
  | failed (before after : World) (code : Int) (nonzero : code ≠ 0) :
      Fflush before after code

theorem successful_fwrite {heap : Heap} {address word : Nat} {before after : World}
    (read : QuotientCMachine.read heap address 0 = some (.u64 word))
    (step : Fwrite heap address before after 1) :
    after.buffered = before.buffered ++ wordBytes word ∧ after.committed = before.committed := by
  cases step with
  | complete other =>
      have hw := Option.some.inj (other.symm.trans read)
      cases hw
      exact ⟨rfl,rfl⟩

theorem successful_fflush {before after : World} (step : Fflush before after 0) :
    after.buffered = [] ∧ after.committed = before.committed ++ before.buffered := by
  cases step with
  | complete => exact ⟨rfl,rfl⟩
  | failed _ _ _ nonzero => exact (nonzero rfl).elim

#print axioms driver_call_correct
#print axioms allocated_local_read
#print axioms successful_fwrite
#print axioms successful_fflush
end RamanujanPV.QuotientDriverExecution

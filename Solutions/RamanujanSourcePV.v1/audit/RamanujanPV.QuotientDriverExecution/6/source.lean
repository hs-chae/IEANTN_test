/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCFunction
import RamanujanPV.QuotientCHeapShape
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
  simp [QuotientCFunctionPrefix.input,hp.1,hp.2]

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
      have hc : registry "rpc_quotient_count" = some QuotientCSourceV2.countFunction := rfl
      rw [hc] at lookup
      have hf := Option.some.inj lookup
      subst_vars
      have he := driver_arguments layout
      rw [he] at arguments
      have henv := Option.some.inj arguments
      subst_vars
      have result := QuotientCFunction.completed_execution_correct
        source_call_domain.1 source_call_domain.2.1 source_call_domain.2.2.1
        source_call_domain.2.2.2.2 (initialized_owned layout) (driver_buffers layout) body
      exact ⟨result.1,result.2.2⟩

theorem driver_call_correct_of_buffers (layout : Layout) {before after : Heap} {value : Value}
    (owned : Owned before)
    (buffers : QuotientCInit.Buffers before layout.smallBase layout.largeBase input.sqrt)
    (call : InternalCall registry QuotientSqrtExecute.service "rpc_quotient_count"
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] before after value) :
    value = .u64 (Nat.primeCounting input) ∧ Owned after ∧ SameShape before after := by
  cases call with
  | execute lookup arguments body =>
      have hc : registry "rpc_quotient_count" = some QuotientCSourceV2.countFunction := rfl
      rw [hc] at lookup
      have hf := Option.some.inj lookup
      subst_vars
      have he : parameters QuotientCSourceV2.countFunction.parameters
          [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] emptyEnv =
          some (QuotientCFunctionPrefix.input input capacity layout.smallBase layout.largeBase before).env :=
        driver_arguments layout
      rw [he] at arguments
      have henv := Option.some.inj arguments
      subst_vars
      have result := QuotientCFunction.completed_execution_correct
        source_call_domain.1 source_call_domain.2.1 source_call_domain.2.2.1
        source_call_domain.2.2.2.2 owned buffers body
      exact ⟨result.1,result.2.2,QuotientCHeapShape.run_shape body⟩

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
  exact read_of_block (heap := allocateLocal heap address word) (base := address) (index := 0)
    (block := localWord word) (by simp [allocateLocal]) aligned (by norm_num [localWord])
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
  | failed _ _ nonzero => exact (nonzero rfl).elim

inductive DriverValue where
  | core (value : Value)
  | signed (value : Int)
  deriving Repr, DecidableEq

def DriverValue.integer : DriverValue → Option Int
  | .core (.u64 n) | .core (.i32 n) | .core (.i64 n) => some n
  | .signed n => some n
  | _ => none

def DriverValue.unsigned : DriverValue → Bool
  | .core (.u64 _) => true
  | _ => false

/-- The selected actual != expressions use ordinary C integer promotions.
In a mixed unsigned64 comparison both operands are reduced modulo2^64;
fflush's signed negative failure code is compared as an integer with zero. -/
def notEqual (left right : DriverValue) : Option DriverValue := do
  let a ← left.integer
  let b ← right.integer
  let different := if left.unsigned || right.unsigned then
    a % (modulus : Int) != b % (modulus : Int) else a != b
  return .core (.i32 (if different then 1 else 0))

def driverTruth (value : DriverValue) : Bool := match value with
  | .core (.ptr address) => address != 0
  | _ => match value.integer with | some n => n != 0 | none => false

abbrev DriverEnv := String → Option DriverValue

def coreEnv (env : DriverEnv) : Env := fun name => do
  let .core value ← env name | none
  return value

def coreArguments : List DriverValue → Option (List Value)
  | [] => some []
  | .core value :: rest => (fun tail => value :: tail) <$> coreArguments rest
  | _ => none

structure DriverState where
  env : DriverEnv
  locations : List (String × Nat)
  heap : Heap
  world : World

def location (s : DriverState) (name : String) : Option Nat := (s.locations.lookup name)

def declareLocal (s : DriverState) (name : String) (address value : Nat) : DriverState :=
  {s with
    env := Function.update s.env name (some (.core (.u64 value)))
    locations := (name,address) :: s.locations
    heap := allocateLocal s.heap address value}

def reserveLocal (s : DriverState) (name : String) (address uninitialized : Nat) : DriverState :=
  {s with
    locations := (name,address) :: s.locations
    heap := allocateLocal s.heap address uninitialized}

def initializeReserved (s : DriverState) (name : String) (value : Nat) (heap : Heap) : DriverState :=
  {s with
    env := Function.update s.env name (some (.core (.u64 value)))
    heap := heap}

/-- Removing a source block's fresh automatic objects ends their lifetimes;
the actual stream effects and global-array contents remain. -/
def closeDriverScope (before after : DriverState) : DriverState :=
  {after with
    env := fun name => if (before.env name).isSome then after.env name else none
    locations := before.locations
    heap := fun address => if (after.locations.filter (fun pair =>
      !(before.locations.any (fun old => old.1 == pair.1)))).any (fun pair => pair.2 == address)
      then none else after.heap address}

mutual
  /-- Generic stateful expressions for the driver's selected C subset. The
  pure rule rejects calls because noCalls has no responses. Internal and stdio
  call effects therefore cannot be hidden inside an unevaluated pure oracle. -/
  inductive DriverEval (stdoutToken : Nat) : Expr → DriverState → DriverState → DriverValue → Prop
    | pure {expression state value}
        (evaluated : evalPure QuotientSqrtExecute.noCalls state.heap (coreEnv state.env) 8 expression = some value) :
        DriverEval stdoutToken expression state state (.core value)
    | address {name state address word}
        (found : location state name = some address)
        (typed : state.env name = some (.core (.u64 word)))
        (storage : QuotientCMachine.read state.heap address 0 = some (.u64 word)) :
        DriverEval stdoutToken (.unary "&" (.var name)) state state (.core (.ptr address))
    | internal {name expressions before arguments values raw after heap value}
        (evaluated : DriverArgs stdoutToken expressions before arguments values)
        (converted : coreArguments values = some raw)
        (called : InternalCall registry QuotientSqrtExecute.service name raw arguments.heap heap value)
        (post : after = {arguments with heap := heap}) :
        DriverEval stdoutToken (.call (.var name) expressions) before after (.core value)
    | fwrite {expressions before arguments values address size count after returned world}
        (evaluated : DriverArgs stdoutToken expressions before arguments values)
        (actual : values = [.core (.ptr address),.core size,.core count,.core (.ptr stdoutToken)])
        (sizeCast : uint64 size = some (.u64 8))
        (countCast : uint64 count = some (.u64 1))
        (effect : Fwrite arguments.heap address arguments.world world returned)
        (post : after = {arguments with world := world}) :
        DriverEval stdoutToken (.call (.var "fwrite") expressions) before after (.core (.u64 returned))
    | fflush {expressions before arguments values after returned world}
        (evaluated : DriverArgs stdoutToken expressions before arguments values)
        (actual : values = [.core (.ptr stdoutToken)])
        (effect : Fflush arguments.world world returned)
        (post : after = {arguments with world := world}) :
        DriverEval stdoutToken (.call (.var "fflush") expressions) before after (.signed returned)
    | ne {left right before middle after a b result}
        (lhs : DriverEval stdoutToken left before middle a)
        (rhs : DriverEval stdoutToken right middle after b)
        (compared : notEqual a b = some result) :
        DriverEval stdoutToken (.binary "!=" left right) before after result

  inductive DriverArgs (stdoutToken : Nat) :
      List Expr → DriverState → DriverState → List DriverValue → Prop
    | nil (state) : DriverArgs stdoutToken [] state state []
    | cons {expression rest before middle after value values}
        (head : DriverEval stdoutToken expression before middle value)
        (tail : DriverArgs stdoutToken rest middle after values) :
        DriverArgs stdoutToken (expression::rest) before after (value::values)
end

/-- Generic scalar local declaration. A real fresh aligned disjoint one-word
object is allocated and initialized from the expression's actual return value. -/
inductive DriverDeclare (stdoutToken : Nat) : List Decl → DriverState → DriverState → Prop
  | nil (s) : DriverDeclare stdoutToken [] s s
  | cons {name rhs rest before reserved middle after final raw value address uninitialized written}
      (uninitializedBound : uninitialized < modulus)
      (freshName : before.env name = none)
      (freshLocation : location before name = none)
      (freshAddress : before.heap address = none)
      (aligned : address % 8 = 0)
      (bounded : address + 8 ≤ modulus)
      (apart : ∀ base block, before.heap base = some block →
        address+8 ≤ base ∨ base+8*block.extent ≤ address)
      (reservedObject : reserved = reserveLocal before name address uninitialized)
      (expression : DriverEval stdoutToken rhs reserved middle (.core raw))
      (converted : uint64 raw = some (.u64 value))
      (valueBound : value < modulus)
      (actualStore : write middle.heap address 0 value = some written)
      (initialized : after = initializeReserved middle name value written)
      (restRun : DriverDeclare stdoutToken rest after final) :
      DriverDeclare stdoutToken (⟨"uint64_t",name,some rhs⟩::rest) before final

def closeDriverFlow (before : DriverState) : LCMSourcePV.ASTLoops.Flow DriverState DriverValue →
    LCMSourcePV.ASTLoops.Flow DriverState DriverValue
  | .continuing after => .continuing (closeDriverScope before after)
  | .returned after value => .returned (closeDriverScope before after) value

def DriverScope (before : DriverState) (inner outer : LCMSourcePV.ASTLoops.Flow DriverState DriverValue) : Prop :=
  outer = closeDriverFlow before inner

abbrev DriverRun (stdoutToken : Nat) :=
  StmtRun (DriverEval stdoutToken) (DriverDeclare stdoutToken) driverTruth DriverScope

abbrev DriverSeqRun (stdoutToken : Nat) :=
  SeqRun (DriverEval stdoutToken) (DriverDeclare stdoutToken) driverTruth DriverScope

def initialDriver (layout : Layout) (stdoutToken : Nat) (world : World) : DriverState where
  env := fun name => if name = "stdout" then some (.core (.ptr stdoutToken))
    else (globalEnv layout name).map DriverValue.core
  locations := []
  heap := initializedHeap layout
  world := world

theorem notEqual_write_success : notEqual (.core (.u64 1)) (.core (.i32 1)) = some (.core (.i32 0)) := by
  norm_num [notEqual,DriverValue.integer,DriverValue.unsigned,modulus]

theorem notEqual_flush_success : notEqual (.signed 0) (.core (.i32 0)) = some (.core (.i32 0)) := by
  norm_num [notEqual,DriverValue.integer,DriverValue.unsigned,modulus]

#print axioms driver_call_correct
#print axioms allocated_local_read
#print axioms successful_fwrite
#print axioms successful_fflush
end RamanujanPV.QuotientDriverExecution

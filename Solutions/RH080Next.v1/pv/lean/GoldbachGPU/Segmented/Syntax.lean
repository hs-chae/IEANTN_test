import Init

namespace GoldbachGPU.Segmented.Code

/-- All loops, casts and memory events in the supported kernels are explicit. -/
inductive R32 where | prime | word | witness | temporary deriving DecidableEq, Repr
inductive R64 where | thread | index | cursor | value | remainder | delta | target | query
  deriving DecidableEq, Repr
inductive Buffer where | base | search | composite | witnesses deriving DecidableEq, Repr
inductive Param where
  | baseStart | baseBatch | candidateLo | candidateCount | bitmapWords
  | targetHi | targetCount | searchCount | cutoff
  deriving DecidableEq, Repr
inductive Builtin where | block | blockSize | lane deriving DecidableEq, Repr
inductive Op64 where | add | sub | mul | div | rem deriving DecidableEq, Repr

mutual
inductive E32 where
  | literal : UInt32 → E32
  | register : R32 → E32
  | builtin : Builtin → E32
  | narrow : E64 → E32
  | bitAnd : E32 → E32 → E32
  | bitOr : E32 → E32 → E32
  | shiftLeft : E32 → E64 → E32
  | shiftRight : E32 → E64 → E32
  deriving Repr
inductive E64 where
  | literal : UInt64 → E64
  | register : R64 → E64
  | parameter : Param → E64
  | widen : E32 → E64
  | binary : Op64 → E64 → E64 → E64
  deriving Repr
end

inductive Condition where
  | equal64 : E64 → E64 → Condition
  | less64 : E64 → E64 → Condition
  | equal32 : E32 → E32 → Condition
  | conjunction : Condition → Condition → Condition
  deriving Repr

inductive Instr where
  | set32 : R32 → E32 → Nat → Instr
  | set64 : R64 → E64 → Nat → Instr
  | branch : Condition → Nat → Nat → Instr
  | load : R32 → Buffer → E64 → Nat → Instr
  | store : Buffer → E64 → E32 → Nat → Instr
  | atomicOr : Buffer → E64 → E32 → Nat → Instr
  | halt : Instr
  deriving Repr

abbrev Program := Array Instr

structure Registers where
  small : R32 → UInt32
  wide : R64 → UInt64

def initialRegisters : Registers := ⟨fun _ => 0, fun _ => 0⟩

def Registers.set32 (r : Registers) (key : R32) (value : UInt32) : Registers :=
  {r with small := fun k => if k = key then value else r.small k}

def Registers.set64 (r : Registers) (key : R64) (value : UInt64) : Registers :=
  {r with wide := fun k => if k = key then value else r.wide k}

structure Environment where
  parameters : Param → UInt64
  builtins : Builtin → UInt32

def evalOp64 (op : Op64) (a b : UInt64) : Option UInt64 :=
  match op with
  | .add => some (a+b)
  | .sub => some (a-b)
  | .mul => some (a*b)
  | .div => if b = 0 then none else some (a/b)
  | .rem => if b = 0 then none else some (a%b)

mutual
def eval32 (env : Environment) (r : Registers) : E32 → Option UInt32
  | .literal v => some v
  | .register k => some (r.small k)
  | .builtin k => some (env.builtins k)
  | .narrow e => (eval64 env r e).map UInt64.toUInt32
  | .bitAnd a b => do return (← eval32 env r a) &&& (← eval32 env r b)
  | .bitOr a b => do return (← eval32 env r a) ||| (← eval32 env r b)
  | .shiftLeft a b => do
    let v ← eval32 env r a
    let shift ← eval64 env r b
    if shift.toNat < 32 then some (v <<< UInt32.ofNat shift.toNat) else none
  | .shiftRight a b => do
    let v ← eval32 env r a
    let shift ← eval64 env r b
    if shift.toNat < 32 then some (v >>> UInt32.ofNat shift.toNat) else none
def eval64 (env : Environment) (r : Registers) : E64 → Option UInt64
  | .literal v => some v
  | .register k => some (r.wide k)
  | .parameter k => some (env.parameters k)
  | .widen e => (eval32 env r e).map UInt32.toUInt64
  | .binary op a b => do evalOp64 op (← eval64 env r a) (← eval64 env r b)
end

def evalCondition (env : Environment) (r : Registers) : Condition → Option Bool
  | .equal64 a b => do return (← eval64 env r a) == (← eval64 env r b)
  | .less64 a b => do return (← eval64 env r a) < (← eval64 env r b)
  | .equal32 a b => do return (← eval32 env r a) == (← eval32 env r b)
  | .conjunction a b => do return (← evalCondition env r a) && (← evalCondition env r b)

end GoldbachGPU.Segmented.Code

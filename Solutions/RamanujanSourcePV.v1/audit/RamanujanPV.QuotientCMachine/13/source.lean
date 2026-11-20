/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CArithmetic
import Mathlib.Logic.Function.Basic

/-! Generic operational semantics for the selected C uint64/pointer subset.
The source has ordinary C integer literals: 2000000000000 is a signed64
literal, and its comparison with uint64 n uses the usual unsigned conversion.
Heap blocks model distinct OWNED uint64 allocations with actual base addresses;
the application refinement must supply Owned, capacity and source-call association.
No function name or quotient-sieve result is interpreted specially here. -/
namespace RamanujanPV.QuotientCMachine
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 2000000

def modulus : Nat := 2^64

inductive Value where
  | u64 (bits : Nat)
  | i32 (bits : Nat)
  | i64 (bits : Nat)
  | ptr (address : Nat)
  deriving Repr, DecidableEq

def Value.bits : Value → Nat
  | .u64 n | .i32 n | .i64 n | .ptr n => n

def Value.scalar : Value → Option Nat
  | .u64 n | .i32 n | .i64 n => some n
  | .ptr _ => none

def ValidValue : Value → Prop
  | .u64 n | .ptr n => n < modulus
  | .i32 n => n < 2^31
  | .i64 n => n < 2^63

/-- Selected source literals are nonnegative unsuffixed C decimal literals. -/
def literal (n : Nat) : Option Value :=
  if n < 2^31 then some (.i32 n)
  else if n < 2^63 then some (.i64 n)
  else none

def truth (v : Value) : Bool := v.bits != 0

def uint64 (v : Value) : Option Value := do return .u64 ((←v.scalar) % modulus)

def unsignedCommon (a b : Value) : Bool := match a,b with
  | .u64 _,_ | _,.u64 _ => true
  | _,_ => false

def longCommon (a b : Value) : Bool := match a,b with
  | .i64 _,_ | _,.i64 _ => true
  | _,_ => false

def packArithmetic (a b : Value) (n : Nat) : Option Value :=
  if unsignedCommon a b then some (.u64 (n % modulus))
  else if longCommon a b then if n < 2^63 then some (.i64 n) else none
  else if n < 2^31 then some (.i32 n) else none

/-- All selected signed inputs are nonnegative. Negative or overflowing signed
arithmetic is rejected; unsigned arithmetic has the C modulo2^64 semantics. -/
def binary (op : String) (a b : Value) : Option Value := do
  let x ← a.scalar
  let y ← b.scalar
  if op == "+" then packArithmetic a b (x+y)
  else if op == "-" then
    if unsignedCommon a b then some (.u64 ((x+modulus-y)%modulus))
    else if y  ≤  x then packArithmetic a b (x-y) else none
  else if op == "*" then packArithmetic a b (x*y)
  else if op == "/" then if y=0 then none else packArithmetic a b (x/y)
  else if op == "%" then if y=0 then none else packArithmetic a b (x%y)
  else if op == "<" then some (.i32 (if x < y then 1 else 0))
  else if op == "<=" then some (.i32 (if x ≤ y then 1 else 0))
  else if op == ">" then some (.i32 (if y < x then 1 else 0))
  else if op == "==" then some (.i32 (if x=y then 1 else 0))
  else none

abbrev Env := String → Option Value
abbrev Service := String → List Value → Option Value

def bind (env : Env) (name : String) (v : Value) : Env := Function.update env name (some v)
def emptyEnv : Env := fun _ => none

structure Block where
  extent : Nat
  words : Nat → Nat

abbrev Heap := Nat → Option Block

/-- Byte-level applicability for the word block representation. In particular,
overlapping source arrays cannot be treated as independent mathematical tables. -/
def Owned (heap : Heap) : Prop :=
  (∀ base block, heap base = some block → base % 8 = 0 ∧
    base + 8*block.extent  ≤  modulus) ∧
  (∀ a b A B, heap a = some A → heap b = some B → a  ≠  b →
    a + 8*A.extent  ≤  b ∨ b + 8*B.extent  ≤  a)

structure State where
  env : Env
  heap : Heap

def read (heap : Heap) (base index : Nat) : Option Value := do
  let block ← heap base
  if base % 8 = 0 ∧ index < block.extent ∧
      base + 8*index + 8  ≤  modulus ∧ block.words index < modulus then
    some (.u64 (block.words index))
  else none

def write (heap : Heap) (base index value : Nat) : Option Heap := do
  let block ← heap base
  if base % 8 = 0 ∧ index < block.extent ∧
      base + 8*index + 8  ≤  modulus ∧ value < modulus then
    some (Function.update heap base (some {block with words := Function.update block.words index value}))
  else none

def evalPure (call : Service) (heap : Heap) (env : Env) : Nat → Expr → Option Value
  | 0,_ => none
  | fuel+1,.nat n => literal n
  | fuel+1,.var name => env name
  | fuel+1,.index base index => do
      let .ptr address ← evalPure call heap env fuel base | none
      let i ← evalPure call heap env fuel index
      read heap address (←i.scalar)
  | fuel+1,.binary op a b => do
      binary op (←evalPure call heap env fuel a) (←evalPure call heap env fuel b)
  | fuel+1,.call (.var name) args => do call name (←args.mapM (evalPure call heap env fuel))
  | _,_ => none

def assign (env : Env) (name : String) (value : Value) : Option Env := do
  let .u64 _ ← env name | none
  let word ← uint64 value
  return bind env name word

/-- The selected source takes no local addresses and declares fresh names in
every actual lexical block. These semantics reject accidental name shadowing. -/
def declare (call : Service) (ds : List Decl) (s : State) : Option State :=
  ds.foldlM (fun t d => do
    if d.type != "uint64_t" then none else
      if (t.env d.name).isSome then none else
        let expression ← d.value
        let v ← evalPure call t.heap t.env 8 expression
        let word ← uint64 v
        return {t with env := bind t.env d.name word}) s

def eval (call : Service) (s : State) : Expr → Option (State × Value)
  | .binary "=" (.var name) rhs => do
      let v ← evalPure call s.heap s.env 8 rhs
      let env ← assign s.env name v
      let word ← env name
      return ({s with env:=env},word)
  | .binary "=" (.index base index) rhs => do
      let .ptr address ← evalPure call s.heap s.env 8 base | none
      let i ← evalPure call s.heap s.env 8 index
      let .u64 word ← uint64 (←evalPure call s.heap s.env 8 rhs) | none
      let heap ← write s.heap address (←i.scalar) word
      return ({s with heap:=heap},.u64 word)
  | .unary "++" (.var name) => do
      let .u64 old ← s.env name | none
      let v := (old+1)%modulus
      return ({s with env:=bind s.env name (.u64 v)},.u64 v)
  | .unary "--" (.var name) => do
      let .u64 old ← s.env name | none
      let v := (old+modulus-1)%modulus
      return ({s with env:=bind s.env name (.u64 v)},.u64 v)
  | e => do return (s,←evalPure call s.heap s.env 8 e)

/-- Discard newly declared block locals while retaining assignments to the
surrounding scope. Fresh declarations are enforced in declare. -/
def closeScope (before after : State) : State :=
  {after with env:=fun name => if (before.env name).isSome then after.env name else none}

abbrev Flow := LCMSourcePV.ASTLoops.Flow State Value

def closeFlow (before : State) : Flow → Flow
  | .continuing t => .continuing (closeScope before t)
  | .returned t value => .returned (closeScope before t) value

def Scope (before : State) (inner outer : Flow) : Prop := outer = closeFlow before inner

def Eval (call : Service) (e : Expr) (s t : State) (value : Value) : Prop :=
  eval call s e = some (t,value)
def Declare (call : Service) (ds : List Decl) (s t : State) : Prop := declare call ds s = some t
abbrev Run (call : Service) := LCMSourcePV.ASTLoops.StmtRun (Eval call) (Declare call) truth Scope
abbrev SeqRun (call : Service) := LCMSourcePV.ASTLoops.SeqRun (Eval call) (Declare call) truth Scope
abbrev ForRun (call : Service) := LCMSourcePV.ASTLoops.ForRun (Eval call) (Declare call) truth Scope
abbrev WhileRun (call : Service) := LCMSourcePV.ASTLoops.WhileRun (Eval call) (Declare call) truth Scope

@[simp] theorem bind_same (env : Env) (name : String) (v : Value) : bind env name v name = some v := by
  simp [bind]
@[simp] theorem bind_other (env : Env) {name other : String} (h : other  ≠  name) (v : Value) :
    bind env name v other = env other := by simp [bind, h]

/-- The actual large source literal is not truncated to signed32. -/
theorem literal_two_trillion : literal 2000000000000 = some (.i64 2000000000000) := by
  norm_num [literal]

theorem uint64_of_u64 {n : Nat} (hn : n < modulus) : uint64 (.u64 n) = some (.u64 n) := by
  simp [uint64,Value.scalar,Nat.mod_eq_of_lt hn]

/-- Primitive uint64 arithmetic applicability lemmas. These reduce the generic
modular operations only after the application supplies the actual range bounds. -/
theorem binary_u64_add {a b : Nat} (h : a+b < modulus) :
    binary "+" (.u64 a) (.u64 b) = some (.u64 (a+b)) := by
  simp [binary,Value.scalar,packArithmetic,unsignedCommon,Nat.mod_eq_of_lt h]
theorem binary_u64_mul {a b : Nat} (h : a*b < modulus) :
    binary "*" (.u64 a) (.u64 b) = some (.u64 (a*b)) := by
  simp [binary,Value.scalar,packArithmetic,unsignedCommon,Nat.mod_eq_of_lt h]
theorem binary_u64_sub {a b : Nat} (hle : b  ≤  a) (h : a < modulus) :
    binary "-" (.u64 a) (.u64 b) = some (.u64 (a-b)) := by
  have heq : a+modulus-b=(a-b)+modulus := by omega
  simp [binary,Value.scalar,unsignedCommon,heq,Nat.mod_eq_of_lt ((Nat.sub_le a b).trans_lt h)]
theorem binary_u64_div {a b : Nat} (hb : 0 < b) (h : a < modulus) :
    binary "/" (.u64 a) (.u64 b) = some (.u64 (a/b)) := by
  have hq : a/b < modulus := (Nat.div_le_self a b).trans_lt h
  simp [binary,Value.scalar,packArithmetic,unsignedCommon,show b ≠ 0 by omega,Nat.mod_eq_of_lt hq]

@[simp] theorem binary_u64_lt (a b : Nat) :
    binary "<" (.u64 a) (.u64 b) = some (.i32 (if a < b then 1 else 0)) := by
  simp [binary,Value.scalar]
@[simp] theorem binary_u64_le (a b : Nat) :
    binary "<=" (.u64 a) (.u64 b) = some (.i32 (if a ≤ b then 1 else 0)) := by
  simp [binary,Value.scalar]
@[simp] theorem truth_i32 (n : Nat) : truth (.i32 n) = (n != 0) := rfl

/-- A successful indexed access is fully justified by its owned block bounds. -/
theorem read_of_block {heap : Heap} {base index : Nat} {block : Block}
    (hblock : heap base=some block) (halign : base%8=0) (hindex : index < block.extent)
    (haddress : base+8*index+8  ≤  modulus) (hword : block.words index < modulus) :
    read heap base index=some (.u64 (block.words index)) := by
  simp [read,hblock,halign,hindex,haddress,hword]

theorem write_of_block {heap : Heap} {base index value : Nat} {block : Block}
    (hblock : heap base=some block) (halign : base%8=0) (hindex : index < block.extent)
    (haddress : base+8*index+8  ≤  modulus) (hword : value < modulus) :
    write heap base index value=some (Function.update heap base
      (some {block with words:=Function.update block.words index value})) := by
  simp [write,hblock,halign,hindex,haddress,hword]

/-- Only word contents change; allocation metadata and disjointness are stable. -/
def SameShape (before after : Heap) : Prop := ∀ base,
  (before base).map Block.extent = (after base).map Block.extent

lemma sameShape_old_block {before after : Heap} (shape : SameShape before after)
    {base : Nat} {block : Block} (hb : after base=some block) :
    ∃ old, before base=some old ∧ old.extent=block.extent := by
  have h := shape base
  cases hold : before base with
  | none => simp [hold,hb] at h
  | some old => exact ⟨old,rfl,by simpa [hold,hb] using h⟩

theorem owned_of_sameShape {before after : Heap} (owned : Owned before)
    (shape : SameShape before after) : Owned after := by
  constructor
  · intro base block hb
    obtain ⟨old,ho,he⟩ := sameShape_old_block shape hb
    simpa only [←he] using owned.1 base old ho
  · intro a b A B hA hB hab
    obtain ⟨oldA,ha,heA⟩ := sameShape_old_block shape hA
    obtain ⟨oldB,hb,heB⟩ := sameShape_old_block shape hB
    simpa only [←heA,←heB] using owned.2 a b oldA oldB ha hb hab

theorem word_update_sameShape {heap : Heap} {base index value : Nat} {block : Block}
    (hblock : heap base=some block) :
    SameShape heap (Function.update heap base
      (some {block with words:=Function.update block.words index value})) := by
  intro other
  by_cases h : other=base
  · subst other
    simp [hblock]
  · simp [Function.update_of_ne h]

theorem write_preserves_owned {heap after : Heap} {base index value : Nat}
    (owned : Owned heap) (written : write heap base index value=some after) : Owned after := by
  unfold write at written
  cases hb : heap base with
  | none => simp [hb] at written
  | some block =>
    rw [hb] at written
    change (if base % 8 = 0 ∧ index < block.extent ∧
      base + 8*index + 8  ≤  modulus ∧ value < modulus then
      some (Function.update heap base (some {block with words:=Function.update block.words index value}))
      else none) = some after at written
    split at written
    · have ha := Option.some.inj written
      subst after
      exact owned_of_sameShape owned (word_update_sameShape hb)
    · contradiction

/-- Lexical cleanup preserves every original binding and all heap effects. -/
theorem closeScope_heap (s t : State) : (closeScope s t).heap=t.heap := rfl

theorem closeScope_binding {s t : State} {name : String} {v : Value}
    (h : s.env name=some v) : (closeScope s t).env name=t.env name := by
  simp [closeScope,h]

theorem closeScope_fresh_binding {s t : State} {name : String}
    (h : s.env name=none) : (closeScope s t).env name=none := by
  simp [closeScope,h]

/-- Opaque compositional equations keep proof terms small: clients must not
unfold the whole fuelled evaluator beneath an opaque source-tree alias. -/
theorem pure_var (call : Service) (heap : Heap) (env : Env) (fuel : Nat) (name : String) :
    evalPure call heap env (fuel+1) (.var name)=env name := rfl

theorem pure_literal (call : Service) (heap : Heap) (env : Env) (fuel n : Nat) :
    evalPure call heap env (fuel+1) (.nat n)=literal n := rfl

theorem pure_binary (call : Service) (heap : Heap) (env : Env) (fuel : Nat)
    (op : String) (a b : Expr) :
    evalPure call heap env (fuel+1) (.binary op a b) =
      (do binary op (←evalPure call heap env fuel a) (←evalPure call heap env fuel b)) := rfl

theorem pure_index (call : Service) (heap : Heap) (env : Env) (fuel : Nat) (base index : Expr) :
    evalPure call heap env (fuel+1) (.index base index) =
      (do let .ptr address ← evalPure call heap env fuel base | none
          let i ← evalPure call heap env fuel index
          read heap address (←i.scalar)) := rfl

theorem eval_index_store (call : Service) (s : State) (base index rhs : Expr) :
    eval call s (.binary "=" (.index base index) rhs) =
      (do let .ptr address ← evalPure call s.heap s.env 8 base | none
          let i ← evalPure call s.heap s.env 8 index
          let .u64 word ← uint64 (←evalPure call s.heap s.env 8 rhs) | none
          let heap ← write s.heap address (←i.scalar) word
          return ({s with heap:=heap},.u64 word)) := rfl

theorem eval_variable_assign (call : Service) (s : State) (name : String) (rhs : Expr) :
    eval call s (.binary "=" (.var name) rhs) =
      (do let v ← evalPure call s.heap s.env 8 rhs
          let env ← assign s.env name v
          let word ← env name
          return ({s with env:=env},word)) := rfl

theorem eval_increment (call : Service) (s : State) (name : String) :
    eval call s (.unary "++" (.var name)) =
      (do let .u64 old ← s.env name | none
          let v := (old+1)%modulus
          return ({s with env:=bind s.env name (.u64 v)},.u64 v)) := rfl

theorem eval_decrement (call : Service) (s : State) (name : String) :
    eval call s (.unary "--" (.var name)) =
      (do let .u64 old ← s.env name | none
          let v := (old+modulus-1)%modulus
          return ({s with env:=bind s.env name (.u64 v)},.u64 v)) := rfl

theorem declare_singleton (call : Service) (s : State) (name : String) (rhs : Expr) :
    declare call [⟨"uint64_t",name,some rhs⟩] s =
      (if (s.env name).isSome then none else
        do let v ← evalPure call s.heap s.env 8 rhs
           let word ← uint64 v
           return {s with env:=bind s.env name word}) := by
  simp [declare,List.foldlM]

/-- Compositional source-expression rules. Concrete application trees are
introduced only after the generic Option continuation has been discharged. -/
theorem pure_binary_of {call : Service} {heap : Heap} {env : Env} {fuel : Nat}
    {op : String} {a b : Expr} {va vb result : Value}
    (ha : evalPure call heap env fuel a = some va)
    (hb : evalPure call heap env fuel b = some vb)
    (hresult : binary op va vb = some result) :
    evalPure call heap env (fuel+1) (.binary op a b) = some result := by
  rw [pure_binary, ha, hb]
  exact hresult

theorem pure_index_of {call : Service} {heap : Heap} {env : Env} {fuel : Nat}
    {base ix : Expr} {address i : Nat} {result : Value}
    (ha : evalPure call heap env fuel base = some (.ptr address))
    (hi : evalPure call heap env fuel ix = some (.u64 i))
    (hr : read heap address i = some result) :
    evalPure call heap env (fuel+1) (.index base ix) = some result := by
  rw [pure_index, ha, hi]
  exact hr

theorem eval_index_store_of {call : Service} {s : State} {after : Heap}
    {base ix rhs : Expr} {address i value : Nat} {raw : Value}
    (ha : evalPure call s.heap s.env 8 base = some (.ptr address))
    (hi : evalPure call s.heap s.env 8 ix = some (.u64 i))
    (hv : evalPure call s.heap s.env 8 rhs = some raw)
    (hc : uint64 raw = some (.u64 value))
    (hw : write s.heap address i value = some after) :
    Eval call (.binary "=" (.index base ix) rhs) s
      {s with heap:=after} (.u64 value) := by
  unfold Eval
  rw [eval_index_store, ha, hi, hv]
  dsimp only [Bind.bind,Option.bind]
  rw [hc]
  dsimp only [Bind.bind,Option.bind,Value.scalar]
  rw [hw]
  rfl

theorem eval_lt_of {call : Service} {s : State} {a b : Expr} {x y : Nat}
    (ha : evalPure call s.heap s.env 7 a=some (.u64 x))
    (hb : evalPure call s.heap s.env 7 b=some (.u64 y)) :
    Eval call (.binary "<" a b) s s (.i32 (if x<y then 1 else 0)) := by
  have h := pure_binary_of ha hb (binary_u64_lt x y)
  unfold Eval
  change (do return (s,←evalPure call s.heap s.env 8 (.binary "<" a b))) = _
  rw [h]
  rfl

theorem eval_le_of {call : Service} {s : State} {a b : Expr} {x y : Nat}
    (ha : evalPure call s.heap s.env 7 a=some (.u64 x))
    (hb : evalPure call s.heap s.env 7 b=some (.u64 y)) :
    Eval call (.binary "<=" a b) s s (.i32 (if x≤y then 1 else 0)) := by
  have h := pure_binary_of ha hb (binary_u64_le x y)
  unfold Eval
  change (do return (s,←evalPure call s.heap s.env 8 (.binary "<=" a b))) = _
  rw [h]
  rfl

theorem eval_variable_assign_of {call : Service} {s : State}
    {name : String} {rhs : Expr} {old value : Nat} {raw : Value}
    (hp : s.env name=some (.u64 old))
    (hv : evalPure call s.heap s.env 8 rhs=some raw)
    (hc : uint64 raw=some (.u64 value)) :
    Eval call (.binary "=" (.var name) rhs) s
      {s with env:=bind s.env name (.u64 value)} (.u64 value) := by
  unfold Eval
  rw [eval_variable_assign,hv]
  dsimp only [Bind.bind,Option.bind]
  have hh : assign s.env name raw=some (bind s.env name (.u64 value)) := by
    simp only [assign,hp]
    dsimp only [Bind.bind,Option.bind]
    rw [hc]
    rfl
  rw [hh]
  dsimp only [Bind.bind,Option.bind]
  rw [bind_same]
  rfl

theorem declare_singleton_of {call : Service} {s : State}
    {name : String} {rhs : Expr} {value : Nat} {raw : Value}
    (hfresh : s.env name=none)
    (hv : evalPure call s.heap s.env 8 rhs=some raw)
    (hc : uint64 raw=some (.u64 value)) :
    Declare call [⟨"uint64_t",name,some rhs⟩] s
      {s with env:=bind s.env name (.u64 value)} := by
  unfold Declare
  rw [declare_singleton]
  simp only [hfresh,Option.isSome_none,Bool.false_eq_true,ite_false]
  rw [hv]
  dsimp only [Bind.bind,Option.bind]
  rw [hc]
  rfl

/-- Initialization may write an owned cell without reading its indeterminate
original contents. Frame equalities concern other cells only. -/
theorem write_frame_from_block {heap : Heap} {base index value : Nat} {block : Block}
    (hb : heap base=some block) (ha : base%8=0) (hi : index < block.extent)
    (haddr : base+8*index+8  ≤  modulus) (hv : value < modulus) :
    ∃ after, write heap base index value=some after ∧
      read after base index=some (.u64 value) ∧ SameShape heap after ∧
      (∀ other j, other ≠ base → read after other j=read heap other j) ∧
      (∀ j, j ≠ index → read after base j=read heap base j) := by
  let after : Heap := Function.update heap base
    (some {block with words:=Function.update block.words index value})
  refine ⟨after,write_of_block hb ha hi haddr hv,?_,word_update_sameShape hb,?_,?_⟩
  · have h := read_of_block (heap:=after) (base:=base) (index:=index)
      (block:={block with words:=Function.update block.words index value})
      (by simp [after]) ha hi haddr (by simpa using hv)
    simpa using h
  · intro other j hother
    simp only [read,after,Function.update_of_ne hother]
  · intro j hji
    simp [read,after,hb,Function.update_of_ne hji]

/-- A syntactic depth check for the actual source trees. All checks are
kernel computations on the AST; they do not stand for native execution. -/
def exprWithin : Nat → Expr → Bool
  | 0,_ => false
  | k+1,.nat _ | k+1,.var _ => true
  | k+1,.unary _ a | k+1,.post _ a | k+1,.cast _ a | k+1,.field _ a _ => exprWithin k a
  | k+1,.binary _ a b | k+1,.index a b => exprWithin k a && exprWithin k b
  | k+1,.call f args => exprWithin k f && args.all (exprWithin k)
  | k+1,.record fields => fields.all (exprWithin k)

def stmtWithin (expressionFuel : Nat) : Nat → Stmt → Bool
  | 0,_ => false
  | k+1,.skip => true
  | k+1,.sequence body => body.all (stmtWithin expressionFuel k)
  | k+1,.declare ds => ds.all (fun d => match d.value with
      | none => true | some e => exprWithin expressionFuel e)
  | k+1,.eval e | k+1,.returnStmt e => exprWithin expressionFuel e
  | k+1,.branch cond yes no => exprWithin expressionFuel cond &&
      stmtWithin expressionFuel k yes && stmtWithin expressionFuel k no
  | k+1,.forLoop init cond step body => stmtWithin expressionFuel k init &&
      (match cond with | none => true | some e => exprWithin expressionFuel e) &&
      exprWithin expressionFuel step && stmtWithin expressionFuel k body
  | k+1,.whileLoop cond body => exprWithin expressionFuel cond && stmtWithin expressionFuel k body

#print axioms write_preserves_owned
#print axioms literal_two_trillion
end RamanujanPV.QuotientCMachine

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapAST
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RH080Next.FapPV.Execution
open GoldbachDirect

/-! A deliberately small, typed scalar-C execution model. All numeric application
variables/parameters/results are uint64_t. Unsupported operations fail; division
by zero and unsigned underflow/overflow fail, rather than being silently assumed
safe. The present application never needs wrapped results. Function calls resolve
actual program ASTs; no rule recognizes a whole selected application function.
The printf host harness is linked separately to the pure numerical function.
-/

abbrev Env := List (String × Nat)
def wordLimit : Nat := 2^64
def lookup (env : Env) (name : String) : Option Nat :=
  (env.find? (fun item => item.1 == name)).map Prod.snd

def assign : Env → String → Nat → Option Env
  | [], _, _ => none
  | (key,value)::rest, name, next =>
    if key = name then some ((key,next)::rest)
    else ((key,value)::·) <$> assign rest name next

def checked (n : Nat) : Option Nat := if n < wordLimit then some n else none

def binary (op : Binary) (a b : Nat) : Option Nat :=
  match op with
  | .add => checked (a+b)
  | .sub => if b ≤ a then some (a-b) else none
  | .mul => checked (a*b)
  | .div => if b=0 then none else some (a/b)
  | .mod => if b=0 then none else some (a%b)
  | .eq => some (if a=b then 1 else 0)
  | .ne => some (if a=b then 0 else 1)
  | .lt => some (if a<b then 1 else 0)
  | .le => some (if a≤b then 1 else 0)
  | .gt => some (if b<a then 1 else 0)
  | .ge => some (if b≤a then 1 else 0)
  | _ => none

inductive Flow where
  | continuing (env : Env)
  | returned (value : Nat)
  deriving Repr, DecidableEq

def closeScope (before : Env) : Flow → Flow
  | .continuing after => .continuing (after.drop (after.length-before.length))
  | .returned value => .returned value

def functions : List Function := RH080Next.FapPV.program.filterMap fun t =>
  match t with | .function f => some f | _ => none

mutual
  def expr : Nat → Env → Expr → Option Nat
    | 0, _, _ => none
    | n+1, env, .literal (.integer value _) => checked value
    | n+1, env, .variable name => lookup env name
    | n+1, env, .paren value => expr n env value
    | n+1, env, .cast .ull value => expr n env value
    | n+1, env, .cast .u64 value => expr n env value
    | n+1, env, .binary op left right => do
        let a ← expr n env left
        let b ← expr n env right
        binary op a b
    | n+1, env, .call name arguments => do
        let values ← args n env arguments
        call n name values
    | _, _, _ => none

  def args : Nat → Env → List Expr → Option (List Nat)
    | 0, _, _ => none
    | _+1, _, [] => some []
    | n+1, env, value::rest => do
        let first ← expr n env value
        let tail ← args n env rest
        return first::tail

  def stmt : Nat → Env → Stmt → Option Flow
    | 0, _, _ => none
    | n+1, env, .block body => closeScope env <$> items n env body
    | n+1, env, .declare .u64 name (some value) => do
        let value ← expr n env value
        return .continuing ((name,value)::env)
    | n+1, env, .assign (.variable name) value => do
        let value ← expr n env value
        let next ← assign env name value
        return .continuing next
    | n+1, env, .ite condition yes no => do
        let condition ← expr n env condition
        if condition=0 then
          match no with
          | none => return .continuing env
          | some other => stmt n env other
        else stmt n env yes
    | n+1, env, .whileLoop condition body => do
        let value ← expr n env condition
        if value=0 then return .continuing env
        else
          let next ← stmt n env body
          match next with
          | .returned value => return .returned value
          | .continuing next => stmt n next (.whileLoop condition body)
    | n+1, env, .returnValue (some value) => do
        return .returned (← expr n env value)
    | _, _, _ => none

  def items : Nat → Env → List Stmt → Option Flow
    | 0, _, _ => none
    | _+1, env, [] => some (.continuing env)
    | n+1, env, first::rest => do
        let next ← stmt n env first
        match next with
        | .returned value => return .returned value
        | .continuing next => items n next rest

  def call : Nat → String → List Nat → Option Nat
    | 0, _, _ => none
    | n+1, name, arguments => do
        let function ← functions.find? (fun f => f.name == name)
        if function.result != .u64 then none else do
          if function.parameters.length != arguments.length then none else do
            if !(function.parameters.all fun p => p.1 == .u64) then none else do
              let env := List.zip (function.parameters.map Prod.snd) arguments
              let result ← stmt n env function.body
              match result with
              | .returned value => checked value
              | .continuing _ => none
end

/-- The word operations coincide with C uint64 operations whenever this checked
model executes. Successful multiplication/addition certifies absence of wrap;
successful subtraction/division certifies their application side conditions. -/
theorem checked_iff {n value : Nat} : checked n = some value ↔ value=n ∧ n<wordLimit := by
  simp [checked, and_comm, eq_comm]

theorem binary_add_exact {a b value : Nat} (run : binary .add a b = some value) :
    value=a+b ∧ a+b<wordLimit := checked_iff.mp run

theorem binary_mul_exact {a b value : Nat} (run : binary .mul a b = some value) :
    value=a*b ∧ a*b<wordLimit := checked_iff.mp run

theorem binary_sub_exact {a b value : Nat} (run : binary .sub a b = some value) :
    b≤a ∧ value=a-b := by
  simp only [binary] at run
  split at run <;> simp_all

theorem binary_div_exact {a b value : Nat} (run : binary .div a b = some value) :
    b≠0 ∧ value=a/b := by
  simp only [binary] at run
  split at run <;> simp_all

end RH080Next.FapPV.Execution

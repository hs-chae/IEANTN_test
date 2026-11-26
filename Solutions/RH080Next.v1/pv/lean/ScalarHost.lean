/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.Syntax
set_option autoImplicit false
namespace RH080Next.ScalarHost
open GoldbachDirect

/-- Supported host effects: a sequence of calls to the generic decimal printf
contract, followed by return 0. No rule assumes an application output. Every
numeric argument is obtained by executing its source-defined numerical call. -/
def printSequence (run : String → Option Nat) : List Stmt → Option (List Nat)
  | [.returnValue (some (.literal (.integer 0 "")))] => some []
  | .expression (.call "printf" [.literal (.string "%llu\n"),
      .cast .ull (.call name [])]) :: rest => do
      let value ← run name
      let tail ← printSequence run rest
      return value::tail
  | _ => none

def mainFunction (p : Program) : Option Function :=
  (p.filterMap fun t => match t with | .function f => some f | _ => none).find?
    fun f => f.name == "main"

/-- `uint64_t` arguments are converted to an unsigned-long-long printf argument.
The platform contract states that this type represents all uint64_t values and
that successful `%llu\n` writes their unsigned decimal representation and LF. -/
def mainOutput (p : Program) (run : String → Option Nat) : Option (List Nat) := do
  let f ← mainFunction p
  if f.result != .int || !f.parameters.isEmpty || !f.qualifiers.isEmpty then none
  else match f.body with
    | .block statements => printSequence run statements
    | _ => none

/-- Abstract sequence of numerical calls, used to separate host syntax proofs
from expensive closed numerical executions. -/
def callSequence (run : String → Option Nat) : List String → Option (List Nat)
  | [] => some []
  | name::rest => do
      let value ← run name
      let tail ← callSequence run rest
      return value::tail

def formattedOutput (values : List Nat) : String :=
  String.join (values.map fun n => toString n ++ "\n")
end RH080Next.ScalarHost

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.ReversCertificate
open WinnerDensityA WinnerProgramA

def executeRoute (route : String) : Option Bool :=
  match route with
  | "revers-density200" => some (acceptUpper (run (ModelProgram.program (15/2) (547/100) 6 200 100 4096)) ReversCertificate.bounds200)
  | "revers-density300" => some (acceptUpper (run (ModelProgram.program (15/2) (547/100) 6 300 100 4096)) ReversCertificate.bounds300)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [route] =>
    match executeRoute route with
    | some accepted =>
      IO.println ("{\"route\":\"" ++ route ++ "\",\"accepted\":" ++ (if accepted then "true" else "false") ++ "}")
      return if accepted then 0 else 1
    | none => IO.eprintln "unknown route"; return 2
  | _ => IO.eprintln "expected exactly one route"; return 2

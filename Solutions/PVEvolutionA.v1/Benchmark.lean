/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Configuration
import PVEvolutionA.Evaluator
open WinnerProgramA Lean

def emit (out : List (LeanCert.Core.IntervalDyadic × Bool)) : IO UInt32 := do
  let accepted:=acceptUpper out [1/1000000,1/10]
  let rows:=out.map fun v=>let z:=v.1.toIntervalRat;
    Json.mkObj [("lo",toJson (toString z.lo)),("hi",toJson (toString z.hi)),("domain",toJson v.2)]
  IO.println <| (Json.mkObj [("accepted",toJson accepted),("rows",toJson rows)]).compress
  return if accepted then 0 else 1

def main (args : List String) : IO UInt32 := do
  let p:=PVEvolutionA.Separated.program 330 100 128
  match args with
  | ["old"] => emit (run p)
  | ["configured"] => emit (PVEvolutionA.Evaluator.run p)
  | _ => IO.eprintln "usage: benchmark old|configured";return 2

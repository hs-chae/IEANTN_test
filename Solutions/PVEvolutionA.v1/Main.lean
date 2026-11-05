/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Configuration
import PVEvolutionA.Evaluator
open Lean WinnerProgramA

def main (args : List String) : IO UInt32 := do
  let selected : Option (Fin 3) := match args with
    | ["p300"] => some 0
    | ["p330"] => some 1
    | ["pmid"] => some 2
    | _ => none
  match selected with
  | none => IO.eprintln "usage: pv-evolution p300|p330|pmid";return 2
  | some i =>
    let p:=PVEvolutionA.Configuration.program i
    let bounds:=PVEvolutionA.Configuration.bounds i
    let out:=PVEvolutionA.Evaluator.run p
    let accepted:=acceptUpper out bounds
    let rows:=out.map fun v=>let r:=v.1.toIntervalRat;
      Json.mkObj [("lo",toJson (toString r.lo)),("hi",toJson (toString r.hi)),("domain",toJson v.2)]
    IO.println <| (Json.mkObj [("route",toJson args.head!),
      ("cells",toJson (65537:Nat)),("precision",toJson (-100:Int)),("taylor_depth",toJson (32:Nat)),
      ("bounds",toJson (bounds.map toString)),("rows",toJson rows),("accepted",toJson accepted)]).compress
    return if accepted then 0 else 1

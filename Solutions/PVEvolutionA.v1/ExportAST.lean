/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Configuration
import PVEvolutionA.Evaluator
open Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | [dest] =>
    let scenarios:=(List.finRange 3).map fun i=>
      let p:=PVEvolutionA.Configuration.program i
      Json.mkObj [("index",toJson i.val),
        ("bounds",toJson ((PVEvolutionA.Configuration.bounds i).map toString)),
        ("rows",toJson (p.map fun r=>Json.mkObj [("cells",toJson r.cells),("body",toJson (reprStr r.body))]))]
    IO.FS.writeFile dest <| (Json.mkObj [("precision",toJson (-100:Int)),("taylor_depth",toJson (32:Nat)),
      ("scenarios",toJson scenarios)]).compress
    return 0
  | _ => IO.eprintln "usage: export-ast OUTPUT.json";return 2

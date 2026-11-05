/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerProgramA.Certificate
open Lean WinnerProgramA

def main (args : List String) : IO UInt32 := do
  let selected := match args with
    | ["old"] => some ("old", p0, p0_lo, p0_hi)
    | ["new"] => some ("new", p1, p1_lo, p1_hi)
    | _ => none
  match selected with
  | none =>
    IO.eprintln "usage: winner-program old|new"
    return 2
  | some (name, p, lo, hi) =>
    let out := run p
    let rows := out.map fun v =>
      let r := v.1.toIntervalRat
      Lean.Json.mkObj [("lo", toJson (toString r.lo)), ("hi", toJson (toString r.hi)),
        ("domain", toJson v.2)]
    IO.println <| (Lean.Json.mkObj [("program", toJson name), ("rows", toJson rows),
      ("lower_accepted", toJson (acceptLower out lo)),
      ("upper_accepted", toJson (acceptUpper out hi)),
      ("scope", toJson "finite expression only; no PNT envelope theorem")]).compress
    return 0

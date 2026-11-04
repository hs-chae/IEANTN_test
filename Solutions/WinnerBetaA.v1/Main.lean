/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Numerical
open Lean WinnerProgramA WinnerBetaA.Numerical

def main (args : List String) : IO UInt32 := do
  let selected := match args with
    | ["old"] => some ("old", baseline (9/10), (20000000001/1000000000000 : ℚ))
    | ["beta09-160"] => some ("beta09-160", program (9/10) 160, (16453/10000000 : ℚ))
    | ["beta09-200"] => some ("beta09-200", program (9/10) 200, (14554/10000000 : ℚ))
    | ["beta09-240"] => some ("beta09-240", program (9/10) 240, (13344/10000000 : ℚ))
    | ["beta078-200"] => some ("beta078-200", program (7/8) 200, (2048/1000000 : ℚ))
    | ["beta078-240"] => some ("beta078-240", program (7/8) 240, (19027/10000000 : ℚ))
    | _ => none
  match selected with
  | none =>
    IO.eprintln "usage: winner-beta old|beta09-160|beta09-200|beta09-240|beta078-200|beta078-240"
    return 2
  | some (name,p,bound) =>
    let out := run p
    let rows := out.map fun v => Lean.Json.mkObj [
      ("lo",toJson (toString v.1.toIntervalRat.lo)),
      ("hi",toJson (toString v.1.toIntervalRat.hi)),("domain",toJson v.2)]
    IO.println <| (Lean.Json.mkObj [("scenario",toJson name),("rows",toJson rows),
      ("upper_accepted",toJson (acceptUpper out [bound])),
      ("scope",toJson "source-linked paired coefficient; prime-error theorem is separately proved")]).compress
    return 0

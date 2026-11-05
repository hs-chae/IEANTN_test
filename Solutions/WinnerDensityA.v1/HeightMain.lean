/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightCertificate
open Lean WinnerProgramA WinnerDensityA

def main (args : List String) : IO UInt32 := do
  match args with
  | ["height300"] =>
    let out:=run (HeightProgram.program 300 100 8192)
    let accepted:=acceptUpper out HeightCertificate.bounds
    let rows:=out.map fun v=>
      let r:=v.1.toIntervalRat
      Json.mkObj [("lo",toJson (toString r.lo)),("hi",toJson (toString r.hi)),("domain",toJson v.2)]
    IO.println <| (Json.mkObj [("route",toJson "height300"),("rows",toJson rows),
      ("accepted",toJson accepted),("cells",toJson (8193:Nat))]).compress
    return if accepted then 0 else 1
  | _ => IO.eprintln "usage: winner-height height300"; return 2

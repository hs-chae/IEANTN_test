/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.SharpCertificate
import OriginalKernel
import OriginalSharpScalars
open WinnerDensityA WinnerProgramA WinnerOriginalDensity WinnerOriginalScalars

def executeRoute (route : String) : Option Bool :=
  match route with
  | "density200" => some (acceptUpper (run (ModelProgram.program (759/100) (269/50) 6 200 100 4096)) SharpCertificate.bounds200)
  | "density300" => some (acceptUpper (run (ModelProgram.program (759/100) (269/50) 6 300 100 4096)) SharpCertificate.bounds300)
  | "gaussian-negative" => some (CH2QRH.DensityComputation.checkUpperBound negativeBody 0 2047 (215/1000) integrationCfg)
  | "gaussian-positive" => some (CH2QRH.DensityComputation.checkUpperBound positiveBody 0 4095 (3425/1000) integrationCfg)
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

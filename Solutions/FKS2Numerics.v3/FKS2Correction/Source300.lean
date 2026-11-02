/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Target

namespace FKS2Correction
open FKS2Scalar

private def l := Expr.lit
private def v := Expr.var
private def call := Expr.call
local infixl:65 " +ₑ " => Expr.bin Bin.add
local infixl:70 " *ₑ " => Expr.bin Bin.mul
local infixl:70 " /ₑ " => Expr.bin Bin.div

/-- The original first ten statements include both actual term-producing loops and a2 selection.
Only the final correction suffix is extended; helpers and loop ASTs are the originals. -/
def configuredMain (aLiteral : String) : Function :=
  { mainFunction with body := mainFunction.body.take 10 ++ [
    .localVar "u" (v "r" /ₑ l "300.0"),
    .localVar "z" (call "sqrt_fixed" (l "300.0" /ₑ v "r")),
    .localVar "p" (((l "1.0" /ₑ l aLiteral) *ₑ v "u") /ₑ v "z"),
    .assign "p" (v "p" *ₑ call "exp_small" (l "2.0" *ₑ v "z")),
    .localVar "e15" (call "exp_small" (.neg (l "15.0"))),
    .localVar "e150" (v "e15"),
    .loop "n" (l "1.0") (l "10.0") false [
      .assign "e150" (v "e150" *ₑ v "e15")],
    .localVar "e20" (call "exp_small" (.neg (l "20.0"))),
    .localVar "e200" (v "e20"),
    .loop "n" (l "1.0") (l "10.0") false [
      .assign "e200" (v "e200" *ₑ v "e20")],
    .localVar "b1" ((v "a1" *ₑ l "300.0") *ₑ v "e150"),
    .localVar "b2" ((v "a2" *ₑ l "300.0") *ₑ v "e200"),
    .ret (v "p" *ₑ (v "b1" +ₑ v "b2"))] }

def configuredProgram (aLiteral : String) : List Function :=
  [expFunction, sqrtFunction, configuredMain aLiteral]

def baselineSource : String := include_str ".."/"c"/"baseline.c"
def baselineAST := configuredProgram "121.096"
def baselineChecked : Bool :=
  let ts := tokens baselineSource
  ts.isSome && ts == tokens (String.join (baselineAST.map functionTokens))

/-- A failed token/constructor association supplies no executable entry point. -/
def baselineProgram := if baselineChecked then baselineAST else []
def baselineBits : Nat := 0x3345fce053ddfb3d
def baselineQ : ℚ := decodeBits baselineBits

def baselineFrame : Frame :=
  ((evalBlock round64 baselineProgram 1024 ⟨[], none⟩ (configuredMain "121.096").body).run [])
    |>.getD (⟨[], none⟩, []) |>.1

def baselineEvents : List HelperEvent :=
  ((executeObserved round64 baselineProgram).map Prod.snd).getD []

theorem prefix_preserved (a : String) :
    (configuredMain a).body.take 10 = mainFunction.body.take 10 := by
  rfl

theorem baseline_source_checked : baselineChecked = true := by
  native_decide

theorem baseline_source_execution : ExecC baselineProgram baselineQ := by
  unfold ExecC
  native_decide

theorem baseline_prefix_execution :
    (evalBlock round64 baselineProgram 1024 ⟨[], none⟩
      ((configuredMain "121.096").body.take 6)).run [] =
        some (FKS2SumBridge.trace1.result, FKS2SumBridge.trace1.events) ∧
    (evalBlock round64 baselineProgram 1024 ⟨[], none⟩
      ((configuredMain "121.096").body.take 7)).run [] =
        some (FKS2SumBridge.trace2.result, FKS2SumBridge.trace2.events) ∧
    (get baselineFrame.env "s1").getD 0 = FKS2SumBridge.acc1 ∧
    (get baselineFrame.env "s2").getD 0 = FKS2SumBridge.acc2 := by
  native_decide

theorem baseline_scope_checks :
    programSupported [] baselineProgram = true ∧
    (execute baselineProgram).bind encodePositiveNormal = some baselineBits ∧
    finiteBits baselineBits = true ∧
    baselineEvents.length = 87 := by
  native_decide

end FKS2Correction

/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Audit300
import IEANTN.Nodes.FKS2Numerics.v4.Conclusions
namespace FKS2Update
open FKS2Scalar FKS2Correction

def updatedSource : String := include_str ".."/"c"/"updated.c"
def updatedAST := configuredProgram "0.0000000001"
def updatedChecked : Bool :=
  let ts := tokens updatedSource
  ts.isSome && ts == tokens (String.join (updatedAST.map functionTokens))
def updatedProgram := if updatedChecked then updatedAST else []
def updatedBits : Nat := 0x35c8376dc3f5b49f
def updatedQ : ℚ := decodeBits updatedBits
def updatedEvents : List HelperEvent :=
  ((executeObserved round64 updatedProgram).map Prod.snd).getD []
def coefficientRatio : ℚ := 121.096 / 0.0000000001
def transportDelta : ℚ := 1/10^62

theorem updated_source_checked : updatedChecked = true := by
  native_decide

theorem updated_source_execution : ExecC updatedProgram updatedQ := by
  unfold ExecC
  native_decide

theorem updated_scope_checks :
    programSupported [] updatedProgram = true ∧ finiteBits updatedBits = true ∧
    (execute updatedProgram).bind encodePositiveNormal = some updatedBits ∧
    updatedEvents = baselineEvents := by
  native_decide

theorem output_transport_check :
    |updatedQ-coefficientRatio*baselineQ| ≤ transportDelta := by
  native_decide

end FKS2Update

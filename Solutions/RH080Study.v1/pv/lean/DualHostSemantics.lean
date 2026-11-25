/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Output
open GoldbachDirect

/-- Standard unsigned decimal output followed by one newline. The relation to
physical libc/OS bytes is an explicitly stated generic printf contract. -/
def decimalLine (value : Nat) : String := toString value ++ "\n"

/- Numeric-expression execution in the host harness. Direct calls are tied to
the exact checked numerical AST interpreter; casts preserve this known uint64
value. No constructor mentions the selected application routine or its answer. -/
mutual
inductive HostExpr : Expr → Nat → Prop where
  | call {fuel name values result arguments}
      (argumentsRun : HostArgs arguments values)
      (run : Execution.call fuel name values = some result) :
      HostExpr (.call name arguments) result
  | castULL {expression value} (run : HostExpr expression value)
      (fits : value<Execution.wordLimit) : HostExpr (.cast .ull expression) value
inductive HostArgs : List Expr → List Nat → Prop where
  | nil : HostArgs [] []
  | cons {expression value expressions values}
      (first : HostExpr expression value) (rest : HostArgs expressions values) :
      HostArgs (expression::expressions) (value::values)
end

/-- The printf primitive's actually performed capture is a parameter, not a
trusted application success fact. It may include partial/failed I/O behavior;
the application ignores printf's return code. A successful-format contract is
therefore stated separately whenever exact output bytes are concluded. -/
inductive PrintAction (PerformedPrintf : Nat → String → Prop) : Expr → String → Prop where
  | unsignedLine {expression value output} (run : HostExpr expression value)
      (performed : PerformedPrintf value output) :
      PrintAction PerformedPrintf
        (.call "printf" [.literal (.string "%llu\n"), expression]) output

/-- Restricted complete host-main behavior: an actual print action followed by
return zero. This rule names no application function and contains no constant
mathematical result. It precisely covers the two statements in the host source. -/
inductive HostMain (PerformedPrintf : Nat → String → Prop) : Stmt → String → Prop where
  | printReturn {expression output}
      (action : PrintAction PerformedPrintf expression output) :
      HostMain PerformedPrintf (.block [.expression expression,
        .returnValue (some (.literal (.integer 0 "")))]) output

/-- A contract for a successfully captured printf operation. Existence of such
an operation is never made a generic compiler/runtime premise. Physical runs are
separately associated with their actual captured stdout bytes by receipts. -/
def SuccessfulPrintfContract (PerformedPrintf : Nat → String → Prop) : Prop :=
  ∀ value output, PerformedPrintf value output → output=decimalLine value


end RH080PV.Output

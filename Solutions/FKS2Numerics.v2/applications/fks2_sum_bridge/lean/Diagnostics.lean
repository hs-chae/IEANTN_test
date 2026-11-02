import FKS2SumBridge
import Lean

open Lean FKS2Scalar FKS2SumBridge

def ratJson (x : Rat) : Json := Json.mkObj [
  ("exact", toJson (toString x)),
  ("ceil_scaled_1e30", toJson (toString (⌈x * 10 ^ 30⌉ : Int)))]

def stepJson (loop : Nat) (name : String) (j : Nat) (st : Iteration) : Json :=
  let k := j + 3
  Json.mkObj [
    ("loop", toJson loop), ("offset", toJson j), ("counter", ratJson (counterOf st)),
    ("body_fuel", toJson ((if loop == 1 then 1016 else 1015) - j)),
    ("helper_name", toJson (eventOf st).name), ("helper_argument", ratJson (eventOf st).arg),
    ("helper_return", ratJson (termOf st)),
    ("accumulator_before", ratJson (beforeAcc name st)),
    ("accumulator_after", ratJson (afterAcc name st)),
    ("binary64_mantissa", toJson (toString (mantissaOf (termOf st)))),
    ("binary64_exponent", toJson (toString (exponentOf (termOf st)))),
    ("domain_check", toJson (inputCheck (termOf st))),
    ("source_step_check", toJson (stepCheck name st)),
    ("RN64_certificate_check", toJson (addCheck (beforeAcc name st + termOf st) (afterAcc name st))),
    ("term_error_envelope", ratJson (if loop == 1 then epsilon1 k else epsilon2 k))]

#eval do
  let rows := (trace1.steps.zipIdx.map (fun (st, j) => stepJson 1 "s1" j st)) ++
    (trace2.steps.zipIdx.map (fun (st, j) => stepJson 2 "s2" j st))
  IO.FS.writeFile "../evidence/source_trace_ledger.json" (Json.arr rows.toArray).pretty
  let budget := Json.mkObj [
    ("terms1", toJson terms1.length), ("terms2", toJson terms2.length),
    ("acc1", ratJson acc1), ("acc2", ratJson acc2),
    ("gamma40", ratJson (SumStability.gamma 40)),
    ("gamma41", ratJson (SumStability.gamma 41)),
    ("upperSum1", ratJson upperSum1), ("upperSum2", ratJson upperSum2),
    ("specError1", ratJson specError1), ("specError2", ratJson specError2),
    ("bridgeError", ratJson bridgeError),
    ("propagatedSpecificationError", ratJson (sensitivity * max specError1 specError2)),
    ("roundError1", ratJson roundError1), ("roundError2", ratJson roundError2),
    ("termError1", ratJson termError1), ("termError2", ratJson termError2),
    ("sumError1", ratJson sumError1), ("sumError2", ratJson sumError2),
    ("prefactor", ratJson prefactor), ("constantB", ratJson constantB),
    ("sumCoefficient", ratJson sumCoefficient), ("sensitivity", ratJson sensitivity),
    ("coefficientError", ratJson coefficientError), ("suffixError", ratJson suffixError),
    ("propagatedSumError", ratJson (sensitivity * max sumError1 sumError2)),
    ("totalError", ratJson totalError), ("q", ratJson q),
    ("Bpoc", ratJson Bpoc), ("output_bits", toJson outputBits)]
  IO.FS.writeFile "../evidence/error_budget.json" budget.pretty

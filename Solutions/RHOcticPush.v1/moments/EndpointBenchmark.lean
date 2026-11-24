import LeanCert.Validity.Bounds.Core
namespace RHOcticPush.EndpointBenchmark
open LeanCert.Core LeanCert.Engine LeanCert.Validity
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

def A (q : ℚ) : ℚ := -16/q^2+672/q^4-13440/q^6+80640/q^8
def B (q : ℚ) : ℚ := 112/q^3-3360/q^5+40320/q^7-80640/q^9
def e (q : ℚ) : Expr := .add (.mul (.const (A q)) (.cos (.var 0)))
  (.mul (.const (B q)) (.sin (.var 0)))
def I (q : ℚ) : IntervalRat := ⟨q,q,le_refl q⟩
def check (q c : ℚ) : Bool := checkUpperBound (e q) (I q) c {taylorDepth := 20} &&
  checkLowerBound (e q) (I q) (-c) {taylorDepth := 20}
example : check 1 2 = true := by decide +kernel
example : check 10 (1/10) = true := by decide +kernel
example : check 100 (1/500) = true := by decide +kernel
#print axioms RHOcticPush.EndpointBenchmark.check
end RHOcticPush.EndpointBenchmark

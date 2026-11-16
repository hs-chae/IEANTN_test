/- The unchanged C main's exact interval expression, before its source-state join.
This is a numerical model; its finite kernel checks alone are not source-first PV.
Actual guards, range applicability and main-loop execution are separate proofs. -/
import SynergyHeightC.FullMainFrame
import SynergyBasis.PositiveDivision
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical
open SynergyAnalytic.HeightPoint SynergyHeightC.PointExecuteAPI
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def adjustedC (c : ProofBox) : ProofBox :=
  ProofBox.add c (ProofBox.literal 128 21600 1)

def fc (c : ProofBox) : ProofBox :=
  ⟨(adjustedC c).hi,(adjustedC c).hi⟩

def fd (d : ProofBox) : ProofBox := ⟨d.hi,d.hi⟩

def weight (left right : ProofBox) : ProofBox :=
  SynergyBasis.Positive.positiveSub
    (SynergyBasis.Positive.expNeg left) (SynergyBasis.Positive.expNeg right)

/-- The C divI computes a direct floor/ceiling division. There is no replacement
by multiplication with a separately rounded inverse. The source expNegAny has
zero shifts when its proved argument is at most 64. -/
def paired (d : ProofBox) : ProofBox :=
  let L := ProofBox.literal 128 330 1
  let difference := SynergyBasis.Positive.positiveSub L (fd d)
  let e := SynergyBasis.Positive.expNeg (SynergyBasis.Positive.divN difference 8)
  ProofBox.add e (SynergyBasis.Positive.divI
    (ProofBox.mul 128 L (SynergyBasis.Positive.positiveSub SynergyBasis.Positive.one e))
    difference)

def term (left right c d : ProofBox) : ProofBox :=
  ProofBox.mul 128
    (ProofBox.mul 128 (ProofBox.literal 128 2 1)
      (ProofBox.mul 128 (weight left right) (fc c))) (paired d)

/-- Its arguments are the actual model pair used by the source-execution family,
not a substituted table of recorded upper words. -/
def cell (i : Nat) : Option ProofBox := do
  let left ← logCell i
  let right ← logCell (i+1)
  let pair ← modelOutputs right
  pure (term left right pair.1 pair.2)

def block (lo count : Nat) : Option ProofBox :=
  (List.range count).foldlM (fun total j => do
    let next ← cell (lo+j)
    pure (ProofBox.add total next)) (⟨0,0⟩ : ProofBox)

def prefixSum (count : Nat) : Option ProofBox := block 0 count

/-- These are explicit useful finite domain obligations; this predicate is not
a substitute for all source arithmetic, range, memory and guard proofs. -/
def cellDomain (i : Nat) : Bool :=
  match logCell i,logCell (i+1) with
  | some left,some right =>
    match modelOutputs right with
    | some (c,d) =>
      decide (0 ≤ left.lo ∧ left.lo ≤ left.hi ∧ left.hi ≤ 64*ProofBox.scale 128 ∧
        0 ≤ right.lo ∧ right.lo ≤ right.hi ∧ right.hi ≤ 64*ProofBox.scale 128 ∧
        0 ≤ (adjustedC c).hi ∧ 0 ≤ d.hi ∧ d.hi < 330*ProofBox.scale 128 ∧
        0 ≤ (term left right c d).lo ∧
        (term left right c d).lo ≤ (term left right c d).hi ∧
        (term left right c d).hi ≤ ProofBox.scale 128)
    | none => false
  | _,_ => false

end SynergyHeightC.MainWeightModel

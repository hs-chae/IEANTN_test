import SynergyAnalytic.TangentCompute
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def prefixFold (pre:Nat) : Nat→Option ProofBox
  | 0=>some zero
  | k+1=>do
      let previous←prefixFold pre k
      let cell←sourceCell (rat (5*pre+k) (6*pre)) (rat 1 (6*pre)) false
      pure (add previous cell.1)

def sharedFold (n:Nat) : Nat→Option (ProofBox×ProofBox×ProofBox)
  | 0=>some (zero,zero,zero)
  | k+1=>do
      let previous←sharedFold n k
      let cell←sourceCell (rat (n+15*k) n) (rat 15 n) true
      pure (add previous.1 cell.1,add previous.2.1 cell.2.1,add previous.2.2 cell.2.2)

/-- Pure mathematical integer-interval counterpart. It has the same primitive
order and all analytic-domain guards; C-word overflow/applicability and actual
source execution remain separate, as documented in the component trust scope. -/
def sourceBasis (n:Nat) : Option (ProofBox×ProofBox×ProofBox) := do
  if n < 16 ∨ 65536 < n then none else do
    let pre:=n/16
    let first←prefixFold pre pre
    let common←sharedFold n n
    let q:=rat 601 2500
    let logarithm←logPos 384 (mul p (rat 6 1) q)
    let peak←safeExp (divN (add one logarithm) 6)
    let bq:=mul p (rat 256 1) q
    let e←safeExp bq
    let tail←safeDiv (mul p e (add bq one)) (mul p (rat 2 1) (mul p q q))
    pure (add (add (add first common.1) (mul p (rat 5 6) peak)) tail,
      add common.2.1 tail,add common.2.2 tail)

/- Host proposal only; exact ordinary-kernel replay is in a separate module. -/
#eval sourceBasis 256
end SynergyAnalytic.BoxModel

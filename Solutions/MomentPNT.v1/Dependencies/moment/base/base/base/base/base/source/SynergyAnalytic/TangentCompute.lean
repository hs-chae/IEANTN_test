import SynergyAnalytic.LogPosModel
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Application-specific functional model, not C operational semantics.
All source guards remain explicit and no computed output is embedded. -/
def rat (n d:Nat) : ProofBox := literal p (n:Int) d

def safeDiv (a b:ProofBox) : Option ProofBox :=
  if 0 < b.lo then some (divI a b) else none

def safeExp (a:ProofBox) : Option ProofBox :=
  if a.lo < 0 ∨ a.hi < a.lo ∨ 64*scale p < a.hi then none else some (expNeg a)

def sourcePower (x:ProofBox) : Nat→ProofBox
  | 0=>one
  | n+1=>mul p (sourcePower x n) x

def newtonStep (left a:ProofBox) : Option ProofBox := do
  let quotient←safeDiv left (mul p a a)
  pure (divN (add (mul p (rat 2 1) a) quotient) 3)
def newtonParameter (left:ProofBox) : Option ProofBox := do
  let a:=divN (add left (rat 2 1)) 3
  let b←newtonStep left a
  newtonStep left b

def momentSeries (z:ProofBox) : Nat→ProofBox×ProofBox
  | 0=>(one,one)
  | n+1=>let previous:=momentSeries z n
           let term:=divN (mul p previous.1 z) (n+1)
           (term,add previous.2 term)

def sourceMoment (lambda width commonExp:ProofBox) (j:Nat) : Option ProofBox := do
  if 4 < j then none else do
    let z:=mul p lambda width
    let residue:=positiveSub one (mul p commonExp (momentSeries z j).2)
    safeDiv (mul p (rat j.factorial 1) residue) (sourcePower lambda (j+1))

def sourceCoefficients (left a:ProofBox) : Option (Fin 5→ProofBox) := do
  let A:=divN (mul p (rat 5 1) a) 6
  let B←safeDiv one (mul p (rat 6 1) (sourcePower a 5))
  pure (fun k=>if k.val=0 then add A (mul p B (mul p left left))
    else if k.val=1 then mul p (rat 2 1) (mul p B left)
    else if k.val=2 then B else zero)

def convolve (coeff:Fin 5→ProofBox) (logLeft invLeft:ProofBox) : Fin 5→ProofBox :=
  fun k=>if hk:k.val=0 then mul p (coeff k) logLeft
    else add (mul p (coeff ⟨k.val-1,by omega⟩) invLeft) (mul p (coeff k) logLeft)

def sourceDot (coeff moments:Fin 5→ProofBox) : Nat→ProofBox
  | 0=>zero
  | n+1=>if hn:n<5 then add (sourceDot coeff moments n) (mul p (coeff ⟨n,hn⟩) (moments ⟨n,hn⟩)) else zero

def sourceCell (left width:ProofBox) (logs:Bool) : Option (ProofBox×ProofBox×ProofBox) := do
  let a←newtonParameter left
  let coefficients←sourceCoefficients left a
  let q:=rat 601 2500
  let lambda:=mul p (rat 2 1) (mul p q left)
  let commonExp←safeExp (mul p lambda width)
  let m0←sourceMoment lambda width commonExp 0
  let m1←sourceMoment lambda width commonExp 1
  let m2←sourceMoment lambda width commonExp 2
  let m3←sourceMoment lambda width commonExp 3
  let m4←sourceMoment lambda width commonExp 4
  let moments:Fin 5→ProofBox:=fun k=>if k.val=0 then m0 else if k.val=1 then m1
    else if k.val=2 then m2 else if k.val=3 then m3 else m4
  let gaussian←safeExp (mul p q (mul p left left))
  let logLeft←if logs then logPos 384 left else some zero
  let invLeft←safeDiv one left
  let output0:=mul p gaussian (sourceDot coefficients moments 5)
  if logs then
    let next:=convolve coefficients logLeft invLeft
    let output1:=mul p gaussian (sourceDot next moments 5)
    let last:=convolve next logLeft invLeft
    let output2:=mul p gaussian (sourceDot last moments 5)
    pure (output0,output1,output2)
  else pure (output0,zero,zero)

/- Diagnostic host evaluation only; no numerical theorem claimed here. -/
#eval sourceCell (rat 1 1) (rat 15 256) true
end SynergyAnalytic.BoxModel

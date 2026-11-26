/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootX
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080Next.FFTPV.RootSource
open FFT.IntegerModel

/-- The two original, fixed grids. This is an applicability restriction,
not a change in the root source or numerical parameters. -/
def OriginalGrid (n : Nat) : Prop:=n=131072 ∨ n=16777216

structure TaylorState where
  ct : Int
  st : Int
  cr : Int
  sr : Int
  deriving DecidableEq

def xInteger (n : Nat) : Int:=(2*piInteger)/(n:Int)
def x2Integer (n : Nat) : Int:=(xInteger n*xInteger n)/unit

def taylorStep (n j : Nat) (s : TaylorState) : TaylorState:=
  let i:=j+1
  let ct:=((s.ct*x2Integer n)/unit)/((2*i*(2*i-1):Nat):Int)
  let st:=((s.st*x2Integer n)/unit)/((2*i*(2*i+1):Nat):Int)
  if i%2=1 then ⟨ct,st,s.cr-ct,s.sr-st⟩ else ⟨ct,st,s.cr+ct,s.sr+st⟩

def taylorState (n : Nat) : Nat → TaylorState
  | 0=>⟨unit,xInteger n,unit,xInteger n⟩
  | j+1=>taylorStep n j (taylorState n j)

/-- Exact general correspondence to the existing integer model. The finite
loop is reduced symbolically; no output or execution result is hypothesized. -/
theorem taylorState_root (n : Nat) :
    ((taylorState n 10).cr,-(taylorState n 10).sr)=root n := by rfl

/-- Bounds for the original finite recurrence, checked by the Lean kernel.
They are model guard facts; source execution is proved separately. -/
theorem original_recurrence_bounds (n j : Nat) (grid : OriginalGrid n) (hj : j≤10) :
    0≤(taylorState n j).ct ∧ (taylorState n j).ct≤unit ∧
    0≤(taylorState n j).st ∧ (taylorState n j).st≤unit ∧
    0≤(taylorState n j).cr ∧ (taylorState n j).cr≤2*unit ∧
    0≤(taylorState n j).sr ∧ (taylorState n j).sr≤2*unit := by
  rcases grid with rfl|rfl
  all_goals interval_cases j <;> decide

theorem original_x_bounds (n : Nat) (grid : OriginalGrid n) :
    0≤xInteger n ∧ xInteger n≤unit ∧ 0≤x2Integer n ∧ x2Integer n≤unit := by
  rcases grid with rfl|rfl <;> decide

theorem original_grid_divisor (n : Nat) (grid : OriginalGrid n) : 0<n ∧ n<1000000000 := by
  rcases grid with rfl|rfl <;> omega

theorem iteration_divisors (j : Nat) (hj : j<10) :
    0<2*(j+1)*(2*(j+1)-1) ∧ 2*(j+1)*(2*(j+1)-1)<1000000000 ∧
    0<2*(j+1)*(2*(j+1)+1) ∧ 2*(j+1)*(2*(j+1)+1)<1000000000 := by
  interval_cases j <;> decide

#print axioms taylorState_root
#print axioms original_recurrence_bounds
#print axioms original_x_bounds
#print axioms iteration_divisors
end RH080Next.FFTPV.RootSource

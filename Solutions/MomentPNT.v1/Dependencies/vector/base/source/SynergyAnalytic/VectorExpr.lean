import SynergyAnalytic.BoxSqrt
import SynergyAnalytic.LogPosModel
import SynergyBasis.BoxRealInverse
namespace SynergyAnalytic.VectorExpr
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- A mathematical interval-expression model. A separate actual-source
execution proof is required before interpreting this model as source-first PV. -/
inductive Expr where
  | rat (n : Int) (d : Nat)
  | pi
  | input (i : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  | inv (a : Expr)
  | expPos (a : Expr)
  | expNeg (a : Expr)
  | log (a : Expr)
  | sqrt (a : Expr)
  deriving Repr

noncomputable def value (xs : List ℝ) : Expr → ℝ
  | .rat n d => (n:ℝ)/d
  | .pi => Real.pi
  | .input i => xs[i]?.getD 0
  | .add a b => value xs a+value xs b
  | .mul a b => value xs a*value xs b
  | .neg a => -value xs a
  | .inv a => (value xs a)⁻¹
  | .expPos a => Real.exp (value xs a)
  | .expNeg a => Real.exp (-value xs a)
  | .log a => Real.log (value xs a)
  | .sqrt a => Real.sqrt (value xs a)

def piLo := literal p 3141592653589793238 1000000000000000000
def piHi := literal p 3141592653589793239 1000000000000000000
def piBox : ProofBox := ⟨piLo.lo,piHi.hi⟩

def eval (xs : List ProofBox) : Expr → Option ProofBox
  | .rat n d => if 0<d then some (literal p n d) else none
  | .pi => some piBox
  | .input i => xs[i]?
  | .add a b => do pure (add (←eval xs a) (←eval xs b))
  | .mul a b => do pure (mul p (←eval xs a) (←eval xs b))
  | .neg a => do pure (neg (←eval xs a))
  | .inv a => do
    let v ← eval xs a
    if 0 < v.lo ∨ v.hi < 0 then some (inv p v) else none
  | .expPos a => do
    let v ← eval xs a
    if v.lo < 0 ∨ 64*scale p < v.hi then none else
      let out := SynergyBasis.Positive.expNeg v
      if 0 < out.lo then some (inv p out) else none
  | .expNeg a => do
    let v ← eval xs a
    if v.lo < 0 ∨ 64*scale p < v.hi then none else
      some (SynergyBasis.Positive.expNeg v)
  | .log a => do BoxModel.logPos 384 (←eval xs a)
  | .sqrt a => do
    let v ← eval xs a
    if 0 ≤ v.lo then some (BoxModel.sqrtBox v) else none

theorem piBox_sound : RealBox.Contains p piBox Real.pi := by
  have hlo := RealBox.literal_sound p 3141592653589793238 1000000000000000000 (by decide)
  have hhi := RealBox.literal_sound p 3141592653589793239 1000000000000000000 (by decide)
  have hp := RealBox.scale_real_pos p
  have hpl : (3141592653589793238:ℝ)/1000000000000000000 ≤ Real.pi := by linarith [Real.pi_gt_d20]
  have hph : Real.pi ≤ (3141592653589793239:ℝ)/1000000000000000000 := by linarith [Real.pi_lt_d20]
  exact ⟨hlo.1.trans (mul_le_mul_of_nonneg_right hpl hp.le),
    (mul_le_mul_of_nonneg_right hph hp.le).trans hhi.2⟩

theorem checked_range {a : ProofBox} {x : ℝ} (ha : RealBox.Contains p a x)
    (h : ¬(a.lo < 0 ∨ 64*scale p < a.hi)) : 0 ≤ x ∧ x ≤ 64 := by
  have hlo : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast le_of_not_gt (not_or.mp h).1
  have hhi : (a.hi:ℝ) ≤ 64*(scale p:ℝ) := by exact_mod_cast le_of_not_gt (not_or.mp h).2
  have hp := RealBox.scale_real_pos p
  constructor <;> nlinarith [ha.1,ha.2]

def EnvSound (input : List ProofBox) (xs : List ℝ) : Prop :=
  ∀ (i : Nat) (b : ProofBox),input[i]?=some b → ∃(x : ℝ),xs[i]?=some x ∧ RealBox.Contains p b x

theorem eval_sound (e : Expr) {input : List ProofBox} {out : ProofBox} {xs : List ℝ}
    (hx : EnvSound input xs) (hr : eval input e=some out) :
    RealBox.Contains p out (value xs e) := by
  induction e generalizing out with
  | rat n d =>
    by_cases hd : 0<d
    · simp only [eval,hd,ite_true,Option.some.injEq] at hr
      subst out
      exact RealBox.literal_sound p n d (by exact_mod_cast hd)
    · simp [eval,hd] at hr
  | pi => simp only [eval,Option.some.injEq] at hr;subst out;exact piBox_sound
  | input i =>
    obtain ⟨x,hi,hmem⟩:=hx i out hr
    simpa [value,hi] using hmem
  | add a b iha ihb =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      cases hb:eval input b with
      | none => simp [eval,ha,hb] at hr
      | some vb =>
        simp only [eval,ha,hb,Bind.bind,Option.bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hr
        subst out
        exact RealBox.add_sound (iha ha) (ihb hb)
  | mul a b iha ihb =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      cases hb:eval input b with
      | none => simp [eval,ha,hb] at hr
      | some vb =>
        simp only [eval,ha,hb,Bind.bind,Option.bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hr
        subst out
        exact RealBox.mul_sound (iha ha) (ihb hb)
  | neg a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some,Option.pure_def,Option.some.injEq] at hr
      subst out
      exact RealBox.neg_sound (ih ha)
  | inv a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      by_cases hg : 0<va.lo ∨ va.hi<0
      · simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some,hg,ite_true,Option.some.injEq] at hr
        subst out
        exact RealBox.inv_sound (ih ha) hg
      · simp [eval,ha,hg] at hr
  | expNeg a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      by_cases hg : va.lo<0 ∨ 64*scale p<va.hi
      · simp [eval,ha,hg] at hr
      · simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some,hg,ite_false,Option.some.injEq] at hr
        subst out
        have hb := checked_range (ih ha) hg
        exact SynergyBasis.Positive.expNeg_sound (ih ha) hb.1 hb.2
  | expPos a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      by_cases hg : va.lo<0 ∨ 64*scale p<va.hi
      · simp [eval,ha,hg] at hr
      · by_cases ho : 0<(SynergyBasis.Positive.expNeg va).lo
        · simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some,hg,ite_false,ho,ite_true,Option.some.injEq] at hr
          subst out
          have hb := checked_range (ih ha) hg
          have he := RealBox.inv_sound (SynergyBasis.Positive.expNeg_sound (ih ha) hb.1 hb.2) (Or.inl ho)
          simpa only [value,Real.exp_neg,inv_inv] using he
        · simp [eval,ha,hg,ho] at hr
  | log a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some] at hr
      exact BoxModel.logPos_sound 384 (ih ha) hr
  | sqrt a ih =>
    cases ha:eval input a with
    | none => simp [eval,ha] at hr
    | some va =>
      by_cases hg : 0≤va.lo
      · simp only [eval,ha,Bind.bind,Option.bind,Option.bind_some,hg,ite_true,Option.some.injEq] at hr
        subst out
        exact BoxModel.sqrtBox_sound (ih ha) hg
      · simp [eval,ha,hg] at hr

#print axioms eval_sound
end SynergyAnalytic.VectorExpr

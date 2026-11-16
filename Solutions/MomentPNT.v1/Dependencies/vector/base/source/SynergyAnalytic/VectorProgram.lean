import SynergyAnalytic.VectorExpr
namespace SynergyAnalytic.VectorExpr
open ScopedNumerical ScopedNumerical.ProofBox
open SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def run : List Expr → List ProofBox → Option (List ProofBox)
  | [],ctx => some ctx
  | e::rest,ctx => do
    let b ← eval ctx e
    run rest (ctx++[b])
noncomputable def realRun : List Expr → List ℝ → List ℝ
  | [],ctx => ctx
  | e::rest,ctx => realRun rest (ctx++[value ctx e])

theorem env_append {bs : List ProofBox} {xs : List ℝ} {b : ProofBox} {x : ℝ}
    (hlen : bs.length=xs.length) (h : EnvSound bs xs) (hb : RealBox.Contains p b x) :
    EnvSound (bs++[b]) (xs++[x]) := by
  intro i out hi
  by_cases hil : i<bs.length
  · have hi' : bs[i]?=some out := by simpa only [List.getElem?_append_left hil] using hi
    obtain ⟨v,hv,hm⟩:=h i out hi'
    refine ⟨v,?_,hm⟩
    rw [List.getElem?_append_left (by omega)]
    exact hv
  · have hle : bs.length ≤ i := le_of_not_gt hil
    rw [List.getElem?_append_right hle] at hi
    have hh : i-bs.length=0 := by
      cases hj : i-bs.length with
      | zero => rfl
      | succ k => simp [hj] at hi
    have hout : out=b := by simpa [hh] using hi.symm
    subst out
    refine ⟨x,?_,hb⟩
    rw [List.getElem?_append_right (by omega)]
    simpa only [←hlen,hh] using (show [x][0]?=some x by rfl)

theorem run_sound (program : List Expr) {input out : List ProofBox} {xs : List ℝ}
    (hlen : input.length=xs.length) (hs : EnvSound input xs)
    (hr : run program input=some out) :
    out.length=(realRun program xs).length ∧ EnvSound out (realRun program xs) := by
  induction program generalizing input xs with
  | nil => simp only [run,Option.some.injEq] at hr;subst out;exact ⟨hlen,hs⟩
  | cons e rest ih =>
    cases he:eval input e with
    | none => simp [run,he] at hr
    | some b =>
      simp only [run,he,Bind.bind,Option.bind] at hr
      have hb := eval_sound e hs he
      exact ih (by simp only [List.length_append,List.length_singleton,hlen]) (env_append hlen hs hb) hr

#print axioms run_sound
end SynergyAnalytic.VectorExpr

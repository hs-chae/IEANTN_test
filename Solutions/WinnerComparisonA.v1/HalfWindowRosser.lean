/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import HalfWindow
import StrongAllowance
namespace WinnerHalfWindow
open Real Set CH2QRH WinnerOldFloors WinnerOldC4Source WinnerStrongEnvelope
set_option maxHeartbeats 0

/-- Rosser's original sharper count theorem, explicitly distinguished from
the weaker one-fifth-log-plus-two bound of the restricted CH2-only package. -/
def OriginalSharpRosser : Prop :=∀t:ℝ,2≤t→
  |ZeroCount.v1.zetaNClosed t-ZeroCount.v1.rvmMain t|≤
    (137/1000)*log t+(443/1000)*log (log t)+397/250

theorem rvm_main_difference {H T:ℝ} (hH:0<H) (hT:0<T) :
    (ZeroCount.v1.rvmMain T-ZeroCount.v1.rvmMain H)/(2*T)=
      ((log H-log (2*Real.pi)-1)*(1-H/T)+(log T-log H))/(4*Real.pi) := by
  unfold ZeroCount.v1.rvmMain
  rw [log_div hT.ne' (by positivity : 2*Real.pi≠0),
    log_div hH.ne' (by positivity : 2*Real.pi≠0)]
  field_simp [Real.pi_ne_zero,hT.ne']
  ring

/-- Exact normalization of the original Riemann--von Mangoldt main terms. -/
theorem windowMain_exact (v:ℝ) :
    (ZeroCount.v1.rvmMain (exp (h+v))-ZeroCount.v1.rvmMain 3000000000000)/
      (2*exp (h+v))=windowMain v := by
  rw [rvm_main_difference (by norm_num) (exp_pos _),log_exp]
  have hh:exp h=(3000000000000:ℝ):=exp_log (by norm_num)
  have hratio:(3000000000000:ℝ)/exp (h+v)=exp (-v):=by
    rw [exp_add,hh,exp_neg]
    field_simp [exp_ne_zero]
  rw [hratio]
  unfold windowMain h
  ring

/-- Original sharper Rosser bounds plus the proved multiplicity pairing give
the exact full old half-window allowance at every real v>=0. -/
theorem closed_windowAllowance (hRosser:OriginalSharpRosser)
    (hRH:IEANTN.RiemannHypothesisUpTo 3000000000000)
    {sigma v:ℝ} (hs:(1/2:ℝ)≤ sigma) (hv:0≤v) :
    IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 (exp (h+v))) (fun _↦(1:ℝ))/exp (h+v)≤
      windowAllowance v := by
  have hexph:exp h=(3000000000000:ℝ):=exp_log (by norm_num)
  have hHT:(3000000000000:ℝ)≤exp (h+v):=by
    rw [exp_add,hexph]
    have he:1≤exp v:=one_le_exp hv
    nlinarith
  have hT2:2≤exp (h+v):=by linarith
  have hhalf:=high_closed_div_height hs (by norm_num) hHT (exp_pos _) hRH
  have hRt:=hRosser (exp (h+v)) hT2
  have hRh:=hRosser 3000000000000 (by norm_num)
  change |ZeroCount.v1.zetaNClosed (exp (h+v))-ZeroCount.v1.rvmMain (exp (h+v))|≤
    rosserError (log (exp (h+v))) at hRt
  change |ZeroCount.v1.zetaNClosed 3000000000000-ZeroCount.v1.rvmMain 3000000000000|≤
    rosserError h at hRh
  rw [log_exp] at hRt
  have hdiff:ZeroCount.v1.zetaNClosed (exp (h+v))-ZeroCount.v1.zetaNClosed 3000000000000≤
      (ZeroCount.v1.rvmMain (exp (h+v))-ZeroCount.v1.rvmMain 3000000000000)+
        (rosserError (h+v)+rosserError h):=by
    have ht:=(abs_le.mp hRt).2
    have hh:=(abs_le.mp hRh).1
    linarith
  have hd:=div_le_div_of_nonneg_right hdiff (show 0≤2*exp (h+v) by positivity)
  have he:((ZeroCount.v1.rvmMain (exp (h+v))-ZeroCount.v1.rvmMain 3000000000000)+
      (rosserError (h+v)+rosserError h))/(2*exp (h+v))=windowAllowance v:=by
    rw [add_div,windowMain_exact]
    unfold windowAllowance
    rw [exp_neg]
    ring
  exact hhalf.trans (hd.trans_eq he)

/-- The original strict-height count is included in the actual closed count. -/
theorem open_le_closed {sigma T:ℝ} :
    IEANTN.zetaN' sigma T≤IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 T) (fun _↦(1:ℝ)) := by
  classical
  have hc:=finite_zero_rectangle (Ioo sigma 1) (T:=T)
  have ho:(IEANTN.zetaZeroesIn (Ioo sigma 1) (Ioo 0 T)).Finite:=
    hc.subset (fun rho hr=>⟨hr.1,⟨hr.2.1.1,hr.2.1.2.le⟩,hr.2.2⟩)
  unfold IEANTN.zetaN'
  rw [rectangle_sum_eq ho,rectangle_sum_eq hc]
  simp only [one_mul]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hr
    have hz:=(Set.Finite.mem_toFinset ho).mp hr
    exact (Set.Finite.mem_toFinset hc).mpr ⟨hz.1,⟨hz.2.1.1,hz.2.1.2.le⟩,hz.2.2⟩
  · intro rho hr _
    have hz:=(Set.Finite.mem_toFinset hc).mp hr
    exact CH2Section7Z.zetaOrder_nonneg_of_mem (J:=Ioc 0 T) Ioc_subset_Ioi_self
      ⟨trivial,hz.2.1,hz.2.2⟩

theorem open_windowAllowance (hRosser:OriginalSharpRosser)
    (hRH:IEANTN.RiemannHypothesisUpTo 3000000000000)
    {sigma v:ℝ} (hs:(1/2:ℝ)≤ sigma) (hv:0≤v) :
    IEANTN.zetaN' sigma (exp (h+v))/exp (h+v)≤windowAllowance v :=
  (div_le_div_of_nonneg_right open_le_closed (exp_pos _).le).trans
    (closed_windowAllowance hRosser hRH hs hv)
#print axioms closed_windowAllowance
#print axioms open_windowAllowance
end WinnerHalfWindow

import SynergyAnalytic.ActualHeightCaps
import SynergyAnalytic.SourceOrdinate
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerNewHeightSource WinnerDensityA CH2QRH
set_option maxHeartbeats 0

/-- Full actual ordinate-weight provider for every future CHJ truncation
height. Count at t, reciprocal sums, finite grid, infinite tail and boundary
terms are all connected to the original analytic inputs. -/
theorem source_ordinate_from_count_cells {a c D : ℕ→ℝ} {n : ℕ} {sigma t : ℝ}
    (ha : Monotone a) (ha0 : a 0=WinnerOriginalScalars.height) (han : a n=Real.exp 60)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hcells : ActualHeightCaps a c D n) (hRH : IEANTN.RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (ht : Real.exp 110 ≤ t) :
    (2*Real.pi/t)*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t)
      (fun rho=>t/Real.pi*(1/rho.im)+2) ≤ ordinateProfile a c D n sigma := by
  have hcaps := tangent256_universal_basis_caps
  have hH : WinnerOriginalScalars.height ≤ Real.exp (110:ℝ) := by
    calc
      WinnerOriginalScalars.height = Real.exp (Real.log WinnerOriginalScalars.height) :=
        (Real.exp_log (by norm_num [WinnerOriginalScalars.height] : (0:ℝ)<WinnerOriginalScalars.height)).symm
      _ ≤ Real.exp 110 := Real.exp_le_exp.mpr (source_log_le32.trans (by norm_num))
  have htH := hH.trans ht
  have ht0 : 0<t := (Real.exp_pos 110).trans_le ht
  have hrec := source_reciprocal_from_count_cells ha ha0 han h hcaps (hcells sigma hs hs') hRH hs hs' htH
  have hcount := source_coarse_density_closed h hcaps hRH hs hs' htH
  have hmono := WinnerDensityA.boundary_antitone (by norm_num : (0:ℝ) ≤ 2000)
    (by norm_num : (0:ℝ) ≤ 6) hs hs'
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<110))
    (by rw [Real.log_exp];norm_num : (28:ℝ) ≤ Real.log (Real.exp 110))
  have hcountSmall : 4*Real.pi/t*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun _=>(1:ℝ)) ≤
      (1/1000000000000:ℝ)*Real.exp ((880/3:ℝ)*((7/8)-sigma))+1/1000000000000 := by
    have hdiv := div_le_div_of_nonneg_right hcount ht0.le
    have hsub := hdiv.trans (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht)
    have hm := mul_le_mul_of_nonneg_left hsub (show 0 ≤ 4*Real.pi by positivity)
    apply LE.le.trans _ (count_boundary_affine hs hs')
    convert hm using 1 <;> first | rfl | ring
  have hfin := finite_zero_rectangle (Ioo sigma 1) (T:=t)
  have he : (2*Real.pi/t)*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t)
      (fun rho=>t/Real.pi*(1/rho.im)+2) =
      2*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun rho=>1/rho.im)+
        4*Real.pi/t*IEANTN.zetaZeroesSum (Ioo sigma 1) (Ioc 0 t) (fun _=>(1:ℝ)) := by
    rw [rectangle_sum_eq hfin,rectangle_sum_eq hfin,rectangle_sum_eq hfin,
      Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    field_simp
    <;> ring
  rw [he]
  unfold ordinateProfile
  nlinarith [hrec,hcountSmall]

#print axioms source_ordinate_from_count_cells
end SynergyAnalytic

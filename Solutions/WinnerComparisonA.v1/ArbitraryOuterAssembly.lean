/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import OuterAssembly
namespace WinnerOldOuter.Arbitrary
open Real Set MeasureTheory WinnerOldOuter.Assembly
set_option maxHeartbeats 0

/-- Arbitrary independently proved source operands for each actual height cell. -/
noncomputable def cellProfile (K beta den:ℝ) (c:CellData) (sigma:ℝ) : ℝ :=
  exp (K*(sigma-beta))*(c.ul*(c.zl*exp (c.Bl*(beta-sigma)))-
    c.ur*(c.zu*exp (c.Bu*(beta-sigma)))^2/(2*c.rmin))/den
noncomputable def closedMass (K width den:ℝ) (c:CellData) : ℝ :=
  (c.ul*c.zl*WinnerOldAnalytic.expMass (K-c.Bl) width-
    c.ur*c.zu^2/(2*c.rmin)*WinnerOldAnalytic.expMass (K-2*c.Bu) width)/den

theorem cell_continuous (K beta den:ℝ) (c:CellData) :
    Continuous (cellProfile K beta den c) := by
  unfold cellProfile
  fun_prop

theorem cell_mass {K beta width den:ℝ} (c:CellData)
    (hBl:K-c.Bl≠0) (hBu:K-2*c.Bu≠0) :
    (∫sigma in (beta-width)..beta,cellProfile K beta den c sigma)=closedMass K width den c :=
  WinnerOldAnalytic.weighted_polynomial_mass hBl hBu

/-- A height grid with arbitrary per-cell operands, exact sigma integration,
and no source/domain or desired incumbent lower-bound oracle. -/
theorem row_integral_lower {F:ℝ→ℝ→ℝ} {K beta width den v0 step:ℝ} {n:ℕ}
    (D:ℕ→CellData) (hw:0≤width) (hs:0≤step)
    (hBl:∀k<n,K-(D k).Bl≠0) (hBu:∀k<n,K-2*(D k).Bu≠0)
    (hInner:∀v∈Icc v0 (v0+step*n),
      IntervalIntegrable (fun sigma=>F sigma v) volume (beta-width) beta)
    (hOuter:∀k<n,IntervalIntegrable
      (fun v=>∫sigma in (beta-width)..beta,F sigma v) volume
      (v0+step*k) (v0+step*(k+1)))
    (hLower:∀k<n,∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (beta-width) beta,cellProfile K beta den (D k) sigma≤F sigma v) :
    (∑k∈Finset.range n,600*step*closedMass K width den (D k))≤
      600*(∫v in v0..(v0+step*n),∫sigma in (beta-width)..beta,F sigma v) := by
  let edge:ℕ→ℝ:=fun k=>v0+step*k
  let G:ℝ→ℝ:=fun v=>∫sigma in (beta-width)..beta,F sigma v
  have hOuter':∀k<n,IntervalIntegrable G volume (edge k) (edge (k+1)):=by
    intro k hk
    simpa only [edge,G,Nat.cast_add,Nat.cast_one] using hOuter k hk
  have hb:∀k∈Finset.range n,600*step*closedMass K width den (D k)≤
      600*(∫v in edge k..edge (k+1),G v):=by
    intro k hk
    have hkn:k<n:=Finset.mem_range.mp hk
    have hed:edge k≤edge (k+1):=by dsimp [edge];push_cast;nlinarith
    have hsub:∀v∈Icc (edge k) (edge (k+1)),v∈Icc v0 (v0+step*n):=by
      intro v hv
      have hkn':(k:ℝ)+1≤n:=by exact_mod_cast Nat.succ_le_of_lt hkn
      have hl:v0≤edge k:=by dsimp [edge];nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
      have hr:edge (k+1)≤v0+step*n:=by
        dsimp [edge]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hkn' hs]
      exact ⟨hl.trans hv.1,hv.2.trans hr⟩
    have hvbound:∀v∈Icc (edge k) (edge (k+1)),closedMass K width den (D k)≤G v:=by
      intro v hv
      rw [←cell_mass (beta:=beta) (D k) (hBl k hkn) (hBu k hkn)]
      apply intervalIntegral.integral_mono_on (by linarith)
        ((cell_continuous K beta den (D k)).intervalIntegrable _ _) (hInner v (hsub v hv))
      exact hLower k hkn v (by simpa only [edge,Nat.cast_add,Nat.cast_one] using hv)
    have hrect:=intervalIntegral.integral_mono_on hed
      (intervalIntegrable_const:IntervalIntegrable (fun _:ℝ=>closedMass K width den (D k)) volume _ _)
      (hOuter' k hkn) hvbound
    rw [intervalIntegral.integral_const] at hrect
    have he:edge (k+1)-edge k=step:=by dsimp [edge];push_cast;ring
    simp only [he,smul_eq_mul] at hrect
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrect (by norm_num:(0:ℝ)≤600)
  have hsum:=Finset.sum_le_sum hb
  have he:(∑k∈Finset.range n,600*(∫v in edge k..edge (k+1),G v))=
      600*(∫v in edge 0..edge n,G v):=by
    rw [←Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals hOuter']
  rw [he] at hsum
  simpa only [edge,G,Nat.cast_zero,mul_zero,add_zero] using hsum

/-- Joint compact continuity discharges both interval convergence inputs. -/
theorem row_lower_of_continuous {F:ℝ→ℝ→ℝ} {K beta width den v0 step:ℝ} {n:ℕ}
    (D:ℕ→CellData) (hw:0≤width) (hs:0≤step)
    (hBl:∀k<n,K-(D k).Bl≠0) (hBu:∀k<n,K-2*(D k).Bu≠0)
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2)
      (Icc (beta-width) beta×ˢ Icc v0 (v0+step*n)))
    (hLower:∀k<n,∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (beta-width) beta,cellProfile K beta den (D k) sigma≤F sigma v) :
    (∑k∈Finset.range n,600*step*closedMass K width den (D k))≤
      600*(∫v in v0..(v0+step*n),∫sigma in (beta-width)..beta,F sigma v) := by
  have hend:v0≤v0+step*n:=by nlinarith [mul_nonneg hs (Nat.cast_nonneg n)]
  obtain ⟨hInner,hG⟩:=rectangle_integrability (by linarith) hend hF
  apply row_integral_lower D hw hs hBl hBu hInner ?_ hLower
  intro k hk
  have hkn:(k:ℝ)+1≤n:=by exact_mod_cast Nat.succ_le_of_lt hk
  have h1:v0≤v0+step*k:=by nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
  have h2:v0+step*(k+1)≤v0+step*n:=by nlinarith [mul_le_mul_of_nonneg_left hkn hs]
  apply (hG.mono (Icc_subset_Icc h1 h2)).intervalIntegrable_of_Icc
  nlinarith

/-- Arbitrary cell data and width, in the sigma-first order of the old source
functional. Fubini follows from actual compact-rectangle continuity. -/
theorem row_sigma_first {F:ℝ→ℝ→ℝ} {K beta width den v0 step:ℝ} {n:ℕ}
    (D:ℕ→CellData) (hw:0≤width) (hs:0≤step)
    (hBl:∀k<n,K-(D k).Bl≠0) (hBu:∀k<n,K-2*(D k).Bu≠0)
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2)
      (Icc (beta-width) beta×ˢ Icc v0 (v0+step*n)))
    (hLower:∀k<n,∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (beta-width) beta,cellProfile K beta den (D k) sigma≤F sigma v) :
    (∑k∈Finset.range n,600*step*closedMass K width den (D k))≤
      600*(∫sigma in (beta-width)..beta,∫v in v0..(v0+step*n),F sigma v) := by
  have h:=row_lower_of_continuous D hw hs hBl hBu hF hLower
  rw [rectangle_integral_swap (by linarith) (by nlinarith [mul_nonneg hs (Nat.cast_nonneg n)]) hF] at h
  exact h

/-- Nonnegative actual F allows a narrower certified sigma strip in one
height row to contribute to a common wider rectangle. Both convergence and
Fubini are derived from joint continuity on that wider rectangle. -/
theorem row_into_wider_rectangle {F:ℝ→ℝ→ℝ}
    {K beta width wholeWidth den v0 step:ℝ} {n:ℕ}
    (D:ℕ→CellData) (hw:0≤width) (hww:width≤wholeWidth) (hs:0≤step)
    (hBl:∀k<n,K-(D k).Bl≠0) (hBu:∀k<n,K-2*(D k).Bu≠0)
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2)
      (Icc (beta-wholeWidth) beta×ˢ Icc v0 (v0+step*n)))
    (hNonneg:∀sigma∈Icc (beta-wholeWidth) beta,∀v∈Icc v0 (v0+step*n),0≤F sigma v)
    (hLower:∀k<n,∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (beta-width) beta,cellProfile K beta den (D k) sigma≤F sigma v) :
    (∑k∈Finset.range n,600*step*closedMass K width den (D k))≤
      600*(∫sigma in (beta-wholeWidth)..beta,∫v in v0..(v0+step*n),F sigma v) := by
  have hend:v0≤v0+step*n:=by nlinarith [mul_nonneg hs (Nat.cast_nonneg n)]
  have hFsmall:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2)
      (Icc (beta-width) beta×ˢ Icc v0 (v0+step*n)):=
    hF.mono (Set.prod_mono (Icc_subset_Icc (by linarith) le_rfl) Subset.rfl)
  have hrow:=row_lower_of_continuous D hw hs hBl hBu hFsmall hLower
  obtain ⟨hInnerSmall,hGsmall⟩:=rectangle_integrability (by linarith) hend hFsmall
  obtain ⟨hInnerWhole,hGwhole⟩:=rectangle_integrability (by linarith) hend hF
  have hpoint:∀v∈Icc v0 (v0+step*n),
      (∫sigma in (beta-width)..beta,F sigma v)≤
        ∫sigma in (beta-wholeWidth)..beta,F sigma v:=by
    intro v hv
    have hc:ContinuousOn (fun sigma=>F sigma v) (Icc (beta-wholeWidth) beta):=
      hF.comp (continuousOn_id.prodMk continuousOn_const) (fun sigma hsig=>⟨hsig,hv⟩)
    have hleft:IntervalIntegrable (fun sigma=>F sigma v) volume (beta-wholeWidth) (beta-width):=
      (hc.mono (Icc_subset_Icc le_rfl (by linarith))).intervalIntegrable_of_Icc (by linarith)
    have hleft0:0≤∫sigma in (beta-wholeWidth)..(beta-width),F sigma v:=by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro sigma hsig
      exact hNonneg sigma ⟨hsig.1,hsig.2.trans (by linarith)⟩ v hv
    have he:=intervalIntegral.integral_add_adjacent_intervals hleft (hInnerSmall v hv)
    linarith
  have hi:=intervalIntegral.integral_mono_on (μ:=volume) hend
    (hGsmall.intervalIntegrable_of_Icc hend) (hGwhole.intervalIntegrable_of_Icc hend) hpoint
  have hh:=hrow.trans (mul_le_mul_of_nonneg_left hi (by norm_num:(0:ℝ)≤600))
  rw [rectangle_integral_swap (by linarith) hend hF] at hh
  exact hh
#print axioms row_into_wider_rectangle

#print axioms row_sigma_first
end WinnerOldOuter.Arbitrary

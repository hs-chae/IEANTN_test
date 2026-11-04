/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldOuterSemantics
import Section7Vihuela
import Mathlib.MeasureTheory.Integral.Prod
namespace WinnerOldOuter.Assembly
open Real Set MeasureTheory
set_option maxHeartbeats 0

structure CellData where
  ul : ℝ
  ur : ℝ
  zl : ℝ
  zu : ℝ
  Bl : ℝ
  Bu : ℝ
  rmin : ℝ

noncomputable def rowData (v0 step U V : ℝ) (k : ℕ) : CellData :=
  let vl := v0+step*k
  let vr := vl+step
  let ul := log 3000000000000+vl
  let ur := log 3000000000000+vr
  let dl := log (U/V)+log ul+4*ul/3
  let dr := log (U/V)+log ur+4*ur/3
  let p := 2*(3663/10000)+2*(3599/10000)*(2*(7/8)-1)
  let al := 1/4+p/(ur+3599/5000)
  let au := 1/4+p/(ul+3599/5000)
  { ul := ul, ur := ur,
    zl := (499999/1000000)*exp (2371/10000+al*dl+log V+2*log ul-ur),
    zu := (501/1000)*exp (2371/10000+au*dr+log V+2*log ur-ul),
    Bl := (2-(3599/2500)/(ur+3599/5000))*dl,
    Bu := (2-(3599/2500)/(ul+3599/5000))*dr,
    rmin := 1-exp (-vl) }

noncomputable def profile (c : CellData) (sigma : ℝ) : ℝ :=
  exp ((601/2:ℝ)*(sigma-7/8))*
    (c.ul*(c.zl*exp (c.Bl*(7/8-sigma)))-
      c.ur*(c.zu*exp (c.Bu*(7/8-sigma)))^2/(2*c.rmin))/((3663/5000)*Real.pi)
noncomputable def cellLower (v0 step U V : ℝ) (k : ℕ) : ℝ → ℝ :=
  profile (rowData v0 step U V k)

theorem profile_continuous (c : CellData) : Continuous (profile c) := by
  unfold profile
  fun_prop

theorem height_log_bounds : (28:ℝ)≤log 3000000000000 ∧ log 3000000000000≤29 := by
  constructor
  · apply exp_le_exp.mp
    rw [exp_log (by norm_num : (0:ℝ)<3000000000000)]
    exact (CH2Section7A.exp_nat_bounds 28).2.trans (by norm_num)
  · apply (log_le_iff_le_exp (by norm_num : (0:ℝ)<3000000000000)).mpr
    exact le_trans (by norm_num) (CH2Section7A.exp_nat_bounds 29).1

private theorem d_bounds {U V u : ℝ} (hU : 1≤U) (hUV : U≤V) (hV : V≤8)
    (hu : (28:ℝ)≤u) (hu' : u≤37) :
    0≤log (U/V)+log u+4*u/3 ∧ log (U/V)+log u+4*u/3≤407/6 := by
  have hUp : 0<U := by linarith
  have hVp : 0<V := by linarith
  have hup : 0<u := by linarith
  have hrat : U/V≤1 := (div_le_one hVp).mpr hUV
  have hlr : log (U/V)≤0 := log_nonpos (div_pos hUp hVp).le hrat
  have hlow : -7≤log (U/V) := by
    rw [log_div hUp.ne' hVp.ne']
    have h1 := log_nonneg hU
    have h2 := log_le_sub_one_of_pos hVp
    linarith
  have hlu : 0≤log u := log_nonneg (by linarith)
  have hlup : log u≤u/2 := by
    have h1 := log_le_sub_one_of_pos (show 0<u/2 by positivity)
    rw [log_div hup.ne' (by norm_num : (2:ℝ)≠0)] at h1
    have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  constructor <;> linarith

theorem row_exponents {v0 step U V : ℝ} {n k : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hmax : v0+step*n≤8)
    (hU : 1≤U) (hUV : U≤V) (hV : V≤8) (hk : k<n) :
    (601/2:ℝ)-(rowData v0 step U V k).Bl≠0 ∧
      (601/2:ℝ)-2*(rowData v0 step U V k).Bu≠0 := by
  have hkn : (k:ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt hk)
  have hvl : 0≤v0+step*k := by positivity
  have hvr : v0+step*k+step≤8 := by
    have hm := mul_le_mul_of_nonneg_left hkn hs
    linarith
  have hlog := height_log_bounds
  have hul : (28:ℝ)≤log 3000000000000+(v0+step*k) := by linarith
  have hur : log 3000000000000+(v0+step*k+step)≤37 := by linarith
  have hul' : log 3000000000000+(v0+step*k)≤37 := by linarith
  have hur' : (28:ℝ)≤log 3000000000000+(v0+step*k+step) := by linarith
  have hdl := d_bounds hU hUV hV hul hul'
  have hdr := d_bounds hU hUV hV hur' hur
  have hfl : 2-(3599/2500:ℝ)/(log 3000000000000+(v0+step*k+step)+3599/5000)≤2 := by
    have hp : 0≤(3599/2500:ℝ)/(log 3000000000000+(v0+step*k+step)+3599/5000) := by positivity
    linarith
  have hfr : 2-(3599/2500:ℝ)/(log 3000000000000+(v0+step*k)+3599/5000)≤2 := by
    have hp : 0≤(3599/2500:ℝ)/(log 3000000000000+(v0+step*k)+3599/5000) := by positivity
    linarith
  have hb1 := mul_le_mul_of_nonneg_right hfl hdl.1
  have hb2 := mul_le_mul_of_nonneg_right hfr hdr.1
  dsimp only [rowData]
  constructor
  · nlinarith [hdl.2]
  · nlinarith [hdr.2]

theorem cell_mass {v0 step U V : ℝ} {n k : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hmax : v0+step*n≤8)
    (hU : 1≤U) (hUV : U≤V) (hV : V≤8) (hk : k<n) :
    (600:ℝ)*step*(∫ sigma in (17/20:ℝ)..(7/8:ℝ),cellLower v0 step U V k sigma) =
      WinnerOldOuter.outerCellReal v0 step U V k := by
  obtain ⟨hb1,hb2⟩ := row_exponents hv hs hmax hU hUV hV hk
  have hh := WinnerOldAnalytic.weighted_polynomial_mass
    (beta:=(7/8:ℝ)) (width:=(1/40:ℝ)) (den:=((3663/5000:ℝ)*Real.pi))
    (ul:=(rowData v0 step U V k).ul) (ur:=(rowData v0 step U V k).ur)
    (zl:=(rowData v0 step U V k).zl) (zu:=(rowData v0 step U V k).zu)
    (rmin:=(rowData v0 step U V k).rmin) hb1 hb2
  norm_num only [show (7/8:ℝ)-1/40=17/20 by norm_num] at hh
  change 600*step*(∫ sigma in (17/20:ℝ)..(7/8:ℝ),
    exp ((601/2:ℝ)*(sigma-7/8))*
      ((rowData v0 step U V k).ul*((rowData v0 step U V k).zl*exp ((rowData v0 step U V k).Bl*(7/8-sigma)))-
        (rowData v0 step U V k).ur*((rowData v0 step U V k).zu*exp ((rowData v0 step U V k).Bu*(7/8-sigma)))^2/
          (2*(rowData v0 step U V k).rmin))/((3663/5000)*Real.pi)) = _
  rw [hh]
  unfold WinnerOldOuter.outerCellReal rowData
  dsimp only
  ring

/-- A generic height grid and exact sigma integration connect the independent
pointwise cell provider to the actual double integral.  No incumbent lower
value or finite certificate is a hypothesis. -/
theorem row_integral_lower {F : ℝ → ℝ → ℝ} {v0 step U V : ℝ} {n : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hmax : v0+step*n≤8)
    (hU : 1≤U) (hUV : U≤V) (hV : V≤8)
    (hInner : ∀v∈Icc v0 (v0+step*n),
      IntervalIntegrable (fun sigma => F sigma v) volume (17/20) (7/8))
    (hOuter : ∀k<n, IntervalIntegrable
      (fun v => ∫ sigma in (17/20:ℝ)..(7/8:ℝ), F sigma v) volume
        (v0+step*k) (v0+step*(k+1)))
    (hLower : ∀k<n, ∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (17/20:ℝ) (7/8), cellLower v0 step U V k sigma≤F sigma v) :
    (∑ k∈Finset.range n, WinnerOldOuter.outerCellReal v0 step U V k) ≤
      600*(∫v in v0..(v0+step*n), ∫sigma in (17/20:ℝ)..(7/8:ℝ), F sigma v) := by
  let edge : ℕ→ℝ := fun k => v0+step*k
  let G : ℝ→ℝ := fun v => ∫sigma in (17/20:ℝ)..(7/8:ℝ), F sigma v
  have hOuter' : ∀ k<n, IntervalIntegrable G volume (edge k) (edge (k+1)) := by
    intro k hk
    simpa only [edge,G,Nat.cast_add,Nat.cast_one] using hOuter k hk
  have hb : ∀ k∈Finset.range n, WinnerOldOuter.outerCellReal v0 step U V k ≤
      600*(∫ v in edge k..edge (k+1), G v) := by
    intro k hk
    have hkn : k<n := Finset.mem_range.mp hk
    have hed : edge k≤edge (k+1) := by dsimp [edge];push_cast;nlinarith
    have hsub : ∀v∈Icc (edge k) (edge (k+1)), v∈Icc v0 (v0+step*n) := by
      intro v hmem
      have hkn' : (k:ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt hkn)
      have hleft : v0≤edge k := by dsimp [edge];nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
      have hright : edge (k+1)≤v0+step*n := by
        dsimp [edge]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hkn' hs]
      exact ⟨hleft.trans hmem.1,hmem.2.trans hright⟩
    have hvbound : ∀v∈Icc (edge k) (edge (k+1)),
        (∫sigma in (17/20:ℝ)..(7/8:ℝ), cellLower v0 step U V k sigma)≤G v := by
      intro v hvv
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((profile_continuous _).intervalIntegrable _ _) (hInner v (hsub v hvv))
      exact hLower k hkn v (by
        simpa only [edge,Nat.cast_add,Nat.cast_one] using hvv)
    have hrect := intervalIntegral.integral_mono_on hed
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ => ∫sigma in (17/20:ℝ)..(7/8:ℝ), cellLower v0 step U V k sigma) volume _ _)
      (hOuter' k hkn) hvbound
    rw [intervalIntegral.integral_const] at hrect
    have hstep : edge (k+1)-edge k=step := by dsimp [edge];push_cast;ring
    simp only [hstep,smul_eq_mul] at hrect
    rw [←cell_mass hv hs hmax hU hUV hV hkn]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrect (by norm_num : (0:ℝ)≤600)
  have hsum := Finset.sum_le_sum hb
  rw [←Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals hOuter'] at hsum
  simpa only [edge,G,Nat.cast_zero,mul_zero,add_zero] using hsum

/-- Joint continuity on the actual compact rectangle supplies both section
integrability and outer-integral continuity, with a proved uniform bound. -/
theorem rectangle_integrability {F : ℝ→ℝ→ℝ} {a b v0 v1 : ℝ}
    (hab : a≤b) (hv : v0≤v1)
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2) (Icc a b ×ˢ Icc v0 v1)) :
    (∀v∈Icc v0 v1, IntervalIntegrable (fun sigma => F sigma v) volume a b) ∧
    ContinuousOn (fun v => ∫sigma in a..b,F sigma v) (Icc v0 v1) := by
  have hsec : ∀v∈Icc v0 v1, ContinuousOn (fun sigma => F sigma v) (Icc a b) := by
    intro v hvv
    exact hF.comp (continuousOn_id.prodMk continuousOn_const) (fun sigma hs => ⟨hs,hvv⟩)
  have hsecv : ∀sigma∈Icc a b, ContinuousOn (fun v => F sigma v) (Icc v0 v1) := by
    intro sigma hs
    exact hF.comp (continuousOn_const.prodMk continuousOn_id) (fun v hvv => ⟨hs,hvv⟩)
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF
  refine ⟨fun v hvv => (hsec v hvv).intervalIntegrable_of_Icc hab,?_⟩
  intro v hvv
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound:=fun _ : ℝ => B)
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact ((hsec w hw).intervalIntegrable_of_Icc hab).def'.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact Filter.Eventually.of_forall fun sigma hs => by
      rw [uIoc_of_le hab] at hs
      exact hB (sigma,w) ⟨⟨hs.1.le,hs.2⟩,hw⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun sigma hs => by
      rw [uIoc_of_le hab] at hs
      exact (hsecv sigma ⟨hs.1.le,hs.2⟩) v hvv

theorem row_lower_of_continuous {F : ℝ→ℝ→ℝ} {v0 step U V : ℝ} {n : ℕ}
    (hv : 0≤v0) (hs : 0≤step) (hmax : v0+step*n≤8)
    (hU : 1≤U) (hUV : U≤V) (hV : V≤8)
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2)
      (Icc (17/20:ℝ) (7/8) ×ˢ Icc v0 (v0+step*n)))
    (hLower : ∀k<n, ∀v∈Icc (v0+step*k) (v0+step*(k+1)),
      ∀sigma∈Icc (17/20:ℝ) (7/8), cellLower v0 step U V k sigma≤F sigma v) :
    (∑ k∈Finset.range n, WinnerOldOuter.outerCellReal v0 step U V k) ≤
      600*(∫v in v0..(v0+step*n), ∫sigma in (17/20:ℝ)..(7/8:ℝ), F sigma v) := by
  have hend : v0≤v0+step*n := by nlinarith [mul_nonneg hs (Nat.cast_nonneg n)]
  obtain ⟨hInner,hG⟩ := rectangle_integrability (by norm_num : (17/20:ℝ)≤7/8) hend hF
  apply row_integral_lower hv hs hmax hU hUV hV hInner ?_ hLower
  intro k hk
  have hkn : (k:ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt hk)
  have h1 : v0≤v0+step*k := by nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
  have h2 : v0+step*(k+1)≤v0+step*n := by nlinarith [mul_le_mul_of_nonneg_left hkn hs]
  apply (hG.mono (Icc_subset_Icc h1 h2)).intervalIntegrable_of_Icc
  nlinarith

def RowProvider (F : ℝ→ℝ→ℝ) (v0 step U V : ℝ) (n : ℕ) : Prop :=
  ∀k<n, ∀v∈Icc (v0+step*k) (v0+step*(k+1)),
    ∀sigma∈Icc (17/20:ℝ) (7/8), cellLower v0 step U V k sigma≤F sigma v

/-- Four actual height rows, with all shared rectangle convergence discharged
by one joint-continuity hypothesis.  Pointwise old-function providers remain
independent proof obligations, to be supplied by the source comparison. -/
theorem four_rows_integral_lower {F : ℝ→ℝ→ℝ}
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2)
      (Icc (17/20:ℝ) (7/8) ×ˢ Icc (13/1000:ℝ) 8))
    (h0 : RowProvider F (13/1000) (987/494000) (1698779/1000000) (36/5) 494)
    (h1 : RowProvider F 1 (1/500) (336493/200000) (719/100) 500)
    (h2 : RowProvider F 2 (1/500) (1652763/1000000) (179/25) 1000)
    (h3 : RowProvider F 4 (1/500) (1602809/1000000) (178/25) 2000) :
    WinnerOldOuter.finiteLower ≤
      600*(∫v in (13/1000:ℝ)..8, ∫sigma in (17/20:ℝ)..(7/8:ℝ), F sigma v) := by
  have hFsub {a b : ℝ} (ha : (13/1000:ℝ)≤a) (hb : b≤8) :
      ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2) (Icc (17/20:ℝ) (7/8) ×ˢ Icc a b) := by
    apply hF.mono
    exact Set.prod_mono Subset.rfl (Icc_subset_Icc ha hb)
  have r0 := row_lower_of_continuous (F:=F) (v0:=(13/1000:ℝ)) (step:=(987/494000:ℝ))
    (U:=(1698779/1000000:ℝ)) (V:=(36/5:ℝ)) (n:=494)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by convert hFsub (a:=13/1000) (b:=1) (by norm_num) (by norm_num) using 1 <;> norm_num) h0
  have r1 := row_lower_of_continuous (F:=F) (v0:=1) (step:=(1/500:ℝ))
    (U:=(336493/200000:ℝ)) (V:=(719/100:ℝ)) (n:=500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by convert hFsub (a:=1) (b:=2) (by norm_num) (by norm_num) using 1 <;> norm_num) h1
  have r2 := row_lower_of_continuous (F:=F) (v0:=2) (step:=(1/500:ℝ))
    (U:=(1652763/1000000:ℝ)) (V:=(179/25:ℝ)) (n:=1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by convert hFsub (a:=2) (b:=4) (by norm_num) (by norm_num) using 1 <;> norm_num) h2
  have r3 := row_lower_of_continuous (F:=F) (v0:=4) (step:=(1/500:ℝ))
    (U:=(1602809/1000000:ℝ)) (V:=(178/25:ℝ)) (n:=2000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by convert hFsub (a:=4) (b:=8) (by norm_num) (by norm_num) using 1 <;> norm_num) h3
  norm_num only [Nat.cast_ofNat] at r0 r1 r2 r3
  norm_num only [show (13/1000:ℝ)+(987/494000)*494=1 by norm_num] at r0
  norm_num only [show (1:ℝ)+(1/500)*500=2 by norm_num] at r1
  norm_num only [show (2:ℝ)+(1/500)*1000=4 by norm_num] at r2
  norm_num only [show (4:ℝ)+(1/500)*2000=8 by norm_num] at r3
  let G : ℝ→ℝ := fun v => ∫sigma in (17/20:ℝ)..(7/8:ℝ),F sigma v
  have hGc := (rectangle_integrability (by norm_num : (17/20:ℝ)≤7/8)
    (by norm_num : (13/1000:ℝ)≤8) hF).2
  have hi {a b : ℝ} (ha : (13/1000:ℝ)≤a) (hb : b≤8) (hab : a≤b) :
      IntervalIntegrable G volume a b :=
    (hGc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have he1 := intervalIntegral.integral_add_adjacent_intervals
    (hi (a:=13/1000) (b:=1) (by norm_num) (by norm_num) (by norm_num))
    (hi (a:=1) (b:=2) (by norm_num) (by norm_num) (by norm_num))
  have he2 := intervalIntegral.integral_add_adjacent_intervals
    (hi (a:=13/1000) (b:=2) (by norm_num) (by norm_num) (by norm_num))
    (hi (a:=2) (b:=4) (by norm_num) (by norm_num) (by norm_num))
  have he3 := intervalIntegral.integral_add_adjacent_intervals
    (hi (a:=13/1000) (b:=4) (by norm_num) (by norm_num) (by norm_num))
    (hi (a:=4) (b:=8) (by norm_num) (by norm_num) (by norm_num))
  have hsum : (∫v in (13/1000:ℝ)..1,G v)+(∫v in (1:ℝ)..2,G v)+
      (∫v in (2:ℝ)..4,G v)+(∫v in (4:ℝ)..8,G v)=∫v in (13/1000:ℝ)..8,G v := by
    rw [he1,he2,he3]
  have hicc (n : ℕ) (hn : 0<n) : Finset.Icc 0 (n-1)=Finset.range n := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_range]
    omega
  unfold WinnerOldOuter.finiteLower
  rw [hicc 494 (by decide),hicc 500 (by decide),hicc 1000 (by decide),hicc 2000 (by decide)]
  dsimp only [G] at hsum
  linarith

/-- The actual compact rectangle, rather than an assumed interchange oracle,
supplies Fubini and allows the source functional's sigma-first order. -/
theorem rectangle_integral_swap {F : ℝ→ℝ→ℝ} {a b v0 v1 : ℝ}
    (hab : a≤b) (hv : v0≤v1)
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2) (Icc a b ×ˢ Icc v0 v1)) :
    (∫v in v0..v1,∫sigma in a..b,F sigma v)=
      ∫sigma in a..b,∫v in v0..v1,F sigma v := by
  have hClosed : IntegrableOn (fun p : ℝ×ℝ => F p.1 p.2)
      (Icc a b ×ˢ Icc v0 v1) (volume.prod volume) :=
    hF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hInt : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc v0 v1))) := by
    rw [Measure.prod_restrict]
    exact hClosed.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hh := MeasureTheory.integral_integral_swap hInt
  simpa only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hv] using hh.symm

theorem four_rows_sigma_first {F : ℝ→ℝ→ℝ}
    (hF : ContinuousOn (fun p : ℝ×ℝ => F p.1 p.2)
      (Icc (17/20:ℝ) (7/8) ×ˢ Icc (13/1000:ℝ) 8))
    (h0 : RowProvider F (13/1000) (987/494000) (1698779/1000000) (36/5) 494)
    (h1 : RowProvider F 1 (1/500) (336493/200000) (719/100) 500)
    (h2 : RowProvider F 2 (1/500) (1652763/1000000) (179/25) 1000)
    (h3 : RowProvider F 4 (1/500) (1602809/1000000) (178/25) 2000) :
    WinnerOldOuter.finiteLower ≤
      600*(∫sigma in (17/20:ℝ)..(7/8:ℝ),∫v in (13/1000:ℝ)..8,F sigma v) := by
  have h := four_rows_integral_lower hF h0 h1 h2 h3
  rw [rectangle_integral_swap (by norm_num) (by norm_num) hF] at h
  exact h

#print axioms rectangle_integral_swap
#print axioms four_rows_sigma_first

#print axioms rectangle_integrability
#print axioms four_rows_integral_lower

#print axioms cell_mass
#print axioms row_integral_lower
end WinnerOldOuter.Assembly

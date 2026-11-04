/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import ArbitraryOuterAssembly
namespace WinnerOldOuter.Warm
open Real Set MeasureTheory WinnerOldOuter.Assembly
set_option maxHeartbeats 0
noncomputable def bandProfile (K beta qStep B M:ℝ) (j:ℕ) (sigma:ℝ) : ℝ :=
  exp (K*(sigma-beta))*M*exp (-B*(qStep*(j+1)))*exp (B*(beta-sigma))
noncomputable def bandMass (K qStep B M:ℝ) (j:ℕ) : ℝ :=
  M*exp (-B*(qStep*(j+1)))*
    ((exp (-(K-B)*(qStep*j))-exp (-(K-B)*(qStep*(j+1))))/(K-B))

theorem band_continuous (K beta qStep B M:ℝ) (j:ℕ) :
    Continuous (bandProfile K beta qStep B M j) := by
  unfold bandProfile
  fun_prop

/-- The finite program's band operand is the exact sigma integral. -/
theorem band_mass {K beta qStep B M:ℝ} (j:ℕ) (hK:K-B≠0) :
    (∫sigma in (beta-qStep*(j+1))..(beta-qStep*j),bandProfile K beta qStep B M j sigma)=
      bandMass K qStep B M j := by
  have he:(bandProfile K beta qStep B M j)=
      fun sigma=>(M*exp (-B*(qStep*(j+1))))*exp ((K-B)*(sigma-beta)):=by
    funext sigma
    unfold bandProfile
    rw [show exp (K*(sigma-beta))*M*exp (-B*(qStep*(j+1)))*exp (B*(beta-sigma))=
      (M*exp (-B*(qStep*(j+1))))*(exp (K*(sigma-beta))*exp (B*(beta-sigma))) by ring,
      ←exp_add]
    congr 1
    congr 1
    ring
  have hd:∀s:ℝ,HasDerivAt (fun t:ℝ=>exp ((K-B)*(t-beta))/(K-B))
      (exp ((K-B)*(s-beta))) s:=by
    intro s
    convert! (((hasDerivAt_id s).sub_const beta).const_mul (K-B)).exp.div_const (K-B) using 1
    all_goals simp only [id_eq,mul_one]
    all_goals field_simp [hK]
  have hc:Continuous (fun s:ℝ=>exp ((K-B)*(s-beta))):=by fun_prop
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s)
    (hc.intervalIntegrable (beta-qStep*(j+1)) (beta-qStep*j))
  rw [he,intervalIntegral.integral_const_mul,hi]
  unfold bandMass
  rw [show (K-B)*(beta-qStep*j-beta)=-(K-B)*(qStep*j) by ring,
    show (K-B)*(beta-qStep*(j+1)-beta)=-(K-B)*(qStep*(j+1)) by ring]
  ring

/-- Finite descending bands telescope with their correct orientation. -/
theorem reverse_adjacent_sum (f:ℝ→ℝ) (edge:ℕ→ℝ) (J:ℕ)
    (hi:∀j<J,IntervalIntegrable f volume (edge j) (edge (j+1))) :
    (∑j∈Finset.range J,∫s in edge (j+1)..edge j,f s)=∫s in edge J..edge 0,f s := by
  have he:(∑j∈Finset.range J,∫s in edge (j+1)..edge j,f s)=
      -(∑j∈Finset.range J,∫s in edge j..edge (j+1),f s):=by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact intervalIntegral.integral_symm ..
  rw [he,intervalIntegral.sum_integral_adjacent_intervals hi]
  exact (intervalIntegral.integral_symm ..).symm

/-- Warm finite q bands, arbitrary signed M, exact finite sigma integration,
actual height integration and Fubini. No positivity or desired old lower bound
is assumed. Every convergence condition follows from compact continuity. -/
theorem warm_row_sigma_first {F:ℝ→ℝ→ℝ} {K beta qStep v0 step:ℝ} {n J:ℕ}
    (B:ℕ→ℝ) (M:ℕ→ℕ→ℝ) (hq:0≤qStep) (hs:0≤step)
    (hK:∀k<n,K-B k≠0)
    (hF:ContinuousOn (fun p:ℝ×ℝ=>F p.1 p.2)
      (Icc (beta-qStep*J) beta×ˢ Icc v0 (v0+step*n)))
    (hLower:∀k<n,∀v∈Icc (v0+step*k) (v0+step*(k+1)),∀j<J,
      ∀sigma∈Icc (beta-qStep*(j+1)) (beta-qStep*j),
        bandProfile K beta qStep (B k) (M k j) j sigma≤F sigma v) :
    (∑k∈Finset.range n,600*step*(∑j∈Finset.range J,bandMass K qStep (B k) (M k j) j))≤
      600*(∫sigma in (beta-qStep*J)..beta,∫v in v0..(v0+step*n),F sigma v) := by
  let edge:ℕ→ℝ:=fun k=>v0+step*k
  let sedge:ℕ→ℝ:=fun j=>beta-qStep*j
  let G:ℝ→ℝ:=fun v=>∫sigma in (beta-qStep*J)..beta,F sigma v
  have hend:v0≤v0+step*n:=by nlinarith [mul_nonneg hs (Nat.cast_nonneg n)]
  have hab:beta-qStep*J≤beta:=by nlinarith [mul_nonneg hq (Nat.cast_nonneg J)]
  obtain ⟨hInner,hG⟩:=rectangle_integrability hab hend hF
  have hsec:∀v∈Icc v0 (v0+step*n),ContinuousOn (fun sigma=>F sigma v) (Icc (beta-qStep*J) beta):=by
    intro v hv
    exact hF.comp (continuousOn_id.prodMk continuousOn_const) (fun sigma hsig=>⟨hsig,hv⟩)
  have hband {v:ℝ} (hv:v∈Icc v0 (v0+step*n)) {j:ℕ} (hj:j<J) :
      IntervalIntegrable (fun sigma=>F sigma v) volume (sedge (j+1)) (sedge j):=by
    have hj':(j:ℝ)+1≤J:=by exact_mod_cast Nat.succ_le_of_lt hj
    have hl:beta-qStep*J≤sedge (j+1):=by
      dsimp [sedge]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hj' hq]
    have hr:sedge j≤beta:=by dsimp [sedge];nlinarith [mul_nonneg hq (Nat.cast_nonneg j)]
    apply ((hsec v hv).mono (Icc_subset_Icc hl hr)).intervalIntegrable_of_Icc
    dsimp [sedge]
    push_cast
    nlinarith
  have hOuter:∀k<n,IntervalIntegrable G volume (edge k) (edge (k+1)):=by
    intro k hk
    have hk':(k:ℝ)+1≤n:=by exact_mod_cast Nat.succ_le_of_lt hk
    have hl:v0≤edge k:=by dsimp [edge];nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
    have hr:edge (k+1)≤v0+step*n:=by dsimp [edge];push_cast;nlinarith [mul_le_mul_of_nonneg_left hk' hs]
    apply (hG.mono (Icc_subset_Icc hl hr)).intervalIntegrable_of_Icc
    dsimp [edge]
    push_cast
    nlinarith
  have hb:∀k∈Finset.range n,600*step*(∑j∈Finset.range J,bandMass K qStep (B k) (M k j) j)≤
      600*(∫v in edge k..edge (k+1),G v):=by
    intro k hk
    have hkn:k<n:=Finset.mem_range.mp hk
    have hed:edge k≤edge (k+1):=by dsimp [edge];push_cast;nlinarith
    have hsub:∀v∈Icc (edge k) (edge (k+1)),v∈Icc v0 (v0+step*n):=by
      intro v hv
      have hk':(k:ℝ)+1≤n:=by exact_mod_cast Nat.succ_le_of_lt hkn
      have hl:v0≤edge k:=by dsimp [edge];nlinarith [mul_nonneg hs (Nat.cast_nonneg k)]
      have hr:edge (k+1)≤v0+step*n:=by dsimp [edge];push_cast;nlinarith [mul_le_mul_of_nonneg_left hk' hs]
      exact ⟨hl.trans hv.1,hv.2.trans hr⟩
    have hvbound:∀v∈Icc (edge k) (edge (k+1)),
        (∑j∈Finset.range J,bandMass K qStep (B k) (M k j) j)≤G v:=by
      intro v hv
      have hcell:∀j∈Finset.range J,bandMass K qStep (B k) (M k j) j≤
          ∫sigma in sedge (j+1)..sedge j,F sigma v:=by
        intro j hj
        have hj':j<J:=Finset.mem_range.mp hj
        rw [←band_mass (beta:=beta) j (hK k hkn)]
        have hh:(∫sigma in sedge (j+1)..sedge j,bandProfile K beta qStep (B k) (M k j) j sigma)≤
            ∫sigma in sedge (j+1)..sedge j,F sigma v:=by
          apply intervalIntegral.integral_mono_on (by dsimp [sedge];push_cast;nlinarith)
            ((band_continuous K beta qStep (B k) (M k j) j).intervalIntegrable _ _)
            (hband (hsub v hv) hj')
          intro sigma hsig
          apply hLower k hkn v (by simpa only [edge,Nat.cast_add,Nat.cast_one] using hv) j hj'
          simpa only [sedge,Nat.cast_add,Nat.cast_one] using hsig
        simpa only [sedge,Nat.cast_add,Nat.cast_one] using hh
      have hh:=Finset.sum_le_sum hcell
      rw [reverse_adjacent_sum (fun sigma=>F sigma v) sedge J
        (fun j hj=>(hband (hsub v hv) hj).symm)] at hh
      simpa only [G,sedge,Nat.cast_zero,mul_zero,sub_zero] using hh
    have hr:=intervalIntegral.integral_mono_on hed
      (intervalIntegrable_const:IntervalIntegrable
        (fun _:ℝ=>∑j∈Finset.range J,bandMass K qStep (B k) (M k j) j) volume _ _)
      (hOuter k hkn) hvbound
    rw [intervalIntegral.integral_const] at hr
    have he:edge (k+1)-edge k=step:=by dsimp [edge];push_cast;ring
    simp only [he,smul_eq_mul] at hr
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hr (by norm_num:(0:ℝ)≤600)
  have hsum:=Finset.sum_le_sum hb
  have he:(∑k∈Finset.range n,600*(∫v in edge k..edge (k+1),G v))=
      600*(∫v in edge 0..edge n,G v):=by
    rw [←Finset.mul_sum,intervalIntegral.sum_integral_adjacent_intervals hOuter]
  rw [he] at hsum
  have hh:(∑k∈Finset.range n,600*step*(∑j∈Finset.range J,bandMass K qStep (B k) (M k j) j))≤
      600*(∫v in v0..(v0+step*n),∫sigma in (beta-qStep*J)..beta,F sigma v):=by
    simpa only [edge,G,Nat.cast_zero,mul_zero,add_zero] using hsum
  rw [rectangle_integral_swap hab hend hF] at hh
  exact hh
#print axioms band_mass
#print axioms warm_row_sigma_first
end WinnerOldOuter.Warm

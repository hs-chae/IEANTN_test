import RH080EstimatePack

set_option autoImplicit false
noncomputable section
open Filter Real IEANTN.CMSFunctional
open scoped Topology
namespace GrowingRank

def P (n : ℕ) : ℝ := primeAt n
def S (n : ℕ) : ℝ := sqrt (P n)
def H (n : ℕ) : ℝ := S n * log (P n)
def rankDensity (n j : ℕ) : ℝ := ((j-1 : ℕ) : ℝ) / S n
def gap (n j : ℕ) : ℝ := P (n+j)-P n

theorem P_gt_one (n : ℕ) : 1 < P n := by
  unfold P primeAt
  exact_mod_cast (Nat.prime_nth_prime n).one_lt

theorem P_strictMono : StrictMono P := by
  intro n m h
  unfold P primeAt
  exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime h

theorem P_atTop : Tendsto P atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
  · intro n
    unfold P primeAt
    exact_mod_cast (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
  · exact tendsto_natCast_atTop_atTop

theorem S_pos (n : ℕ) : 0 < S n :=
  sqrt_pos.2 (zero_lt_one.trans (P_gt_one n))

theorem H_pos (n : ℕ) : 0 < H n :=
  mul_pos (S_pos n) (log_pos (P_gt_one n))

theorem gap_pos {n j : ℕ} (hj : 1 ≤ j) : 0 < gap n j := by
  exact sub_pos.2 (P_strictMono (by omega))

theorem piReal_at_P (n : ℕ) : piReal (P n) = n+1 := by
  simp only [piReal, P, Nat.floor_natCast, primeAt, Nat.primeCounting, Nat.primeCounting',
    Nat.count_succ, Nat.prime_nth_prime, ite_true]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)

theorem piReal_le_iff {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    piReal y ≤ k ↔ y < P k := by
  change Nat.count Nat.Prime (⌊y⌋₊+1) ≤ k ↔ _
  rw [Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime]
  change ⌊y⌋₊ + 1 ≤ Nat.nth Nat.Prime k ↔ y < (Nat.nth Nat.Prime k : ℝ)
  rw [← Nat.lt_iff_add_one_le, Nat.floor_lt hy]

theorem P_le_iff {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    P k ≤ y ↔ k+1 ≤ piReal y := by
  rw [← not_lt, ← piReal_le_iff hy]
  omega

theorem piReal_mono : Monotone piReal :=
  Nat.monotone_primeCounting.comp Nat.floor_mono

theorem halfOpen_order {n j : ℕ} {y : ℝ} (hy : P n ≤ y) :
    P (n+j) ≤ y ↔ j ≤ piReal y - piReal (P n) := by
  have hy0 := (zero_lt_one.trans (P_gt_one n)).le.trans hy
  have hmono := piReal_mono hy
  rw [P_le_iff hy0, piReal_at_P] at *
  omega

def endpoint (y : ℝ) : ℕ := by
  classical
  exact if ∃ k : ℕ, P k = y then 1 else 0

theorem strict_order {n j : ℕ} {y : ℝ} (hy : P n ≤ y) (hj : 1 ≤ j) :
    P (n+j) < y ↔ j ≤ (piReal y - piReal (P n)) - endpoint y := by
  classical
  by_cases hp : ∃ k : ℕ, P k = y
  · obtain ⟨k,rfl⟩ := hp
    rw [endpoint, ite_eq_left ⟨k,rfl⟩, piReal_at_P, piReal_at_P, P_strictMono.lt_iff_lt]
    omega
  · rw [endpoint, ite_eq_right hp, Nat.sub_zero, ← halfOpen_order hy]
    exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (fun he => hp ⟨n+j,he⟩)⟩

theorem strict_of_extra_count {n j : ℕ} {y : ℝ} (hy : P n ≤ y)
    (h : j+1 ≤ piReal y-piReal (P n)) : P (n+j) < y :=
  (P_strictMono (show n+j < n+(j+1) by omega)).trans_le ((halfOpen_order hy).mpr h)

theorem from_good {b c : ℝ} (h : GoodCoefficient b c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rankDensity n j ≤ b → gap n j < c * H n := by
  obtain ⟨hc, δ,hδ,hpop⟩ := h
  have hsmall := ((tendsto_sqrt_atTop.comp P_atTop).eventually_ge_atTop (2/δ))
  filter_upwards [P_atTop.eventually hpop,hsmall] with n hn hs
  intro j hj hjb
  change 2/δ ≤ S n at hs
  have h2 := (div_le_iff₀ hδ).mp hs
  have hcnt := (le_div_iff₀ (S_pos n)).mp hn
  have hj' := (div_le_iff₀ (S_pos n)).mp hjb
  have hjcast : ((j+1 : ℕ) : ℝ) = ((j-1 : ℕ) : ℝ)+2 := by
    exact_mod_cast (show j+1 = j-1+2 by omega)
  have hR : ((j+1 : ℕ) : ℝ) ≤ (halfOpenCount c (P n) : ℝ) := by
    rw [hjcast]
    linarith [mul_add (S n) b δ, add_mul b δ (S n)]
  have hcnt' : j+1 ≤ halfOpenCount c (P n) := by exact_mod_cast hR
  have hy : P n ≤ P n + c * H n := le_add_of_nonneg_right (mul_pos hc (H_pos n)).le
  have hlt := strict_of_extra_count hy (j := j) (by
    simpa [halfOpenCount, H, S, mul_assoc] using hcnt')
  exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hlt)

theorem density_le_iff_floor {β : ℝ} (hβ : 0 ≤ β) (n j : ℕ) (hj : 1 ≤ j) :
    rankDensity n j ≤ β ↔ j ≤ ⌊β * S n⌋₊ + 1 := by
  unfold rankDensity
  rw [div_le_iff₀ (S_pos n), ← Nat.le_floor_iff (mul_nonneg hβ (S_pos n).le)]
  omega

theorem density_nonneg (n j : ℕ) : 0 ≤ rankDensity n j :=
  div_nonneg (Nat.cast_nonneg _) (S_pos n).le


/-- Finite upper mesh: only finitely many eventual statements are used. -/
theorem affine_transport {A B β ε : ℝ} (hB : 0 ≤ B) (_hβ : 0 ≤ β) (he : 0 < ε)
    (curve : ∀ b : ℝ, 0 ≤ b → ∀ η : ℝ, 0 < η → GoodCoefficient b (A+B*b+η)) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rankDensity n j ≤ β →
      gap n j < (A+B*rankDensity n j+ε) * H n := by
  let t := ε / (2*(B+1))
  have ht : 0 < t := div_pos he (by linarith)
  have hstep : B*t ≤ ε/2 := by
    have h := (div_mul_cancel₀ ε (show 2*(B+1) ≠ 0 by positivity))
    dsimp [t] at *
    nlinarith
  have hMesh : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range (⌈β/t⌉₊+1),
      ∀ j : ℕ, 1 ≤ j → rankDensity n j ≤ i*t →
        gap n j < (A+B*(i*t)+ε/2) * H n := by
    refine (eventually_all_finset _).mpr ?_
    intro i _
    exact from_good (curve (i*t) (mul_nonneg (Nat.cast_nonneg i) ht.le) _ (by linarith))
  filter_upwards [hMesh] with n hn
  intro j hj hjβ
  let a := rankDensity n j
  have ha : 0 ≤ a := density_nonneg n j
  let i := ⌈a/t⌉₊
  have hi : i ∈ Finset.range (⌈β/t⌉₊+1) := by
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.ceil_le.mpr
    exact (div_le_div_of_nonneg_right hjβ ht.le).trans (Nat.le_ceil _)
  have hab : a ≤ i*t := (div_le_iff₀ ht).mp (Nat.le_ceil _)
  have hb : (i : ℝ)*t ≤ a+t := by
    have h := (lt_div_iff₀ ht).mp
      (show (i:ℝ) < (a+t)/t by
        rw [add_div, div_self ht.ne']
        exact Nat.ceil_lt_add_one (div_nonneg ha ht.le))
    exact h.le
  have hcoeff : A+B*((i:ℝ)*t)+ε/2 ≤ A+B*a+ε := by
    have hmul := mul_le_mul_of_nonneg_left hb hB
    rw [mul_add] at hmul
    linarith
  exact (hn i hi j hj hab).trans_le (mul_le_mul_of_nonneg_right hcoeff (H_pos n).le)

theorem curve_from_exact {A B : ℝ}
    (curve : ∀ b : ℝ, 0 ≤ b → GoodCoefficient b (A+B*b)) :
    ∀ b : ℝ, 0 ≤ b → ∀ η : ℝ, 0 < η → GoodCoefficient b (A+B*b+η) := by
  intro b hb η hη
  exact RHOnePrime.CMSFunctional.goodCoefficient_mono (curve b hb) (by linarith)

def G (a : ℝ) : ℝ := (20582561296/24680948495 : ℝ)*(1+2*a)
abbrev Sparse := RHWeightedPopulation.v1.sparseLine
abbrev Flat := RHWeightedPopulation.v1.flatLine

theorem gaussian_rankwise (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rankDensity n j ≤ β →
      gap n j < (G (rankDensity n j)+ε) * H n := by
  have hG (a : ℝ) : G a = 20582561296/24680948495 + (2*(20582561296/24680948495))*a := by
    unfold G
    ring
  simp only [hG]
  apply affine_transport (by norm_num) hβ he
  intro b hb η hη
  have hg := RH080Exposure.Estimates.gaussian hCMS hRH b hb η hη
  change GoodCoefficient b (G b+η) at hg
  simpa only [hG] using hg

theorem common_curves (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β*S n⌋₊+1 →
      0 < gap n j ∧ gap n j <
        min (min (G (rankDensity n j)) (min (Sparse (rankDensity n j))
          (Flat (rankDensity n j)))+ε) (min (G β+ε) (min (Sparse β) (Flat β))) * H n := by
  have hg := gaussian_rankwise hCMS hRH hβ he
  have hs := affine_transport (by norm_num : (0:ℝ) ≤ 1163388/1000000) hβ he
    (curve_from_exact (RH080Exposure.Estimates.sparse hNorm hUniform hRH))
  have hf := affine_transport (by norm_num : (0:ℝ) ≤ 16/15) hβ he
    (curve_from_exact (RH080Exposure.Estimates.flat hNorm hUniform hRH))
  have hgβ := from_good (RH080Exposure.Estimates.gaussian hCMS hRH β hβ ε he)
  have hsβ := from_good (RH080Exposure.Estimates.sparse hNorm hUniform hRH β hβ)
  have hfβ := from_good (RH080Exposure.Estimates.flat hNorm hUniform hRH β hβ)
  filter_upwards [hg,hs,hf,hgβ,hsβ,hfβ] with n hgn hsn hfn hgβn hsβn hfβn
  intro j hj hfloor
  have hjβ := (density_le_iff_floor hβ n j hj).mpr hfloor
  refine ⟨gap_pos hj, ?_⟩
  simp only [← min_add_add_right, min_mul_of_nonneg _ _ (H_pos n).le, lt_min_iff]
  exact ⟨⟨hgn j hj hjβ,hsn j hj hjβ,hfn j hj hjβ⟩,hgβn j hj hjβ,hsβn j hj hjβ,hfβn j hj hjβ⟩


section RefinedBR
open RH080Next.Explicit RH080Next.PopulationCanonical AffineFourierPrograms.v1

def sparseD : ℝ := 1-4*(119725872611533800/(8*1000000000000000000))
def sparseN : ℝ := 887721072633027910/1000000000000000000
def sparseM : ℝ := 546871713113309800/1000000000000000000
def flatD : ℝ := 15*533333333333333333/(8*1000000000000000000)
def flatN : ℝ := 1120475208606944546/1000000000000000000
def flatM : ℝ := 533333333333333333/1000000000000000000

def SparseRef (a : ℝ) : ℝ := sparseN/sparseD+(2*sparseM/sparseD)*a
def FlatRef (a : ℝ) : ℝ := flatN/flatD+(2*flatM/flatD)*a

private theorem curve_of_bound (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) (nodes : List ℚ) (m : ℕ)
    (hm : 0 < m) (hlen : 2 ≤ nodes.length) (hlen5 : nodes.length ≤ 5*m+1)
    (hlast : node nodes (nodes.length-1) = 0)
    {M N D : ℝ} (hM : 0 < M) (hN : 0 ≤ N) (hD : 0 < D)
    (hdenom : brDenominatorFour nodes m = D)
    (hnorm : brAmplitudeMass nodes m ≤ N)
    (hbound : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (hattain : ∃ v : ℝ, |affineSpectrum nodes m v| = M)
    (a : ℝ) (ha : 0 ≤ a) (e : ℝ) (he : 0 < e) :
    GoodCoefficient a (N/D+(2*M/D)*a+e) := by
  apply source_BR_population_goodCoefficient hUniform nodes m hm hlen hlen5 hlast M hM
    hbound hattain (hdenom ▸ hD) _ a (by positivity) _ hRH
  rw [hdenom, lt_div_iff₀ (by positivity : 0 < 2*M)]
  have heD := mul_pos he hD
  have hEq : (N/D+(2*M/D)*a+e)*D = N+2*M*a+e*D := by
    field_simp
  rw [hEq]
  linarith

theorem sparse_refined_curve (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    (a : ℝ) (ha : 0 ≤ a) (e : ℝ) (he : 0 < e) : GoodCoefficient a (SparseRef a+e) := by
  rcases kernel_only_sparse_witness hNorm with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 = sparseD := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
    rfl
  apply curve_of_bound hUniform hRH sparseNodes 8 (by decide) (by decide) (by decide)
    (by norm_num [node,sparseNodes,sparseNumerators])
    (by norm_num [sparseM]) (by norm_num [sparseN]) (by norm_num [sparseD])
    hD hN hBound hAttain a ha e he

theorem flat_refined_curve (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    (a : ℝ) (ha : 0 ≤ a) (e : ℝ) (he : 0 < e) : GoodCoefficient a (FlatRef a+e) := by
  rcases kernel_only_flat_witness hNorm with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 = flatD := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]
    unfold flatD
    ring
  apply curve_of_bound hUniform hRH flatNodes 8 (by decide) (by decide) (by decide)
    (by norm_num [node,flatNodes,flatNumerators])
    (by norm_num [flatM]) (by norm_num [flatN]) (by norm_num [flatD])
    hD hN hBound hAttain a ha e he

theorem sparse_rounding {a : ℝ} (ha : 0 ≤ a) : SparseRef a + 1/2000000 ≤ Sparse a := by
  unfold SparseRef sparseN sparseM sparseD Sparse RHWeightedPopulation.v1.sparseLine
  linarith

theorem flat_rounding (a : ℝ) : FlatRef a + 1/250 ≤ Flat a := by
  unfold FlatRef flatN flatM flatD Flat RHWeightedPopulation.v1.flatLine
  linarith

theorem refined_curves (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (he : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β*S n⌋₊+1 →
      0 < gap n j ∧
      gap n j < min (G (rankDensity n j)+ε)
        (min (SparseRef (rankDensity n j) + min ε (1/2000000))
             (FlatRef (rankDensity n j) + min ε (1/250))) * H n := by
  have hg := gaussian_rankwise hCMS hRH hβ he
  have hs := affine_transport (by norm_num [sparseD,sparseM] : (0:ℝ) ≤ 2*sparseM/sparseD)
    hβ (lt_min he (by norm_num : (0:ℝ) < 1/2000000))
    (sparse_refined_curve hNorm hUniform hRH)
  have hf := affine_transport (by norm_num [flatD,flatM] : (0:ℝ) ≤ 2*flatM/flatD)
    hβ (lt_min he (by norm_num : (0:ℝ) < 1/250))
    (flat_refined_curve hNorm hUniform hRH)
  filter_upwards [hg,hs,hf] with n hgn hsn hfn
  intro j hj hjf
  have hjβ := (density_le_iff_floor hβ n j hj).mpr hjf
  simp only [min_mul_of_nonneg _ _ (H_pos n).le, lt_min_iff]
  exact ⟨gap_pos hj,hgn j hj hjβ,hsn j hj hjβ,hfn j hj hjβ⟩

theorem br_exact_rounded_rankwise (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β*S n⌋₊+1 →
      gap n j < min (Sparse (rankDensity n j)) (Flat (rankDensity n j)) * H n := by
  have hs := affine_transport (by norm_num [sparseD,sparseM] : (0:ℝ) ≤ 2*sparseM/sparseD)
    hβ (by norm_num : (0:ℝ) < 1/2000000) (sparse_refined_curve hNorm hUniform hRH)
  have hf := affine_transport (by norm_num [flatD,flatM] : (0:ℝ) ≤ 2*flatM/flatD)
    hβ (by norm_num : (0:ℝ) < 1/250) (flat_refined_curve hNorm hUniform hRH)
  filter_upwards [hs,hf] with n hsn hfn
  intro j hj hjf
  have hjβ := (density_le_iff_floor hβ n j hj).mpr hjf
  simp only [min_mul_of_nonneg _ _ (H_pos n).le, lt_min_iff]
  exact ⟨(hsn j hj hjβ).trans_le
      (mul_le_mul_of_nonneg_right (sparse_rounding (density_nonneg n j)) (H_pos n).le),
    (hfn j hj hjβ).trans_le (mul_le_mul_of_nonneg_right (flat_rounding _) (H_pos n).le)⟩

theorem refined_switches :
    (∀ a : ℝ, a ≤ 51187386629078138002907957/234124646216239748387333864 →
      min (G a) (min (SparseRef a) (FlatRef a)) = G a) ∧
    (∀ a : ℝ, 51187386629078138002907957/234124646216239748387333864 ≤ a →
      a ≤ 26508671988622117596716777934930407/14548889325776686924240277504722904 →
      min (G a) (min (SparseRef a) (FlatRef a)) = SparseRef a) ∧
    (∀ a : ℝ, 26508671988622117596716777934930407/14548889325776686924240277504722904 ≤ a →
      min (G a) (min (SparseRef a) (FlatRef a)) = FlatRef a) := by
  unfold G SparseRef FlatRef sparseN sparseD sparseM flatN flatD flatM
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact min_eq_left (le_min (by linarith) (by linarith))
  · intro a ha hb
    exact (congrArg (min _) (min_eq_left (by linarith))).trans (min_eq_right (by linarith))
  · intro a ha
    exact (congrArg (min _) (min_eq_right (by linarith))).trans (min_eq_right (by linarith))

end RefinedBR

-- Endpoint and zero-cutoff regression tests.
example (n j : ℕ) (hj : 1 ≤ j) :
    piReal (P (n+j))-piReal (P n) = j ∧
    ¬ j ≤ (piReal (P (n+j))-piReal (P n))-endpoint (P (n+j)) := by
  constructor
  · simp only [piReal_at_P]; omega
  · rw [← strict_order (P_strictMono.monotone (Nat.le_add_right n j)) hj]
    exact lt_irrefl _

example (n j : ℕ) (hj : 1 ≤ j) : rankDensity n j ≤ 0 ↔ j = 1 := by
  rw [density_le_iff_floor le_rfl n j hj]
  simp only [zero_mul, Nat.floor_zero, zero_add]
  omega

#print axioms GrowingRank.strict_order
#print axioms GrowingRank.common_curves
#print axioms GrowingRank.refined_curves
#print axioms GrowingRank.br_exact_rounded_rankwise
#print axioms GrowingRank.refined_switches
end GrowingRank

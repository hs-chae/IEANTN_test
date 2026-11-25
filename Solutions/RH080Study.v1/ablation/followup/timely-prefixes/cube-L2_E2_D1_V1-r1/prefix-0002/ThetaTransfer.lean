import Mathlib
import CompactDualVerified

noncomputable section
open Real Finset Filter Set
open scoped Topology

namespace CubeStudy

def primesLE (x : ℝ) : Finset ℕ := Nat.primesLE ⌊x⌋₊

def primesOpen (x y : ℝ) : Finset ℕ :=
  (primesLE y).filter fun p => x < (p : ℝ) ∧ (p : ℝ) < y

def theta (x : ℝ) : ℝ := ∑ p ∈ primesLE x, log (p : ℝ)

def thetaLeft (x : ℝ) : ℝ :=
  ∑ p ∈ (primesLE x).filter (fun p : ℕ => (p : ℝ) < x), log (p : ℝ)

def count (x y : ℝ) : ℝ := (primesOpen x y).card

def err (x : ℝ) : ℝ := sqrt x * (log x - 2) * log x / (8 * π)

-- A source proposition, NOT a new axiom.
def Schoenfeld : Prop :=
  RiemannHypothesis → ∀ x : ℝ, 2300000000 ≤ x → |theta x - x| < err x

def Buthe : Prop :=
  (∀ x : ℝ, 1423 ≤ x → x ≤ 10^19 → x - theta x ≤ (195/100 : ℝ) * sqrt x) ∧
  (∀ x : ℝ, 1 ≤ x → x ≤ 10^19 → (5/100 : ℝ) * sqrt x < x - theta x)

lemma mem_le {p : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    p ∈ primesLE y ↔ (p : ℝ) ≤ y ∧ p.Prime := by
  rw [primesLE, Nat.mem_primesLE, Nat.le_floor_iff hy]

lemma theta_eq_left_eventually {y : ℝ} (hy : 0 < y) :
    ∀ᶠ z in 𝓝[<] y, theta z = thetaLeft y := by
  classical
  have h : ∀ᶠ z in 𝓝 y, ∀ p ∈ primesLE y,
      (p : ℝ) < y → (p : ℝ) < z := by
    apply (Finset.eventually_all _).mpr
    intro p _
    by_cases hp : (p : ℝ) < y
    · filter_upwards [eventually_gt_nhds hp] with z hz
      exact fun _ => hz
    · exact Filter.Eventually.of_forall (fun _ a => (hp a).elim)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds,
    (eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz0 hzy
  have hzy' : z < y := hzy
  unfold theta thetaLeft
  congr 1
  ext p
  simp only [mem_filter]
  rw [mem_le hz0.le, mem_le hy.le]
  constructor
  · exact fun ⟨hp, hprime⟩ => ⟨⟨hp.trans hzy'.le, hprime⟩, hp.trans_lt hzy'⟩
  · intro ⟨⟨hpy, hprime⟩, hplt⟩
    exact ⟨(hz p ((mem_le hy.le).mpr ⟨hpy,hprime⟩) hplt).le, hprime⟩

lemma left_transfer {y : ℝ} {f : ℝ → ℝ} {a : ℝ}
    (hy : 0 < y) (hf : ContinuousAt f y) (ha : a < y)
    (h : ∀ z ∈ Ioo a y, f z ≤ theta z) : f y ≤ thetaLeft y := by
  haveI : NeBot (𝓝[<] y) := inferInstance
  refine le_of_tendsto_of_tendsto (hf.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio y)))
    tendsto_const_nhds ?_
  filter_upwards [theta_eq_left_eventually hy,
    (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z he haz hzy
  rw [← he]
  exact h z ⟨haz,hzy⟩

lemma transfer_count {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    thetaLeft y - theta x ≤ count x y * log y := by
  classical
  have hy := hx.trans hxy.le
  have hs : primesLE x ∪ primesOpen x y =
      (primesLE y).filter (fun p : ℕ => (p : ℝ) < y) := by
    ext p
    unfold primesOpen
    simp only [Finset.mem_union, mem_filter]
    rw [mem_le hx, mem_le hy]
    by_cases hp : (p : ℝ) ≤ x
    · have hpy := hp.trans_lt hxy
      simp [hp, hpy, hpy.le, not_lt_of_ge hp]
    · simp [hp, lt_of_not_ge hp]
  have hd : Disjoint (primesLE x) (primesOpen x y) := by
    apply Finset.disjoint_left.mpr
    intro p hp hpp
    exact (not_lt_of_ge ((mem_le hx).mp hp).1) (mem_filter.mp hpp).2.1
  have he : thetaLeft y = theta x + ∑ p ∈ primesOpen x y, log (p : ℝ) := by
    unfold thetaLeft theta
    rw [← hs, sum_union hd]
  rw [he, add_sub_cancel_left]
  calc
    _ ≤ ∑ _ ∈ primesOpen x y, log y := by
      apply sum_le_sum
      intro p hp
      have hpo := (mem_filter.mp hp).2
      exact log_le_log (hx.trans_lt hpo.1) hpo.2.le
    _ = _ := by simp [count]

lemma err_cont {y : ℝ} (hy : 0 < y) : ContinuousAt err y :=
  ((Real.continuous_sqrt.continuousAt.mul ((continuousAt_log hy.ne').sub continuousAt_const)).mul
    (continuousAt_log hy.ne')).div_const _

theorem schoenfeld_window (h : Schoenfeld) (rh : RiemannHypothesis)
    {x y : ℝ} (hx : 2300000000 ≤ x) (hxy : x < y) :
    y - x - err x - err y < count x y * log y := by
  have hx0 : 0 ≤ x := by linarith
  have hy := hx0.trans_lt hxy
  have hl := left_transfer hy (continuousAt_id.sub (err_cont hy)) hxy
    (fun z hz => by
      have he := ((abs_lt.mp (h rh z (hx.trans hz.1.le))).1)
      dsimp
      linarith)
  change y - err y ≤ thetaLeft y at hl
  have hu := (abs_lt.mp (h rh x hx)).2
  linarith [transfer_count hx0 hxy]

theorem buthe_window (h : Buthe) {x y : ℝ} (hx : 1423 ≤ x)
    (hxy : x < y) (hy : y ≤ 10^19) :
    y - x - (195/100 : ℝ) * sqrt y + (5/100 : ℝ) * sqrt x <
      count x y * log y := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 := hx0.trans_lt hxy
  have hl := left_transfer hy0 (continuousAt_id.sub (Real.continuous_sqrt.continuousAt.const_mul (195/100 : ℝ))) hxy
    (fun z hz => by
      have he := h.1 z (hx.trans hz.1.le) (hz.2.le.trans hy)
      dsimp
      linarith)
  change y - (195/100 : ℝ) * sqrt y ≤ thetaLeft y at hl
  have hu := h.2 x (by linarith) (hxy.le.trans hy)
  linarith [transfer_count hx0 hxy]

end CubeStudy
#print axioms CubeStudy.schoenfeld_window
#print axioms CubeStudy.buthe_window

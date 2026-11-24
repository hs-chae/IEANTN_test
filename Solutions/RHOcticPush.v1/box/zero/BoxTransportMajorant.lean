import BoxPositivePieces
import BoxZeroPairing
import BoxZeroKernel

/-! Actual full-family majorant assembly. The low range is a finite count and
the high range is the complete infinite quadratic tail, each already proved. -/
namespace RHOcticPush.BoxZero
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount RHOcticPush.BPTInfinite
set_option maxHeartbeats 0

noncomputable def transportMajorant (d t : ℝ) : ℝ :=
  |kernel d t| + if |t|≤32768 then d/48 else 1/t^2

lemma F_neg (t : ℝ) : F (-t)=F t := by rw [F_sinc,Real.sinc_neg,F_sinc]

lemma kernel_abs_neg (d t : ℝ) : |kernel d (-t)|=|kernel d t| := by
  simp only [kernel,mul_neg,F_neg,div_neg,abs_neg]

lemma transportMajorant_even (d t : ℝ) : transportMajorant d (-t)=transportMajorant d t := by
  simp only [transportMajorant,kernel_abs_neg,abs_neg,neg_sq]

lemma transportMajorant_nonneg {d : ℝ} (hd : 0≤d) (t : ℝ) :
    0≤transportMajorant d t := by
  unfold transportMajorant
  split_ifs <;> positivity

lemma transportMajorant_positive (d : ℝ) (z : PositiveZero 12) :
    transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ) =
      |kernel d z.val.im| * (IEANTN.zetaOrder z.val : ℝ) +
        (d/48)*countPiece 32768 z + tailPiece 32768 z := by
  have ht0 : 0<z.val.im := by have hh : (12:ℝ)<z.val.im := z.property.2.1;linarith
  unfold transportMajorant countPiece tailPiece
  rw [abs_of_pos ht0]
  by_cases ht : z.val.im≤32768
  · simp only [if_pos ht,if_neg (not_lt.mpr ht)]
    ring
  · simp only [if_neg ht,if_pos (lt_of_not_ge ht)]
    ring

theorem transportMajorant_summable (h : PublishedBound) {d : ℝ} (hd : 0<d) :
    Summable (fun z : PositiveZero 12 =>
      transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ)) := by
  have hk := (kernel_infinite_bound h hd).1
  have hc := ((countPiece_bound 32768).1).mul_left (d/48)
  have ht := (tailPiece_bound h (by norm_num : (12:ℝ)≤32768)).1
  exact ((hk.add hc).add ht).congr (fun z => (transportMajorant_positive d z).symm)

/-- The precise actual shift allowance, with both entire ranges verified. -/
theorem transportMajorant_bound (h : PublishedBound) {d : ℝ} (hd : 0<d) :
    2*(∑' z : PositiveZero 12,transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ)) ≤
      2*(∑' z : PositiveZero 12,|kernel d z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) +
        shiftAllowance d := by
  have hk := (kernel_infinite_bound h hd).1
  have hc := (countPiece_bound 32768).1
  have ht := (tailPiece_bound h (by norm_num : (12:ℝ)≤32768)).1
  have he : (∑' z : PositiveZero 12,transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ)) =
      (∑' z : PositiveZero 12,|kernel d z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) +
        (d/48)*(∑' z : PositiveZero 12,countPiece 32768 z) +
          ∑' z : PositiveZero 12,tailPiece 32768 z := by
    rw [tsum_congr (transportMajorant_positive d)]
    rw [(hk.add (hc.mul_left (d/48))).tsum_add ht,hk.tsum_add (hc.mul_left (d/48)),
      tsum_mul_left]
  rw [he]
  have hb := fixed_transport_bounds h
  have hl := mul_le_mul_of_nonneg_left hb.1 (by positivity : 0≤d/48)
  unfold shiftAllowance
  linarith [hb.2]

/-- A verified pointwise actual-packet bound is lifted to the full sum, with
summability proved before the norm comparison and no omitted zero ordinates. -/
theorem complete_transport_bound (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hB : PublishedBound)
    {d X : ℝ} (hd : 0<d) (hX : 0≤X) {p : PsiSmoothing.Zero → ℂ}
    (hp : ∀ z,‖p z‖≤X*transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ)) :
    Summable p ∧ ‖∑' z : PsiSmoothing.Zero,p z‖ ≤
      X*(2*(∑' z : PositiveZero 12,|kernel d z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) +
        shiftAllowance d) := by
  let g := fun t : ℝ => X*transportMajorant d t
  have hs : Summable (fun z : PositiveZero 12 => g z.val.im*(IEANTN.zetaOrder z.val : ℝ)) := by
    exact ((transportMajorant_summable hB hd).mul_left X).congr
      (fun z => by dsimp [g];ring)
  have he : ∀ t,g (-t)=g t := by intro t;dsimp [g];rw [transportMajorant_even]
  have hh := full_packet_bound rh hN hB he hs hp
  have ht : 2*(∑' z : PositiveZero 12,g z.val.im*(IEANTN.zetaOrder z.val : ℝ)) =
      X*(2*(∑' z : PositiveZero 12,transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ))) := by
    have he : (fun z : PositiveZero 12 => g z.val.im*(IEANTN.zetaOrder z.val : ℝ)) =
        (fun z : PositiveZero 12 => X*(transportMajorant d z.val.im*(IEANTN.zetaOrder z.val : ℝ))) := by
      ext z
      dsimp [g]
      ring
    rw [he,tsum_mul_left]
    ring
  rw [ht] at hh
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left (transportMajorant_bound hB hd) hX)⟩

#print axioms transportMajorant_bound
#print axioms complete_transport_bound
end RHOcticPush.BoxZero

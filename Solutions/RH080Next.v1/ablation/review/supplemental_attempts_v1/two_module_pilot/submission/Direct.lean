import RH080EstimatePack

noncomputable section
open Real Filter IEANTN.CMSFunctional
open RH080Next.Explicit AffineFourierPrograms.v1
set_option autoImplicit false

namespace RHWidthDirect

-- Same frozen bound, leakage, and maximum operands as in WeightedPopulationSolution.
def Ds : ℝ := 1-4*(119725872611533800/(8*1000000000000000000) : ℝ)
def Ns : ℝ := 887721072633027910/1000000000000000000
def Ms : ℝ := 546871713113309800/1000000000000000000
def Df : ℝ := (15*533333333333333333)/(8*1000000000000000000)
def Nf : ℝ := 1120475208606944546/1000000000000000000
def Mf : ℝ := 533333333333333333/1000000000000000000

def B_s (c : ℝ) : ℝ := (c*Ds-Ns)/(2*Ms)
def B_f (c : ℝ) : ℝ := (c*Df-Nf)/(2*Mf)

theorem sparse_of_lt (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {c a : ℝ} (hc : 0 < c) (ha : a < B_s c) :
    GoodCoefficient a c := by
  obtain ⟨_,hN,hJ,h0,hBound,hAttain⟩ :=
    RH080Next.PopulationCanonical.kernel_only_sparse_witness hNorm
  have hD : brDenominatorFour sparseNodes 8 = Ds := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
    rfl
  have hN' : brAmplitudeMass sparseNodes 8 ≤ Ns := hN
  apply source_BR_population_goodCoefficient hUniform sparseNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,sparseNodes,sparseNumerators])
    Ms (by norm_num [Ms]) hBound hAttain
    (by rw [hD]; norm_num [Ds]) c a hc _ hRH
  rw [hD]
  exact ha.trans_le (div_le_div_of_nonneg_right (sub_le_sub_left hN' _) (by norm_num [Ms]))

theorem flat_of_lt (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {c a : ℝ} (hc : 0 < c) (ha : a < B_f c) :
    GoodCoefficient a c := by
  obtain ⟨_,hN,hJ,h0,hBound,hAttain⟩ :=
    RH080Next.PopulationCanonical.kernel_only_flat_witness hNorm
  have hD : brDenominatorFour flatNodes 8 = Df := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]
    unfold Df
    ring
  have hN' : brAmplitudeMass flatNodes 8 ≤ Nf := hN
  apply source_BR_population_goodCoefficient hUniform flatNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,flatNodes,flatNumerators])
    Mf (by norm_num [Mf]) hBound hAttain
    (by rw [hD]; norm_num [Df]) c a hc _ hRH
  rw [hD]
  exact ha.trans_le (div_le_div_of_nonneg_right (sub_le_sub_left hN' _) (by norm_num [Mf]))

def L3 : ℝ := 193269011844967139/109374342622661960
def L5 : ℝ := 31036198331144443607/8533333333333333328

theorem exact_values :
    B_f 3 < B_s 3 ∧ B_s 5 < B_f 5 ∧
    B_s 3 = L3 ∧ B_f 5 = L5 ∧ 685251/387796 < L3 ∧ 465/128 < L5 := by
  norm_num [B_s,B_f,Ds,Ns,Ms,Df,Nf,Mf,L3,L5]

theorem three_below_direct (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {a : ℝ} (ha : a < L3) : GoodCoefficient a 3 :=
  sparse_of_lt hNorm hUniform hRH (by norm_num) (exact_values.2.2.1.symm ▸ ha)

theorem five_below_direct (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {a : ℝ} (ha : a < L5) : GoodCoefficient a 5 :=
  flat_of_lt hNorm hUniform hRH (by norm_num) (exact_values.2.2.2.1.symm ▸ ha)

-- Examples above the line-inversion targets, using the same width.
theorem three_example (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : GoodCoefficient (1767041/1000000) 3 :=
  three_below_direct hNorm hUniform hRH (by norm_num [L3])

theorem five_example (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : GoodCoefficient (3637/1000) 5 :=
  five_below_direct hNorm hUniform hRH (by norm_num [L5])

#print axioms three_below_direct
#print axioms five_below_direct
#print axioms three_example
#print axioms five_example
end RHWidthDirect

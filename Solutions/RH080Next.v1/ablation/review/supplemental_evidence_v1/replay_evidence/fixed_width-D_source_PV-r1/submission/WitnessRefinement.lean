import Transfer
import AffineProgramsSolution

set_option autoImplicit false
noncomputable section
open Filter Real IEANTN.CMSFunctional
open RH080Next.Explicit AffineFourierPrograms.v1
namespace Transfer

def Ds : ℝ := 1-4*(119725872611533800/(8*1000000000000000000) : ℝ)
def Df : ℝ := 15*533333333333333333/(8*1000000000000000000)
def Us : ℝ := 887721072633027910/1000000000000000000
def Uf : ℝ := 1120475208606944546/1000000000000000000
def Ms : ℝ := 546871713113309800/1000000000000000000
def Mf : ℝ := 533333333333333333/1000000000000000000
def Ls (c : ℝ) : ℝ := (c*Ds-Us)/(2*Ms)
def Lf (c : ℝ) : ℝ := (c*Df-Uf)/(2*Mf)

theorem sparse_cap (hu : BRPop) (rh : RiemannHypothesis)
    (hw : sparse_witness) {c a : ℝ} (hc : 0 < c) (ha : a < Ls c) :
    GoodCoefficient a c := by
  rcases hw with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 = Ds := by
    change sparseAmplitude 0 - 4 * positiveLeak sparseWindow = Ds
    rw [h0,hJ]
    rfl
  have hN' : brAmplitudeMass sparseNodes 8 ≤ Us := hN
  apply source_BR_population_goodCoefficient hu sparseNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,sparseNodes,sparseNumerators])
    Ms (by norm_num [Ms]) hBound hAttain
    (by rw [hD]; norm_num [Ds]) c a hc _ rh
  rw [hD]
  exact lt_of_lt_of_le ha (div_le_div_of_nonneg_right (sub_le_sub_left hN' _) (show 0 ≤ 2*Ms by norm_num [Ms]))

theorem flat_cap (hu : BRPop) (rh : RiemannHypothesis)
    (hw : flat_witness) {c a : ℝ} (hc : 0 < c) (ha : a < Lf c) :
    GoodCoefficient a c := by
  rcases hw with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 = Df := by
    change flatAmplitude 0 - 4 * positiveLeak flatWindow = Df
    rw [h0,hJ]
    norm_num [Df]
  have hN' : brAmplitudeMass flatNodes 8 ≤ Uf := hN
  apply source_BR_population_goodCoefficient hu flatNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,flatNodes,flatNumerators])
    Mf (by norm_num [Mf]) hBound hAttain
    (by rw [hD]; norm_num [Df]) c a hc _ rh
  rw [hD]
  exact lt_of_lt_of_le ha (div_le_div_of_nonneg_right (sub_le_sub_left hN' _) (show 0 ≤ 2*Mf by norm_num [Mf]))

def R3 : ℝ := 193269011844967139/109374342622661960
def R5 : ℝ := 31036198331144443607/8533333333333333328
theorem caps_at_widths :
    Ls 3 = R3 ∧ Lf 5 = R5 ∧
    Lf 3 < R3 ∧ Ls 5 < R5 ∧ t3 < R3 ∧ t5 < R5 := by
  norm_num [Ls,Lf,Ds,Df,Us,Uf,Ms,Mf,R3,R5,t3,t5]

theorem width3_refined (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < R3) : GoodCoefficient a 3 :=
  sparse_cap hu rh (challenge_sparse_witness hn) (by norm_num) (caps_at_widths.1.symm ▸ ha)

theorem width5_refined (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < R5) : GoodCoefficient a 5 :=
  flat_cap hu rh (challenge_flat_witness hn) (by norm_num) (caps_at_widths.2.1.symm ▸ ha)

theorem width3_refined_counts (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < R3) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop,
      (a+d)*sqrt x ≤ (halfOpenCount 3 x : ℝ) ∧
      (a+d)*sqrt x ≤ ((openSet 3 x).card : ℝ) :=
  both_counts_of_good (width3_refined hn hu rh ha)
theorem width5_refined_counts (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < R5) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop,
      (a+d)*sqrt x ≤ (halfOpenCount 5 x : ℝ) ∧
      (a+d)*sqrt x ≤ ((openSet 5 x).card : ℝ) :=
  both_counts_of_good (width5_refined hn hu rh ha)

theorem refined_leading_gains :
    R3 - oldCount 3 = 1726734183826542841/164061513933992940000 ∧
    R5 - oldCount 5 = 9864964558708324124141/95999999999999999940000 := by
  norm_num [R3,R5,oldCount]

#print axioms width3_refined_counts
#print axioms width5_refined_counts
#print axioms refined_leading_gains
end Transfer

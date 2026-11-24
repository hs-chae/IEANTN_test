import SpectralNetwork

example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (integratedperron_v1_formula : IntegratedPerron.v1.formula)
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound) :
    RHPrimeCounting.v5.compensation_profile :=
  @RHPrimeCounting.v5.challenge_compensation_profile rh_v1_hypothesis integratedperron_v1_formula nicolas_v1_spectral_bound

#print axioms RHPrimeCounting.v5.challenge_compensation_profile
example
    (rhprimecounting_v5_compensation_profile : RHPrimeCounting.v5.compensation_profile) :
    RHPrimeCounting.v5.compensation_076 :=
  @RHPrimeCounting.v5.challenge_compensation_076 rhprimecounting_v5_compensation_profile

#print axioms RHPrimeCounting.v5.challenge_compensation_076
example
    (rhprimecounting_v5_compensation_profile : RHPrimeCounting.v5.compensation_profile) :
    RHPrimeCounting.v5.compensation_055 :=
  @RHPrimeCounting.v5.challenge_compensation_055 rhprimecounting_v5_compensation_profile

#print axioms RHPrimeCounting.v5.challenge_compensation_055
example
    (rhprimecounting_v5_compensation_profile : RHPrimeCounting.v5.compensation_profile) :
    RHPrimeCounting.v5.ordinary_transfer :=
  @RHPrimeCounting.v5.challenge_ordinary_transfer rhprimecounting_v5_compensation_profile

#print axioms RHPrimeCounting.v5.challenge_ordinary_transfer
example
    (rhprimecounting_v5_ordinary_transfer : RHPrimeCounting.v5.ordinary_transfer)
    (rhsmoothing_v3_box_psi : RHSmoothing.v3.box_psi)
    (rhprimecounting_v5_effective_min : RHPrimeCounting.v5.effective_min) :
    RHPrimeCounting.v5.box_Li :=
  @RHPrimeCounting.v5.challenge_box_Li rhprimecounting_v5_ordinary_transfer rhsmoothing_v3_box_psi rhprimecounting_v5_effective_min

#print axioms RHPrimeCounting.v5.challenge_box_Li
example
    (rhprimecounting_v5_box_li : RHPrimeCounting.v5.box_Li) :
    RHPrimeCounting.v5.box_interval :=
  @RHPrimeCounting.v5.challenge_box_interval rhprimecounting_v5_box_li

#print axioms RHPrimeCounting.v5.challenge_box_interval
example : RHPrimeCounting.v5.whole_gain :=
  @RHPrimeCounting.v5.challenge_whole_gain

#print axioms RHPrimeCounting.v5.challenge_whole_gain
example
    (rhprimecounting_v5_whole_gain : RHPrimeCounting.v5.whole_gain) :
    RHPrimeCounting.v5.effective_min :=
  @RHPrimeCounting.v5.challenge_effective_min rhprimecounting_v5_whole_gain

#print axioms RHPrimeCounting.v5.challenge_effective_min
example
    (rhprimecounting_v5_ordinary_transfer : RHPrimeCounting.v5.ordinary_transfer)
    (rhsmoothing_v1_recovered_ch_psi : RHSmoothing.v1.recovered_ch_psi)
    (rhprimecounting_v5_effective_min : RHPrimeCounting.v5.effective_min) :
    RHPrimeCounting.v5.ch_Li :=
  @RHPrimeCounting.v5.challenge_ch_Li rhprimecounting_v5_ordinary_transfer rhsmoothing_v1_recovered_ch_psi rhprimecounting_v5_effective_min

#print axioms RHPrimeCounting.v5.challenge_ch_Li
example
    (rhprimecounting_v5_ch_li : RHPrimeCounting.v5.ch_Li) :
    RHPrimeCounting.v5.ch_interval :=
  @RHPrimeCounting.v5.challenge_ch_interval rhprimecounting_v5_ch_li

#print axioms RHPrimeCounting.v5.challenge_ch_interval

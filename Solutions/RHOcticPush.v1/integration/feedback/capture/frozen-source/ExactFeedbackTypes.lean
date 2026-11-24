import FeedbackNetwork

example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (integratedperron_v1_formula : IntegratedPerron.v1.formula)
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    RHPrimeCounting.v6.J_upper :=
  @RHPrimeCounting.v6.challenge_J_upper rh_v1_hypothesis integratedperron_v1_formula nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms RHPrimeCounting.v6.challenge_J_upper
example
    (rhprimecounting_v6_j_upper : RHPrimeCounting.v6.J_upper) :
    RHPrimeCounting.v6.prime_power_feedback :=
  @RHPrimeCounting.v6.challenge_prime_power_feedback rhprimecounting_v6_j_upper

#print axioms RHPrimeCounting.v6.challenge_prime_power_feedback
example
    (rhprimecounting_v5_compensation_profile : RHPrimeCounting.v5.compensation_profile)
    (rhprimecounting_v6_prime_power_feedback : RHPrimeCounting.v6.prime_power_feedback) :
    RHPrimeCounting.v6.ordinary_transfer :=
  @RHPrimeCounting.v6.challenge_ordinary_transfer rhprimecounting_v5_compensation_profile rhprimecounting_v6_prime_power_feedback

#print axioms RHPrimeCounting.v6.challenge_ordinary_transfer
example
    (rhprimecounting_v6_ordinary_transfer : RHPrimeCounting.v6.ordinary_transfer)
    (rhsmoothing_v3_box_psi : RHSmoothing.v3.box_psi) :
    RHPrimeCounting.v6.box_Li :=
  @RHPrimeCounting.v6.challenge_box_Li rhprimecounting_v6_ordinary_transfer rhsmoothing_v3_box_psi

#print axioms RHPrimeCounting.v6.challenge_box_Li
example
    (rhprimecounting_v6_box_li : RHPrimeCounting.v6.box_Li) :
    RHPrimeCounting.v6.box_interval :=
  @RHPrimeCounting.v6.challenge_box_interval rhprimecounting_v6_box_li

#print axioms RHPrimeCounting.v6.challenge_box_interval
example
    (rhprimecounting_v5_effective_min : RHPrimeCounting.v5.effective_min) :
    RHPrimeCounting.v6.preserves_v5 :=
  @RHPrimeCounting.v6.challenge_preserves_v5 rhprimecounting_v5_effective_min

#print axioms RHPrimeCounting.v6.challenge_preserves_v5
example : RHPrimeCounting.v6.below70 :=
  @RHPrimeCounting.v6.challenge_below70

#print axioms RHPrimeCounting.v6.challenge_below70
example : RHPrimeCounting.v6.full_min :=
  @RHPrimeCounting.v6.challenge_full_min

#print axioms RHPrimeCounting.v6.challenge_full_min
example : RHPrimeCounting.v6.whole_gain :=
  @RHPrimeCounting.v6.challenge_whole_gain

#print axioms RHPrimeCounting.v6.challenge_whole_gain
example
    (rhprimecounting_v6_box_li : RHPrimeCounting.v6.box_Li) :
    RHPrimeCounting.v6.clean_pi :=
  @RHPrimeCounting.v6.challenge_clean_pi rhprimecounting_v6_box_li

#print axioms RHPrimeCounting.v6.challenge_clean_pi
example : RHPrimeCounting.v6.clean_gain :=
  @RHPrimeCounting.v6.challenge_clean_gain

#print axioms RHPrimeCounting.v6.challenge_clean_gain

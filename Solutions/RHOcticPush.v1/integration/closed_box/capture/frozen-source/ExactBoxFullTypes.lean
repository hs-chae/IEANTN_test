import BoxFullNetwork

example : BoxMellinInputs.v2.first_moment :=
  @BoxMellinInputs.v2.challenge_first_moment

#print axioms BoxMellinInputs.v2.challenge_first_moment
example : BoxMellinInputs.v2.second_moment_identity :=
  @BoxMellinInputs.v2.challenge_second_moment_identity

#print axioms BoxMellinInputs.v2.challenge_second_moment_identity
example : BoxMellinInputs.v2.stieltjes_trapezoid :=
  @BoxMellinInputs.v2.challenge_stieltjes_trapezoid

#print axioms BoxMellinInputs.v2.challenge_stieltjes_trapezoid
example
    (integratedperron_v1_formula : IntegratedPerron.v1.formula) :
    RHSmoothingInputs.v2.box_explicit_formula :=
  @RHSmoothingInputs.v2.challenge_box_explicit_formula integratedperron_v1_formula

#print axioms RHSmoothingInputs.v2.challenge_box_explicit_formula
example
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    RHSmoothingInputs.v2.box_zero_estimate :=
  @RHSmoothingInputs.v2.challenge_box_zero_estimate nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms RHSmoothingInputs.v2.challenge_box_zero_estimate
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (rhsmoothinginputs_v2_box_explicit_formula : RHSmoothingInputs.v2.box_explicit_formula)
    (rhsmoothinginputs_v2_box_zero_estimate : RHSmoothingInputs.v2.box_zero_estimate)
    (boxmellininputs_v2_first_moment : BoxMellinInputs.v2.first_moment)
    (boxmellininputs_v2_second_moment_identity : BoxMellinInputs.v2.second_moment_identity) :
    RHSmoothing.v3.box_psi :=
  @RHSmoothing.v3.challenge_box_psi rh_v1_hypothesis rhsmoothinginputs_v2_box_explicit_formula rhsmoothinginputs_v2_box_zero_estimate boxmellininputs_v2_first_moment boxmellininputs_v2_second_moment_identity

#print axioms RHSmoothing.v3.challenge_box_psi
example : RHSmoothing.v3.box_gain :=
  @RHSmoothing.v3.challenge_box_gain

#print axioms RHSmoothing.v3.challenge_box_gain
example
    (rhsmoothing_v3_box_psi : RHSmoothing.v3.box_psi) :
    Lcm.v6.box_growth :=
  @Lcm.v6.challenge_box_growth rhsmoothing_v3_box_psi

#print axioms Lcm.v6.challenge_box_growth
example
    (rhprimecounting_v3_refined_transfer : RHPrimeCounting.v3.refined_transfer)
    (rhsmoothing_v3_box_psi : RHSmoothing.v3.box_psi) :
    RHPrimeCounting.v4.box_Li :=
  @RHPrimeCounting.v4.challenge_box_Li rhprimecounting_v3_refined_transfer rhsmoothing_v3_box_psi

#print axioms RHPrimeCounting.v4.challenge_box_Li
example
    (rhprimecounting_v4_box_li : RHPrimeCounting.v4.box_Li) :
    RHPrimeCounting.v4.box_interval :=
  @RHPrimeCounting.v4.challenge_box_interval rhprimecounting_v4_box_li

#print axioms RHPrimeCounting.v4.challenge_box_interval
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (buthe2016_v1_theorem_2_psi : Buthe2016.v1.theorem_2_psi)
    (rhsmoothing_v3_box_psi : RHSmoothing.v3.box_psi) :
    Primorial.v4.box_growth :=
  @Primorial.v4.challenge_box_growth rh_v1_hypothesis buthe2016_v1_theorem_2_psi rhsmoothing_v3_box_psi

#print axioms Primorial.v4.challenge_box_growth

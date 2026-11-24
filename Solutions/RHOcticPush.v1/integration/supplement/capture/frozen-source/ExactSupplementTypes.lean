import OcticVerifiedEvolution

example
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    PrimeKernelInputs.v4.octic_215_zero_estimate :=
  @PrimeKernelInputs.v4.challenge_octic_215_zero_estimate nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms PrimeKernelInputs.v4.challenge_octic_215_zero_estimate
example
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    PrimeKernelInputs.v4.octic_family_zero_estimate :=
  @PrimeKernelInputs.v4.challenge_octic_family_zero_estimate nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms PrimeKernelInputs.v4.challenge_octic_family_zero_estimate
example
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    PrimeKernelInputs.v4.optimized_215_zero_estimate :=
  @PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate
example
    (nicolas_v1_spectral_bound : Nicolas.v1.spectral_bound)
    (bptoffordinate_v1_bound : BPTOffOrdinate.v1.bound) :
    PrimeKernelInputs.v4.optimized_family_zero_estimate :=
  @PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate nicolas_v1_spectral_bound bptoffordinate_v1_bound

#print axioms PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_215_explicit_formula : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (primekernelinputs_v4_octic_215_zero_estimate : PrimeKernelInputs.v4.octic_215_zero_estimate) :
    PrimeInterval.v4.count_215 :=
  @PrimeInterval.v4.challenge_count_215 rh_v1_hypothesis primekernelinputs_v3_octic_215_explicit_formula primekernelinputs_v4_octic_215_zero_estimate

#print axioms PrimeInterval.v4.challenge_count_215
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_family_explicit_formula : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (primekernelinputs_v4_octic_family_zero_estimate : PrimeKernelInputs.v4.octic_family_zero_estimate) :
    PrimeInterval.v4.count_family :=
  @PrimeInterval.v4.challenge_count_family rh_v1_hypothesis primekernelinputs_v3_octic_family_explicit_formula primekernelinputs_v4_octic_family_zero_estimate

#print axioms PrimeInterval.v4.challenge_count_family
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_215_explicit_formula : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (primekernelinputs_v4_optimized_215_zero_estimate : PrimeKernelInputs.v4.optimized_215_zero_estimate) :
    PrimeInterval.v4.optimized_strict_215 :=
  @PrimeInterval.v4.challenge_optimized_strict_215 rh_v1_hypothesis primekernelinputs_v3_octic_215_explicit_formula primekernelinputs_v4_optimized_215_zero_estimate

#print axioms PrimeInterval.v4.challenge_optimized_strict_215
example
    (rh_v1_hypothesis : RH.v1.hypothesis)
    (primekernelinputs_v3_octic_family_explicit_formula : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (primekernelinputs_v4_optimized_family_zero_estimate : PrimeKernelInputs.v4.optimized_family_zero_estimate) :
    PrimeInterval.v4.optimized_strict_family :=
  @PrimeInterval.v4.challenge_optimized_strict_family rh_v1_hypothesis primekernelinputs_v3_octic_family_explicit_formula primekernelinputs_v4_optimized_family_zero_estimate

#print axioms PrimeInterval.v4.challenge_optimized_strict_family
example
    (primeinterval_v4_optimized_strict_215 : PrimeInterval.v4.optimized_strict_215) :
    PrimeInterval.v4.optimized_count_215 :=
  @PrimeInterval.v4.challenge_optimized_count_215 primeinterval_v4_optimized_strict_215

#print axioms PrimeInterval.v4.challenge_optimized_count_215
example
    (primeinterval_v4_optimized_strict_family : PrimeInterval.v4.optimized_strict_family) :
    PrimeInterval.v4.strict_214891875 :=
  @PrimeInterval.v4.challenge_strict_214891875 primeinterval_v4_optimized_strict_family

#print axioms PrimeInterval.v4.challenge_strict_214891875
example
    (primeinterval_v4_optimized_strict_family : PrimeInterval.v4.optimized_strict_family) :
    PrimeInterval.v4.strict_2149_uniform :=
  @PrimeInterval.v4.challenge_strict_2149_uniform primeinterval_v4_optimized_strict_family

#print axioms PrimeInterval.v4.challenge_strict_2149_uniform
example
    (primeinterval_v4_optimized_strict_family : PrimeInterval.v4.optimized_strict_family) :
    PrimeInterval.v4.optimized_count_family :=
  @PrimeInterval.v4.challenge_optimized_count_family primeinterval_v4_optimized_strict_family

#print axioms PrimeInterval.v4.challenge_optimized_count_family
example
    (primeinterval_v4_count_215 : PrimeInterval.v4.count_215) :
    PrimeQuantile.v3.octic_block :=
  @PrimeQuantile.v3.challenge_octic_block primeinterval_v4_count_215

#print axioms PrimeQuantile.v3.challenge_octic_block
example
    (primeinterval_v4_count_215 : PrimeInterval.v4.count_215) :
    PrimeQuantile.v3.successive_cubes :=
  @PrimeQuantile.v3.challenge_successive_cubes primeinterval_v4_count_215

#print axioms PrimeQuantile.v3.challenge_successive_cubes
example
    (primeinterval_v4_optimized_count_215 : PrimeInterval.v4.optimized_count_215) :
    PrimeQuantile.v3.optimized_octic_block :=
  @PrimeQuantile.v3.challenge_optimized_octic_block primeinterval_v4_optimized_count_215

#print axioms PrimeQuantile.v3.challenge_optimized_octic_block
example
    (primeinterval_v4_strict_214891875 : PrimeInterval.v4.strict_214891875) :
    Goldbach.v2.octic_sorted_count :=
  @Goldbach.v2.challenge_octic_sorted_count primeinterval_v4_strict_214891875

#print axioms Goldbach.v2.challenge_octic_sorted_count
example
    (primeinterval_v4_optimized_strict_215 : PrimeInterval.v4.optimized_strict_215) :
    Goldbach.v2.octic_fixed_sorted_count :=
  @Goldbach.v2.challenge_octic_fixed_sorted_count primeinterval_v4_optimized_strict_215

#print axioms Goldbach.v2.challenge_octic_fixed_sorted_count
example
    (primeinterval_v4_optimized_strict_family : PrimeInterval.v4.optimized_strict_family) :
    Goldbach.v2.octic_sorted_family :=
  @Goldbach.v2.challenge_octic_sorted_family primeinterval_v4_optimized_strict_family

#print axioms Goldbach.v2.challenge_octic_sorted_family

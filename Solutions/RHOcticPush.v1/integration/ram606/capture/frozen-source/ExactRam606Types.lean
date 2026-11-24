import Ram606Network

example
    (rhprimecounting_v5_compensation_profile : RHPrimeCounting.v5.compensation_profile)
    (buthe_v1_table_1_interval_bounds : Buthe.v1.table_1_interval_bounds)
    (buthe_v1_theorem_2_li_minus_pi : Buthe.v1.theorem_2_li_minus_pi)
    (buthe_v1_theorem_2_li_gt_pi : Buthe.v1.theorem_2_li_gt_pi) :
    RamanujanGap.v6.local_606b :=
  @RamanujanGap.v6.challenge_local_606b rhprimecounting_v5_compensation_profile buthe_v1_table_1_interval_bounds buthe_v1_theorem_2_li_minus_pi buthe_v1_theorem_2_li_gt_pi

#print axioms RamanujanGap.v6.challenge_local_606b
example
    (ramanujangap_v6_local_606b : RamanujanGap.v6.local_606b)
    (ramanujangap_v5_full_profile : RamanujanGap.v5.full_profile) :
    RamanujanGap.v6.full_profile :=
  @RamanujanGap.v6.challenge_full_profile ramanujangap_v6_local_606b ramanujangap_v5_full_profile

#print axioms RamanujanGap.v6.challenge_full_profile
example
    (ramanujangap_v6_full_profile : RamanujanGap.v6.full_profile) :
    RamanujanGap.v6.margin_606b :=
  @RamanujanGap.v6.challenge_margin_606b ramanujangap_v6_full_profile

#print axioms RamanujanGap.v6.challenge_margin_606b
example
    (ramanujangap_v6_margin_606b : RamanujanGap.v6.margin_606b) :
    RamanujanGap.v6.ramanujan :=
  @RamanujanGap.v6.challenge_ramanujan ramanujangap_v6_margin_606b

#print axioms RamanujanGap.v6.challenge_ramanujan
example : RamanujanGap.v6.retains_v5_profile :=
  @RamanujanGap.v6.challenge_retains_v5_profile

#print axioms RamanujanGap.v6.challenge_retains_v5_profile
example
    (ramanujangap_v6_retains_v5_profile : RamanujanGap.v6.retains_v5_profile)
    (ramanujangap_v5_retains_original_margin : RamanujanGap.v5.retains_original_margin) :
    RamanujanGap.v6.retains_original_margin :=
  @RamanujanGap.v6.challenge_retains_original_margin ramanujangap_v6_retains_v5_profile ramanujangap_v5_retains_original_margin

#print axioms RamanujanGap.v6.challenge_retains_original_margin
example : RamanujanGap.v6.profile_gain :=
  @RamanujanGap.v6.challenge_profile_gain

#print axioms RamanujanGap.v6.challenge_profile_gain

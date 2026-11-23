import SlabMonotonic
import LeafMargins
namespace Ramanujan640
open Real Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def c0 : ℝ := (343973689997/1000000000000:ℝ)
noncomputable def d0 : ℝ := (938886602791/500000000000:ℝ)
theorem proof_representation_0 : 0 ≤ c0 ∧ c0 ≤ (2176739058723318217125781788777683737890683340751445949058039/6328213819890606000000000000000000000000000000000000000000000:ℝ) ∧ (2176739058723318217125781788777683737890683340751445949058039/6328213819890606000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c0 ∧ 0 ≤ d0 ∧ (757236614448608878177550430964844202550763945393160121839853/403263084273360200000000000000000000000000000000000000000000:ℝ) ≤ d0 ∧ d0 ≤ (757236614448608878177550430964844202550763945393160121839853/403263084273360200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c0,d0]
theorem proof_0_c_number : c0 ≤ p3 ((1743/64:ℝ)/2)-q ((6957/256:ℝ)/2)*exp (-(6957/256:ℝ)/4)+(-37/50:ℝ) := by
  unfold c0 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_0_c_number
theorem proof_0_d_number : ppUpper ((6957/256:ℝ)-1)+(19/25:ℝ) ≤ d0 := by
  unfold ppUpper ppExpSum p3 d0
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_0_d_number
theorem proof_0_margin : (1/25:ℝ) ≤ endpointMargin (6957/256:ℝ) (1743/64:ℝ) c0 d0 := by
  unfold endpointMargin c0 d0
  interval_decide 80 (trust := kernel)
#print axioms proof_0_margin

noncomputable def c1 : ℝ := (17157143579/50000000000:ℝ)
noncomputable def d1 : ℝ := (1877221083621/1000000000000:ℝ)
theorem proof_representation_1 : 0 ≤ c1 ∧ c1 ≤ (3496321438776421677463494856671441996658012898302114353199/10189112840012400000000000000000000000000000000000000000000:ℝ) ∧ (3496321438776421677463494856671441996658012898302114353199/10189112840012400000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c1 ∧ 0 ≤ d1 ∧ (2983652246703512014283177126372176325038732738036455370873/1589398431936200000000000000000000000000000000000000000000:ℝ) ≤ d1 ∧ d1 ≤ (2983652246703512014283177126372176325038732738036455370873/1589398431936200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c1,d1]
theorem proof_1_c_number : c1 ≤ p3 ((879/32:ℝ)/2)-q ((1743/64:ℝ)/2)*exp (-(1743/64:ℝ)/4)+(-37/50:ℝ) := by
  unfold c1 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_1_c_number
theorem proof_1_d_number : ppUpper ((1743/64:ℝ)-1)+(19/25:ℝ) ≤ d1 := by
  unfold ppUpper ppExpSum p3 d1
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_1_d_number
theorem proof_1_margin : (1/25:ℝ) ≤ endpointMargin (1743/64:ℝ) (879/32:ℝ) c1 d1 := by
  unfold endpointMargin c1 d1
  interval_decide 80 (trust := kernel)
#print axioms proof_1_margin

noncomputable def c2 : ℝ := (85610377959/250000000000:ℝ)
noncomputable def d2 : ℝ := (1975065771563/1000000000000:ℝ)
theorem proof_representation_2 : 0 ≤ c2 ∧ c2 ≤ (54616843677409006012214446206192782500741722995797147976743/159492473282511000000000000000000000000000000000000000000000:ℝ) ∧ (54616843677409006012214446206192782500741722995797147976743/159492473282511000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c2 ∧ 0 ≤ d2 ∧ (25412957643825286629528233820075014698479410827440489417/12866891832025000000000000000000000000000000000000000000:ℝ) ≤ d2 ∧ d2 ≤ (25412957643825286629528233820075014698479410827440489417/12866891832025000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c2,d2]
theorem proof_2_c_number : c2 ≤ p3 ((1773/64:ℝ)/2)-q ((879/32:ℝ)/2)*exp (-(879/32:ℝ)/4)+(-37/50:ℝ) := by
  unfold c2 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_2_c_number
theorem proof_2_d_number : ppUpper ((879/32:ℝ)-1)+(43/50:ℝ) ≤ d2 := by
  unfold ppUpper ppExpSum p3 d2
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_2_d_number
theorem proof_2_margin : (1/25:ℝ) ≤ endpointMargin (879/32:ℝ) (1773/64:ℝ) c2 d2 := by
  unfold endpointMargin c2 d2
  interval_decide 80 (trust := kernel)
#print axioms proof_2_margin

noncomputable def c3 : ℝ := (1576155807/7812500000:ℝ)
noncomputable def d3 : ℝ := (1972992126517/1000000000000:ℝ)
theorem proof_representation_3 : 0 ≤ c3 ∧ c3 ≤ (46620065429335938079480428286073650691261890765919884043/231080746933800000000000000000000000000000000000000000000:ℝ) ∧ (46620065429335938079480428286073650691261890765919884043/231080746933800000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c3 ∧ 0 ≤ d3 ∧ (841518382556771885608863240771404980543496277920807474889/426518875188050000000000000000000000000000000000000000000:ℝ) ≤ d3 ∧ d3 ≤ (841518382556771885608863240771404980543496277920807474889/426518875188050000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c3,d3]
theorem proof_3_c_number : c3 ≤ p3 ((447/16:ℝ)/2)-q ((1773/64:ℝ)/2)*exp (-(1773/64:ℝ)/4)+(-22/25:ℝ) := by
  unfold c3 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_3_c_number
theorem proof_3_d_number : ppUpper ((1773/64:ℝ)-1)+(43/50:ℝ) ≤ d3 := by
  unfold ppUpper ppExpSum p3 d3
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_3_d_number
theorem proof_3_margin : (1/25:ℝ) ≤ endpointMargin (1773/64:ℝ) (447/16:ℝ) c3 d3 := by
  unfold endpointMargin c3 d3
  interval_decide 80 (trust := kernel)
#print axioms proof_3_margin

noncomputable def c4 : ℝ := (198695524639/1000000000000:ℝ)
noncomputable def d4 : ℝ := (985497919529/500000000000:ℝ)
theorem proof_representation_4 : 0 ≤ c4 ∧ c4 ≤ (6041628992264308627946757363689053574572218354135785497/30406467399000000000000000000000000000000000000000000000:ℝ) ∧ (6041628992264308627946757363689053574572218354135785497/30406467399000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c4 ∧ 0 ≤ d4 ∧ (13602689467048245077127669401072990198559678828993288477/6901429824200000000000000000000000000000000000000000000:ℝ) ≤ d4 ∧ d4 ≤ (13602689467048245077127669401072990198559678828993288477/6901429824200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c4,d4]
theorem proof_4_c_number : c4 ≤ p3 ((231/8:ℝ)/2)-q ((447/16:ℝ)/2)*exp (-(447/16:ℝ)/4)+(-22/25:ℝ) := by
  unfold c4 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_4_c_number
theorem proof_4_d_number : ppUpper ((447/16:ℝ)-1)+(43/50:ℝ) ≤ d4 := by
  unfold ppUpper ppExpSum p3 d4
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_4_d_number
theorem proof_4_margin : (1/25:ℝ) ≤ endpointMargin (447/16:ℝ) (231/8:ℝ) c4 d4 := by
  unfold endpointMargin c4 d4
  interval_decide 80 (trust := kernel)
#print axioms proof_4_margin

noncomputable def c5 : ℝ := (101728395421/500000000000:ℝ)
noncomputable def d5 : ℝ := (1993707446001/1000000000000:ℝ)
theorem proof_representation_5 : 0 ≤ c5 ∧ c5 ≤ (1496503426694101061880792437830493353270049475582414313/7355386962000000000000000000000000000000000000000000000:ℝ) ∧ (1496503426694101061880792437830493353270049475582414313/7355386962000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c5 ∧ 0 ≤ d5 ∧ (986077112616638307455916656508388420253348915871839037/494594688200000000000000000000000000000000000000000000:ℝ) ≤ d5 ∧ d5 ≤ (986077112616638307455916656508388420253348915871839037/494594688200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c5,d5]
theorem proof_5_c_number : c5 ≤ p3 ((123/4:ℝ)/2)-q ((231/8:ℝ)/2)*exp (-(231/8:ℝ)/4)+(-87/100:ℝ) := by
  unfold c5 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_5_c_number
theorem proof_5_d_number : ppUpper ((231/8:ℝ)-1)+(89/100:ℝ) ≤ d5 := by
  unfold ppUpper ppExpSum p3 d5
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_5_d_number
theorem proof_5_margin : (1/25:ℝ) ≤ endpointMargin (231/8:ℝ) (123/4:ℝ) c5 d5 := by
  unfold endpointMargin c5 d5
  interval_decide 80 (trust := kernel)
#print axioms proof_5_margin

noncomputable def c6 : ℝ := (194812957221/1000000000000:ℝ)
noncomputable def d6 : ℝ := (2091832675601/1000000000000:ℝ)
theorem proof_representation_6 : 0 ≤ c6 ∧ c6 ≤ (23906737380638527430086679783737460783421856010802443/122716362000000000000000000000000000000000000000000000:ℝ) ∧ (23906737380638527430086679783737460783421856010802443/122716362000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c6 ∧ 0 ≤ d6 ∧ (83896681702804002900123516842570761987075155309578641/40106784200000000000000000000000000000000000000000000:ℝ) ≤ d6 ∧ d6 ≤ (83896681702804002900123516842570761987075155309578641/40106784200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c6,d6]
theorem proof_6_c_number : c6 ≤ p3 ((69/2:ℝ)/2)-q ((123/4:ℝ)/2)*exp (-(123/4:ℝ)/4)+(-87/100:ℝ) := by
  unfold c6 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_6_c_number
theorem proof_6_d_number : ppUpper ((123/4:ℝ)-1)+(1:ℝ) ≤ d6 := by
  unfold ppUpper ppExpSum p3 d6
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_6_d_number
theorem proof_6_margin : (1/25:ℝ) ≤ endpointMargin (123/4:ℝ) (69/2:ℝ) c6 d6 := by
  unfold endpointMargin c6 d6
  interval_decide 80 (trust := kernel)
#print axioms proof_6_margin

noncomputable def c7 : ℝ := (3274972973/62500000000:ℝ)
noncomputable def d7 : ℝ := (102761047567/50000000000:ℝ)
theorem proof_representation_7 : 0 ≤ c7 ∧ c7 ≤ (171139398060153797548950417313217381037044060990117/3266046000000000000000000000000000000000000000000000:ℝ) ∧ (171139398060153797548950417313217381037044060990117/3266046000000000000000000000000000000000000000000000:ℝ)-1/(10:ℝ)^12 ≤ c7 ∧ 0 ≤ d7 ∧ (8283001214435345513897737423267212443286714082180233/4030224200000000000000000000000000000000000000000000:ℝ) ≤ d7 ∧ d7 ≤ (8283001214435345513897737423267212443286714082180233/4030224200000000000000000000000000000000000000000000:ℝ)+1/(10:ℝ)^12 := by
  norm_num [c7,d7]
theorem proof_7_c_number : c7 ≤ p3 ((42:ℝ)/2)-q ((69/2:ℝ)/2)*exp (-(69/2:ℝ)/4)+(-1:ℝ) := by
  unfold c7 p3 q
  interval_decide 80 (trust := kernel)
#print axioms proof_7_c_number
theorem proof_7_d_number : ppUpper ((69/2:ℝ)-1)+(49/50:ℝ) ≤ d7 := by
  unfold ppUpper ppExpSum p3 d7
  norm_num only [sum_range_succ,Nat.cast_zero,Nat.cast_add,Nat.cast_ofNat,zero_add]
  interval_decide 80 (trust := kernel)
#print axioms proof_7_d_number
theorem proof_7_margin : (1/25:ℝ) ≤ endpointMargin (69/2:ℝ) (42:ℝ) c7 d7 := by
  unfold endpointMargin c7 d7
  interval_decide 80 (trust := kernel)
#print axioms proof_7_margin
end Ramanujan640

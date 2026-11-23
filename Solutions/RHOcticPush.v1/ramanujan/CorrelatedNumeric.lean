import RamCorrelatedCore

namespace RHOcticPush.Correlated
open Real RHContinuation.Ramanujan Ramanujan640
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

/-- Only a definitional expansion of the proved pair budget at x=e^z,y=e^(z−1).
It is suitable for certified interval arithmetic on a complete real interval. -/
noncomputable def numericBudget (k z : ℝ) : ℝ :=
  k * ((693/5000:ℝ)*exp (z/2)/(z*(z-5))-
    (693/5000:ℝ)*exp ((z-1)/2)/((z-1)*((z-1)-5))+
    2*((231/5000:ℝ)*exp (z-1)*exp ((z-1)/2)+(919/500:ℝ)*exp (z-1)+
      19851/10000+(5097/10000:ℝ)/exp (z-1))*
      (1/(exp (z-1)*(z-1)^2))+(919/500:ℝ)/(z-1))+
    (exp 1-k)*((1551/100:ℝ)+
      (693/5000:ℝ)*exp ((z-1)/2)/((z-1)*((z-1)-5)))

lemma numericBudget_eq (k z : ℝ) :
    numericBudget k z=GM.pairBudget k (exp (z-1)) (exp z) := by
  unfold numericBudget GM.pairBudget GM.leading gmEnvelope gmWeight
  simp only [Real.log_exp,←Real.exp_half]

noncomputable def numericMargin (k a b z : ℝ) : ℝ :=
  fullBase z+1/1600+k*F z*a-H z*b-(q z)^2*Q z-T z*numericBudget k z

lemma numericMargin_eq {k a b z : ℝ} (hz : z ≠ 0) :
    numericMargin k a b z=margin k a b z := by
  unfold numericMargin margin
  rw [SharpBase.sharpBase_eq_full hz,numericBudget_eq]

#print axioms numericBudget_eq
#print axioms numericMargin_eq
end RHOcticPush.Correlated

import GaussianCanonicalConsumers
open Real Filter IEANTN.CMSFunctional
example : RHAsymptoticGaussian.v1.normalized_gap = (∀ n : ℕ, 1000 ≤ n → normalizedGap n ≤ (834021/1000000 : ℝ)) := rfl

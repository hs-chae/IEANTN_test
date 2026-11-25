import FiniteLogSquared
import IEANTN.Nodes.FiniteLogSquaredPrimeGaps.v1.Conclusions
import IEANTN.Nodes.PrimeInterval.v5.Conclusions

namespace PrimeInterval.v5

theorem challenge_closed_width1550 (hgap : PrimeGapTable.v1.gaps) :
    closed_width1550 := by
  intro x hx hxQ
  exact RH080.FiniteFrontier.closed_width1550 hgap hx hxQ

theorem challenge_strict_width1550_add (hgap : PrimeGapTable.v1.gaps) :
    strict_width1550_add := by
  intro ε hε x hx hxQ
  exact RH080.FiniteFrontier.strict_width1550_add hgap hx hxQ hε

theorem challenge_strict_log_squared (hsource : FiniteLogSquaredPrimeGaps.v1.gaps) :
    strict_log_squared := by
  intro x hx hx42
  exact RH080.FiniteFrontier.strict_log_squared hsource hx hx42

theorem challenge_strict_minimum_width (hgap : PrimeGapTable.v1.gaps)
    (hsource : FiniteLogSquaredPrimeGaps.v1.gaps) : strict_minimum_width := by
  intro ε hε x hx hx42
  exact RH080.FiniteFrontier.strict_minimum_width hgap hsource hx hx42 hε

#print axioms challenge_closed_width1550
#print axioms challenge_strict_width1550_add
#print axioms challenge_strict_log_squared
#print axioms challenge_strict_minimum_width
end PrimeInterval.v5

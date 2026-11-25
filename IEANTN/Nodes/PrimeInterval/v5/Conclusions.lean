import IEANTN.Vocabulary.FinitePrimeFrontier

namespace PrimeInterval.v5
/-- Finite source table, exact terminal-prime domain, closed width1550. -/
def closed_width1550 : Prop := IEANTN.FinitePrimeFrontier.closedWidth1550
/-- Any positive epsilon suffices for a strict upper endpoint. -/
def strict_width1550_add : Prop := IEANTN.FinitePrimeFrontier.strictWidth1550Add
/-- The separate logarithmic-gap source gives a strict all-real finite window. -/
def strict_log_squared : Prop := IEANTN.FinitePrimeFrontier.strictLogSquared
/-- The smaller of two justified finite widths, with both source inputs explicit. -/
def strict_minimum_width : Prop := IEANTN.FinitePrimeFrontier.strictMinimumWidth
end PrimeInterval.v5

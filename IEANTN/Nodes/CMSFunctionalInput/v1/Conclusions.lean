import IEANTN.Vocabulary.CMSFunctional

namespace CMSFunctionalInput.v1
/-- General numerical-free consequence of CMS Corollary4 (1.14), optimization
(1.3), and the Brun--Titchmarsh bound (1.12). Literature-backed B input. -/
def gap_reduction : Prop := IEANTN.CMSFunctional.SourceCMSFunctional
/-- General numerical-free functional infimum bound from CMS Theorem3 (1.13).
Nonemptiness and strict limiting count margin are part of the exact input. -/
def population_reduction : Prop := IEANTN.CMSFunctional.SourceCMSPopulation
end CMSFunctionalInput.v1

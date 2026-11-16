/- The source model's own emitted high words, linked by accepted pure evaluations. -/
import SynergyMomentC.WordBridge
import SourceMomentWordsV1.All
namespace SynergyMomentC.WordValues
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
noncomputable section
theorem source_words (i : Nat) (hi : i < 768) :
 Model.highPair (modelPair i)=SourceMomentWordsV1.All.word i :=
 @WordBridge.source_words i (SourceMomentWordsV1.All.word i)
   (SourceMomentWordsV1.All.all_words i hi)
#print axioms source_words
end
end SynergyMomentC.WordValues

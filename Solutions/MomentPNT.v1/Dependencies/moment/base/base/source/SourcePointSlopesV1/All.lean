import SourcePointSlopesV1.Block00
import SourcePointSlopesV1.Block01
import SourcePointSlopesV1.Block02
import SourcePointSlopesV1.Block03
import SourcePointSlopesV1.Block04
import SourcePointSlopesV1.Block05
import SourcePointSlopesV1.Block06
import SourcePointSlopesV1.Block07
import SourcePointSlopesV1.Block08
import SourcePointSlopesV1.Block09
import SourcePointSlopesV1.Block10
import SourcePointSlopesV1.Block11
import SourcePointSlopesV1.Block12
import SourcePointSlopesV1.Block13
import SourcePointSlopesV1.Block14
import SourcePointSlopesV1.Block15
import SourcePointSlopesV1.Block16
import SourcePointSlopesV1.Block17
import SourcePointSlopesV1.Block18
import SourcePointSlopesV1.Block19
import SourcePointSlopesV1.Block20
import SourcePointSlopesV1.Block21
import SourcePointSlopesV1.Block22
import SourcePointSlopesV1.Block23
import SourcePointSlopesV1.Block24
import SourcePointSlopesV1.Block25
import SourcePointSlopesV1.Block26
import SourcePointSlopesV1.Block27
import SourcePointSlopesV1.Block28
import SourcePointSlopesV1.Block29
import SourcePointSlopesV1.Block30
import SourcePointSlopesV1.Block31
import SourcePointSlopesV1.Block32
import SourcePointSlopesV1.Block33
import SourcePointSlopesV1.Block34
import SourcePointSlopesV1.Block35
import SourcePointSlopesV1.Block36
import SourcePointSlopesV1.Block37
import SourcePointSlopesV1.Block38
import SourcePointSlopesV1.Block39
import SourcePointSlopesV1.Block40
import SourcePointSlopesV1.Block41
import SourcePointSlopesV1.Block42
import SourcePointSlopesV1.Block43
import SourcePointSlopesV1.Block44
import SourcePointSlopesV1.Block45
import SourcePointSlopesV1.Block46
import SourcePointSlopesV1.Block47
import SourcePointSlopesV1.Block48
import SourcePointSlopesV1.Block49
import SourcePointSlopesV1.Block50
import SourcePointSlopesV1.Block51
import SourcePointSlopesV1.Block52
import SourcePointSlopesV1.Block53
import SourcePointSlopesV1.Block54
import SourcePointSlopesV1.Block55
import SourcePointSlopesV1.Block56
import SourcePointSlopesV1.Block57
import SourcePointSlopesV1.Block58
import SourcePointSlopesV1.Block59
import SourcePointSlopesV1.Block60
import SourcePointSlopesV1.Block61
import SourcePointSlopesV1.Block62
import SourcePointSlopesV1.Block63
import SourcePointSlopesV1.Block64
import SourcePointSlopesV1.Block65
import SourcePointSlopesV1.Block66
import SourcePointSlopesV1.Block67
import SourcePointSlopesV1.Block68
import SourcePointSlopesV1.Block69
import SourcePointSlopesV1.Block70
import SourcePointSlopesV1.Block71
import SourcePointSlopesV1.Block72
import SourcePointSlopesV1.Block73
import SourcePointSlopesV1.Block74
import SourcePointSlopesV1.Block75
import SourcePointSlopesV1.Block76
import SourcePointSlopesV1.Block77
import SourcePointSlopesV1.Block78
import SourcePointSlopesV1.Block79
import SourcePointSlopesV1.Block80
import SourcePointSlopesV1.Block81
import SourcePointSlopesV1.Block82
import SourcePointSlopesV1.Block83
import SourcePointSlopesV1.Block84
import SourcePointSlopesV1.Block85
import SourcePointSlopesV1.Block86
import SourcePointSlopesV1.Block87
import SourcePointSlopesV1.Block88
import SourcePointSlopesV1.Block89
import SourcePointSlopesV1.Block90
import SourcePointSlopesV1.Block91
import SourcePointSlopesV1.Block92
import SourcePointSlopesV1.Block93
import SourcePointSlopesV1.Block94
import SourcePointSlopesV1.Block95
import SourceMainWeightsV1.All
import Mathlib.Tactic.IntervalCases
namespace SourcePointSlopesV1.All
open ScopedNumerical SynergyHeightC.MainWeightModel SynergyAnalytic.HeightPoint
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem bounds (i : Nat) (hi : i < logCellCount) :
    77 ≤ pointD i ∧ pointD i ≤ 163 := by
 have domain := SourceMainWeightsV1.All.all_domains i hi
 change i < 768 at hi
 let b := i / 8
 have hb : b < 96 := by dsimp [b]; omega
 have lower : 8*b ≤ i := by dsimp [b]; omega
 have upper : i < 8*(b+1) := by dsimp [b]; omega
 interval_cases b
 · exact SourcePointSlopesV1.Block00.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block01.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block02.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block03.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block04.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block05.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block06.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block07.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block08.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block09.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block10.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block11.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block12.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block13.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block14.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block15.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block16.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block17.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block18.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block19.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block20.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block21.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block22.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block23.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block24.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block25.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block26.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block27.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block28.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block29.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block30.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block31.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block32.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block33.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block34.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block35.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block36.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block37.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block38.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block39.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block40.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block41.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block42.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block43.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block44.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block45.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block46.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block47.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block48.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block49.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block50.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block51.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block52.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block53.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block54.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block55.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block56.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block57.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block58.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block59.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block60.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block61.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block62.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block63.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block64.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block65.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block66.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block67.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block68.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block69.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block70.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block71.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block72.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block73.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block74.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block75.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block76.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block77.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block78.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block79.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block80.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block81.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block82.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block83.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block84.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block85.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block86.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block87.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block88.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block89.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block90.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block91.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block92.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block93.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block94.bounds i (by omega) (by omega) domain
 · exact SourcePointSlopesV1.Block95.bounds i (by omega) (by omega) domain

#print axioms bounds
end SourcePointSlopesV1.All

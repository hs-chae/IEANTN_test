import SourceMomentFamilyV1.Block00
import SourceMomentFamilyV1.Block01
import SourceMomentFamilyV1.Block02
import SourceMomentFamilyV1.Block03
import SourceMomentFamilyV1.Block04
import SourceMomentFamilyV1.Block05
import SourceMomentFamilyV1.Block06
import SourceMomentFamilyV1.Block07
import SourceMomentFamilyV1.Block08
import SourceMomentFamilyV1.Block09
import SourceMomentFamilyV1.Block10
import SourceMomentFamilyV1.Block11
import SourceMomentFamilyV1.Block12
import SourceMomentFamilyV1.Block13
import SourceMomentFamilyV1.Block14
import SourceMomentFamilyV1.Block15
import SourceMomentFamilyV1.Block16
import SourceMomentFamilyV1.Block17
import SourceMomentFamilyV1.Block18
import SourceMomentFamilyV1.Block19
import SourceMomentFamilyV1.Block20
import SourceMomentFamilyV1.Block21
import SourceMomentFamilyV1.Block22
import SourceMomentFamilyV1.Block23
import SourceMomentFamilyV1.Block24
import SourceMomentFamilyV1.Block25
import SourceMomentFamilyV1.Block26
import SourceMomentFamilyV1.Block27
import SourceMomentFamilyV1.Block28
import SourceMomentFamilyV1.Block29
import SourceMomentFamilyV1.Block30
import SourceMomentFamilyV1.Block31
import SourceMomentFamilyV1.Block32
import SourceMomentFamilyV1.Block33
import SourceMomentFamilyV1.Block34
import SourceMomentFamilyV1.Block35
import SourceMomentFamilyV1.Block36
import SourceMomentFamilyV1.Block37
import SourceMomentFamilyV1.Block38
import SourceMomentFamilyV1.Block39
import SourceMomentFamilyV1.Block40
import SourceMomentFamilyV1.Block41
import SourceMomentFamilyV1.Block42
import SourceMomentFamilyV1.Block43
import SourceMomentFamilyV1.Block44
import SourceMomentFamilyV1.Block45
import SourceMomentFamilyV1.Block46
import SourceMomentFamilyV1.Block47
import SourceMomentFamilyV1.Block48
import SourceMomentFamilyV1.Block49
import SourceMomentFamilyV1.Block50
import SourceMomentFamilyV1.Block51
import SourceMomentFamilyV1.Block52
import SourceMomentFamilyV1.Block53
import SourceMomentFamilyV1.Block54
import SourceMomentFamilyV1.Block55
import SourceMomentFamilyV1.Block56
import SourceMomentFamilyV1.Block57
import SourceMomentFamilyV1.Block58
import SourceMomentFamilyV1.Block59
import SourceMomentFamilyV1.Block60
import SourceMomentFamilyV1.Block61
import SourceMomentFamilyV1.Block62
import SourceMomentFamilyV1.Block63
import SourceMomentFamilyV1.Block64
import SourceMomentFamilyV1.Block65
import SourceMomentFamilyV1.Block66
import SourceMomentFamilyV1.Block67
import SourceMomentFamilyV1.Block68
import SourceMomentFamilyV1.Block69
import SourceMomentFamilyV1.Block70
import SourceMomentFamilyV1.Block71
import SourceMomentFamilyV1.Block72
import SourceMomentFamilyV1.Block73
import SourceMomentFamilyV1.Block74
import SourceMomentFamilyV1.Block75
import SourceMomentFamilyV1.Block76
import SourceMomentFamilyV1.Block77
import SourceMomentFamilyV1.Block78
import SourceMomentFamilyV1.Block79
import SourceMomentFamilyV1.Block80
import SourceMomentFamilyV1.Block81
import SourceMomentFamilyV1.Block82
import SourceMomentFamilyV1.Block83
import SourceMomentFamilyV1.Block84
import SourceMomentFamilyV1.Block85
import SourceMomentFamilyV1.Block86
import SourceMomentFamilyV1.Block87
import SourceMomentFamilyV1.Block88
import SourceMomentFamilyV1.Block89
import SourceMomentFamilyV1.Block90
import SourceMomentFamilyV1.Block91
import SourceMomentFamilyV1.Block92
import SourceMomentFamilyV1.Block93
import SourceMomentFamilyV1.Block94
import SourceMomentFamilyV1.Block95
import Mathlib.Tactic.IntervalCases
namespace SourceMomentFamilyV1.All
open SynergyMomentC SynergyMomentCHi
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem rows (kind : Kind) (i : Nat) (hi : i < 768) : FamilyAPI.ExactRow kind i := by
 let b:=i/8
 have hb : b < 96 := by dsimp [b];omega
 have lower : 8*b ≤ i := by dsimp [b];omega
 have upper : i < 8*b+8 := by dsimp [b];omega
 interval_cases b
 · exact Block00.rows kind i (by omega) (by omega)
 · exact Block01.rows kind i (by omega) (by omega)
 · exact Block02.rows kind i (by omega) (by omega)
 · exact Block03.rows kind i (by omega) (by omega)
 · exact Block04.rows kind i (by omega) (by omega)
 · exact Block05.rows kind i (by omega) (by omega)
 · exact Block06.rows kind i (by omega) (by omega)
 · exact Block07.rows kind i (by omega) (by omega)
 · exact Block08.rows kind i (by omega) (by omega)
 · exact Block09.rows kind i (by omega) (by omega)
 · exact Block10.rows kind i (by omega) (by omega)
 · exact Block11.rows kind i (by omega) (by omega)
 · exact Block12.rows kind i (by omega) (by omega)
 · exact Block13.rows kind i (by omega) (by omega)
 · exact Block14.rows kind i (by omega) (by omega)
 · exact Block15.rows kind i (by omega) (by omega)
 · exact Block16.rows kind i (by omega) (by omega)
 · exact Block17.rows kind i (by omega) (by omega)
 · exact Block18.rows kind i (by omega) (by omega)
 · exact Block19.rows kind i (by omega) (by omega)
 · exact Block20.rows kind i (by omega) (by omega)
 · exact Block21.rows kind i (by omega) (by omega)
 · exact Block22.rows kind i (by omega) (by omega)
 · exact Block23.rows kind i (by omega) (by omega)
 · exact Block24.rows kind i (by omega) (by omega)
 · exact Block25.rows kind i (by omega) (by omega)
 · exact Block26.rows kind i (by omega) (by omega)
 · exact Block27.rows kind i (by omega) (by omega)
 · exact Block28.rows kind i (by omega) (by omega)
 · exact Block29.rows kind i (by omega) (by omega)
 · exact Block30.rows kind i (by omega) (by omega)
 · exact Block31.rows kind i (by omega) (by omega)
 · exact Block32.rows kind i (by omega) (by omega)
 · exact Block33.rows kind i (by omega) (by omega)
 · exact Block34.rows kind i (by omega) (by omega)
 · exact Block35.rows kind i (by omega) (by omega)
 · exact Block36.rows kind i (by omega) (by omega)
 · exact Block37.rows kind i (by omega) (by omega)
 · exact Block38.rows kind i (by omega) (by omega)
 · exact Block39.rows kind i (by omega) (by omega)
 · exact Block40.rows kind i (by omega) (by omega)
 · exact Block41.rows kind i (by omega) (by omega)
 · exact Block42.rows kind i (by omega) (by omega)
 · exact Block43.rows kind i (by omega) (by omega)
 · exact Block44.rows kind i (by omega) (by omega)
 · exact Block45.rows kind i (by omega) (by omega)
 · exact Block46.rows kind i (by omega) (by omega)
 · exact Block47.rows kind i (by omega) (by omega)
 · exact Block48.rows kind i (by omega) (by omega)
 · exact Block49.rows kind i (by omega) (by omega)
 · exact Block50.rows kind i (by omega) (by omega)
 · exact Block51.rows kind i (by omega) (by omega)
 · exact Block52.rows kind i (by omega) (by omega)
 · exact Block53.rows kind i (by omega) (by omega)
 · exact Block54.rows kind i (by omega) (by omega)
 · exact Block55.rows kind i (by omega) (by omega)
 · exact Block56.rows kind i (by omega) (by omega)
 · exact Block57.rows kind i (by omega) (by omega)
 · exact Block58.rows kind i (by omega) (by omega)
 · exact Block59.rows kind i (by omega) (by omega)
 · exact Block60.rows kind i (by omega) (by omega)
 · exact Block61.rows kind i (by omega) (by omega)
 · exact Block62.rows kind i (by omega) (by omega)
 · exact Block63.rows kind i (by omega) (by omega)
 · exact Block64.rows kind i (by omega) (by omega)
 · exact Block65.rows kind i (by omega) (by omega)
 · exact Block66.rows kind i (by omega) (by omega)
 · exact Block67.rows kind i (by omega) (by omega)
 · exact Block68.rows kind i (by omega) (by omega)
 · exact Block69.rows kind i (by omega) (by omega)
 · exact Block70.rows kind i (by omega) (by omega)
 · exact Block71.rows kind i (by omega) (by omega)
 · exact Block72.rows kind i (by omega) (by omega)
 · exact Block73.rows kind i (by omega) (by omega)
 · exact Block74.rows kind i (by omega) (by omega)
 · exact Block75.rows kind i (by omega) (by omega)
 · exact Block76.rows kind i (by omega) (by omega)
 · exact Block77.rows kind i (by omega) (by omega)
 · exact Block78.rows kind i (by omega) (by omega)
 · exact Block79.rows kind i (by omega) (by omega)
 · exact Block80.rows kind i (by omega) (by omega)
 · exact Block81.rows kind i (by omega) (by omega)
 · exact Block82.rows kind i (by omega) (by omega)
 · exact Block83.rows kind i (by omega) (by omega)
 · exact Block84.rows kind i (by omega) (by omega)
 · exact Block85.rows kind i (by omega) (by omega)
 · exact Block86.rows kind i (by omega) (by omega)
 · exact Block87.rows kind i (by omega) (by omega)
 · exact Block88.rows kind i (by omega) (by omega)
 · exact Block89.rows kind i (by omega) (by omega)
 · exact Block90.rows kind i (by omega) (by omega)
 · exact Block91.rows kind i (by omega) (by omega)
 · exact Block92.rows kind i (by omega) (by omega)
 · exact Block93.rows kind i (by omega) (by omega)
 · exact Block94.rows kind i (by omega) (by omega)
 · exact Block95.rows kind i (by omega) (by omega)
#print axioms rows
end SourceMomentFamilyV1.All

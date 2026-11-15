/- All proposed prefix steps are accepted only through the96kernel checks. -/
import SourceMomentSumsV1.Data
import SynergyMomentMath.Fold
import SourceMomentSumsV1.Block00
import SourceMomentSumsV1.Block01
import SourceMomentSumsV1.Block02
import SourceMomentSumsV1.Block03
import SourceMomentSumsV1.Block04
import SourceMomentSumsV1.Block05
import SourceMomentSumsV1.Block06
import SourceMomentSumsV1.Block07
import SourceMomentSumsV1.Block08
import SourceMomentSumsV1.Block09
import SourceMomentSumsV1.Block10
import SourceMomentSumsV1.Block11
import SourceMomentSumsV1.Block12
import SourceMomentSumsV1.Block13
import SourceMomentSumsV1.Block14
import SourceMomentSumsV1.Block15
import SourceMomentSumsV1.Block16
import SourceMomentSumsV1.Block17
import SourceMomentSumsV1.Block18
import SourceMomentSumsV1.Block19
import SourceMomentSumsV1.Block20
import SourceMomentSumsV1.Block21
import SourceMomentSumsV1.Block22
import SourceMomentSumsV1.Block23
import SourceMomentSumsV1.Block24
import SourceMomentSumsV1.Block25
import SourceMomentSumsV1.Block26
import SourceMomentSumsV1.Block27
import SourceMomentSumsV1.Block28
import SourceMomentSumsV1.Block29
import SourceMomentSumsV1.Block30
import SourceMomentSumsV1.Block31
import SourceMomentSumsV1.Block32
import SourceMomentSumsV1.Block33
import SourceMomentSumsV1.Block34
import SourceMomentSumsV1.Block35
import SourceMomentSumsV1.Block36
import SourceMomentSumsV1.Block37
import SourceMomentSumsV1.Block38
import SourceMomentSumsV1.Block39
import SourceMomentSumsV1.Block40
import SourceMomentSumsV1.Block41
import SourceMomentSumsV1.Block42
import SourceMomentSumsV1.Block43
import SourceMomentSumsV1.Block44
import SourceMomentSumsV1.Block45
import SourceMomentSumsV1.Block46
import SourceMomentSumsV1.Block47
import SourceMomentSumsV1.Block48
import SourceMomentSumsV1.Block49
import SourceMomentSumsV1.Block50
import SourceMomentSumsV1.Block51
import SourceMomentSumsV1.Block52
import SourceMomentSumsV1.Block53
import SourceMomentSumsV1.Block54
import SourceMomentSumsV1.Block55
import SourceMomentSumsV1.Block56
import SourceMomentSumsV1.Block57
import SourceMomentSumsV1.Block58
import SourceMomentSumsV1.Block59
import SourceMomentSumsV1.Block60
import SourceMomentSumsV1.Block61
import SourceMomentSumsV1.Block62
import SourceMomentSumsV1.Block63
import SourceMomentSumsV1.Block64
import SourceMomentSumsV1.Block65
import SourceMomentSumsV1.Block66
import SourceMomentSumsV1.Block67
import SourceMomentSumsV1.Block68
import SourceMomentSumsV1.Block69
import SourceMomentSumsV1.Block70
import SourceMomentSumsV1.Block71
import SourceMomentSumsV1.Block72
import SourceMomentSumsV1.Block73
import SourceMomentSumsV1.Block74
import SourceMomentSumsV1.Block75
import SourceMomentSumsV1.Block76
import SourceMomentSumsV1.Block77
import SourceMomentSumsV1.Block78
import SourceMomentSumsV1.Block79
import SourceMomentSumsV1.Block80
import SourceMomentSumsV1.Block81
import SourceMomentSumsV1.Block82
import SourceMomentSumsV1.Block83
import SourceMomentSumsV1.Block84
import SourceMomentSumsV1.Block85
import SourceMomentSumsV1.Block86
import SourceMomentSumsV1.Block87
import SourceMomentSumsV1.Block88
import SourceMomentSumsV1.Block89
import SourceMomentSumsV1.Block90
import SourceMomentSumsV1.Block91
import SourceMomentSumsV1.Block92
import SourceMomentSumsV1.Block93
import SourceMomentSumsV1.Block94
import SourceMomentSumsV1.Block95
namespace SourceMomentSumsV1.All
open ScopedNumerical SynergyMomentMath.Cells
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
def mass_rows : List Row := (Block00.mass++(Block01.mass++(Block02.mass++(Block03.mass++(Block04.mass++(Block05.mass++(Block06.mass++(Block07.mass++(Block08.mass++(Block09.mass++(Block10.mass++(Block11.mass++(Block12.mass++(Block13.mass++(Block14.mass++(Block15.mass++(Block16.mass++(Block17.mass++(Block18.mass++(Block19.mass++(Block20.mass++(Block21.mass++(Block22.mass++(Block23.mass++(Block24.mass++(Block25.mass++(Block26.mass++(Block27.mass++(Block28.mass++(Block29.mass++(Block30.mass++(Block31.mass++(Block32.mass++(Block33.mass++(Block34.mass++(Block35.mass++(Block36.mass++(Block37.mass++(Block38.mass++(Block39.mass++(Block40.mass++(Block41.mass++(Block42.mass++(Block43.mass++(Block44.mass++(Block45.mass++(Block46.mass++(Block47.mass++(Block48.mass++(Block49.mass++(Block50.mass++(Block51.mass++(Block52.mass++(Block53.mass++(Block54.mass++(Block55.mass++(Block56.mass++(Block57.mass++(Block58.mass++(Block59.mass++(Block60.mass++(Block61.mass++(Block62.mass++(Block63.mass++(Block64.mass++(Block65.mass++(Block66.mass++(Block67.mass++(Block68.mass++(Block69.mass++(Block70.mass++(Block71.mass++(Block72.mass++(Block73.mass++(Block74.mass++(Block75.mass++(Block76.mass++(Block77.mass++(Block78.mass++(Block79.mass++(Block80.mass++(Block81.mass++(Block82.mass++(Block83.mass++(Block84.mass++(Block85.mass++(Block86.mass++(Block87.mass++(Block88.mass++(Block89.mass++(Block90.mass++(Block91.mass++(Block92.mass++(Block93.mass++(Block94.mass++Block95.mass)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def first_moment_rows : List Row := (Block00.first_moment++(Block01.first_moment++(Block02.first_moment++(Block03.first_moment++(Block04.first_moment++(Block05.first_moment++(Block06.first_moment++(Block07.first_moment++(Block08.first_moment++(Block09.first_moment++(Block10.first_moment++(Block11.first_moment++(Block12.first_moment++(Block13.first_moment++(Block14.first_moment++(Block15.first_moment++(Block16.first_moment++(Block17.first_moment++(Block18.first_moment++(Block19.first_moment++(Block20.first_moment++(Block21.first_moment++(Block22.first_moment++(Block23.first_moment++(Block24.first_moment++(Block25.first_moment++(Block26.first_moment++(Block27.first_moment++(Block28.first_moment++(Block29.first_moment++(Block30.first_moment++(Block31.first_moment++(Block32.first_moment++(Block33.first_moment++(Block34.first_moment++(Block35.first_moment++(Block36.first_moment++(Block37.first_moment++(Block38.first_moment++(Block39.first_moment++(Block40.first_moment++(Block41.first_moment++(Block42.first_moment++(Block43.first_moment++(Block44.first_moment++(Block45.first_moment++(Block46.first_moment++(Block47.first_moment++(Block48.first_moment++(Block49.first_moment++(Block50.first_moment++(Block51.first_moment++(Block52.first_moment++(Block53.first_moment++(Block54.first_moment++(Block55.first_moment++(Block56.first_moment++(Block57.first_moment++(Block58.first_moment++(Block59.first_moment++(Block60.first_moment++(Block61.first_moment++(Block62.first_moment++(Block63.first_moment++(Block64.first_moment++(Block65.first_moment++(Block66.first_moment++(Block67.first_moment++(Block68.first_moment++(Block69.first_moment++(Block70.first_moment++(Block71.first_moment++(Block72.first_moment++(Block73.first_moment++(Block74.first_moment++(Block75.first_moment++(Block76.first_moment++(Block77.first_moment++(Block78.first_moment++(Block79.first_moment++(Block80.first_moment++(Block81.first_moment++(Block82.first_moment++(Block83.first_moment++(Block84.first_moment++(Block85.first_moment++(Block86.first_moment++(Block87.first_moment++(Block88.first_moment++(Block89.first_moment++(Block90.first_moment++(Block91.first_moment++(Block92.first_moment++(Block93.first_moment++(Block94.first_moment++Block95.first_moment)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def rows : Stat→List Row
 | .mass=>mass_rows
 | .firstMoment=>first_moment_rows
private theorem append_checked {a b : List Row} (stat : Stat)
 (ha : a.all (check stat)=true) (hb : b.all (check stat)=true) :
 (a++b).all (check stat)=true := by rw [List.all_append,ha,hb];rfl
theorem checked (stat : Stat) : (rows stat).all (check stat)=true := by
 cases stat with
 | mass=>exact (append_checked .mass Block00.mass_checked (append_checked .mass Block01.mass_checked (append_checked .mass Block02.mass_checked (append_checked .mass Block03.mass_checked (append_checked .mass Block04.mass_checked (append_checked .mass Block05.mass_checked (append_checked .mass Block06.mass_checked (append_checked .mass Block07.mass_checked (append_checked .mass Block08.mass_checked (append_checked .mass Block09.mass_checked (append_checked .mass Block10.mass_checked (append_checked .mass Block11.mass_checked (append_checked .mass Block12.mass_checked (append_checked .mass Block13.mass_checked (append_checked .mass Block14.mass_checked (append_checked .mass Block15.mass_checked (append_checked .mass Block16.mass_checked (append_checked .mass Block17.mass_checked (append_checked .mass Block18.mass_checked (append_checked .mass Block19.mass_checked (append_checked .mass Block20.mass_checked (append_checked .mass Block21.mass_checked (append_checked .mass Block22.mass_checked (append_checked .mass Block23.mass_checked (append_checked .mass Block24.mass_checked (append_checked .mass Block25.mass_checked (append_checked .mass Block26.mass_checked (append_checked .mass Block27.mass_checked (append_checked .mass Block28.mass_checked (append_checked .mass Block29.mass_checked (append_checked .mass Block30.mass_checked (append_checked .mass Block31.mass_checked (append_checked .mass Block32.mass_checked (append_checked .mass Block33.mass_checked (append_checked .mass Block34.mass_checked (append_checked .mass Block35.mass_checked (append_checked .mass Block36.mass_checked (append_checked .mass Block37.mass_checked (append_checked .mass Block38.mass_checked (append_checked .mass Block39.mass_checked (append_checked .mass Block40.mass_checked (append_checked .mass Block41.mass_checked (append_checked .mass Block42.mass_checked (append_checked .mass Block43.mass_checked (append_checked .mass Block44.mass_checked (append_checked .mass Block45.mass_checked (append_checked .mass Block46.mass_checked (append_checked .mass Block47.mass_checked (append_checked .mass Block48.mass_checked (append_checked .mass Block49.mass_checked (append_checked .mass Block50.mass_checked (append_checked .mass Block51.mass_checked (append_checked .mass Block52.mass_checked (append_checked .mass Block53.mass_checked (append_checked .mass Block54.mass_checked (append_checked .mass Block55.mass_checked (append_checked .mass Block56.mass_checked (append_checked .mass Block57.mass_checked (append_checked .mass Block58.mass_checked (append_checked .mass Block59.mass_checked (append_checked .mass Block60.mass_checked (append_checked .mass Block61.mass_checked (append_checked .mass Block62.mass_checked (append_checked .mass Block63.mass_checked (append_checked .mass Block64.mass_checked (append_checked .mass Block65.mass_checked (append_checked .mass Block66.mass_checked (append_checked .mass Block67.mass_checked (append_checked .mass Block68.mass_checked (append_checked .mass Block69.mass_checked (append_checked .mass Block70.mass_checked (append_checked .mass Block71.mass_checked (append_checked .mass Block72.mass_checked (append_checked .mass Block73.mass_checked (append_checked .mass Block74.mass_checked (append_checked .mass Block75.mass_checked (append_checked .mass Block76.mass_checked (append_checked .mass Block77.mass_checked (append_checked .mass Block78.mass_checked (append_checked .mass Block79.mass_checked (append_checked .mass Block80.mass_checked (append_checked .mass Block81.mass_checked (append_checked .mass Block82.mass_checked (append_checked .mass Block83.mass_checked (append_checked .mass Block84.mass_checked (append_checked .mass Block85.mass_checked (append_checked .mass Block86.mass_checked (append_checked .mass Block87.mass_checked (append_checked .mass Block88.mass_checked (append_checked .mass Block89.mass_checked (append_checked .mass Block90.mass_checked (append_checked .mass Block91.mass_checked (append_checked .mass Block92.mass_checked (append_checked .mass Block93.mass_checked (append_checked .mass Block94.mass_checked Block95.mass_checked)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 | firstMoment=>exact (append_checked .firstMoment Block00.first_moment_checked (append_checked .firstMoment Block01.first_moment_checked (append_checked .firstMoment Block02.first_moment_checked (append_checked .firstMoment Block03.first_moment_checked (append_checked .firstMoment Block04.first_moment_checked (append_checked .firstMoment Block05.first_moment_checked (append_checked .firstMoment Block06.first_moment_checked (append_checked .firstMoment Block07.first_moment_checked (append_checked .firstMoment Block08.first_moment_checked (append_checked .firstMoment Block09.first_moment_checked (append_checked .firstMoment Block10.first_moment_checked (append_checked .firstMoment Block11.first_moment_checked (append_checked .firstMoment Block12.first_moment_checked (append_checked .firstMoment Block13.first_moment_checked (append_checked .firstMoment Block14.first_moment_checked (append_checked .firstMoment Block15.first_moment_checked (append_checked .firstMoment Block16.first_moment_checked (append_checked .firstMoment Block17.first_moment_checked (append_checked .firstMoment Block18.first_moment_checked (append_checked .firstMoment Block19.first_moment_checked (append_checked .firstMoment Block20.first_moment_checked (append_checked .firstMoment Block21.first_moment_checked (append_checked .firstMoment Block22.first_moment_checked (append_checked .firstMoment Block23.first_moment_checked (append_checked .firstMoment Block24.first_moment_checked (append_checked .firstMoment Block25.first_moment_checked (append_checked .firstMoment Block26.first_moment_checked (append_checked .firstMoment Block27.first_moment_checked (append_checked .firstMoment Block28.first_moment_checked (append_checked .firstMoment Block29.first_moment_checked (append_checked .firstMoment Block30.first_moment_checked (append_checked .firstMoment Block31.first_moment_checked (append_checked .firstMoment Block32.first_moment_checked (append_checked .firstMoment Block33.first_moment_checked (append_checked .firstMoment Block34.first_moment_checked (append_checked .firstMoment Block35.first_moment_checked (append_checked .firstMoment Block36.first_moment_checked (append_checked .firstMoment Block37.first_moment_checked (append_checked .firstMoment Block38.first_moment_checked (append_checked .firstMoment Block39.first_moment_checked (append_checked .firstMoment Block40.first_moment_checked (append_checked .firstMoment Block41.first_moment_checked (append_checked .firstMoment Block42.first_moment_checked (append_checked .firstMoment Block43.first_moment_checked (append_checked .firstMoment Block44.first_moment_checked (append_checked .firstMoment Block45.first_moment_checked (append_checked .firstMoment Block46.first_moment_checked (append_checked .firstMoment Block47.first_moment_checked (append_checked .firstMoment Block48.first_moment_checked (append_checked .firstMoment Block49.first_moment_checked (append_checked .firstMoment Block50.first_moment_checked (append_checked .firstMoment Block51.first_moment_checked (append_checked .firstMoment Block52.first_moment_checked (append_checked .firstMoment Block53.first_moment_checked (append_checked .firstMoment Block54.first_moment_checked (append_checked .firstMoment Block55.first_moment_checked (append_checked .firstMoment Block56.first_moment_checked (append_checked .firstMoment Block57.first_moment_checked (append_checked .firstMoment Block58.first_moment_checked (append_checked .firstMoment Block59.first_moment_checked (append_checked .firstMoment Block60.first_moment_checked (append_checked .firstMoment Block61.first_moment_checked (append_checked .firstMoment Block62.first_moment_checked (append_checked .firstMoment Block63.first_moment_checked (append_checked .firstMoment Block64.first_moment_checked (append_checked .firstMoment Block65.first_moment_checked (append_checked .firstMoment Block66.first_moment_checked (append_checked .firstMoment Block67.first_moment_checked (append_checked .firstMoment Block68.first_moment_checked (append_checked .firstMoment Block69.first_moment_checked (append_checked .firstMoment Block70.first_moment_checked (append_checked .firstMoment Block71.first_moment_checked (append_checked .firstMoment Block72.first_moment_checked (append_checked .firstMoment Block73.first_moment_checked (append_checked .firstMoment Block74.first_moment_checked (append_checked .firstMoment Block75.first_moment_checked (append_checked .firstMoment Block76.first_moment_checked (append_checked .firstMoment Block77.first_moment_checked (append_checked .firstMoment Block78.first_moment_checked (append_checked .firstMoment Block79.first_moment_checked (append_checked .firstMoment Block80.first_moment_checked (append_checked .firstMoment Block81.first_moment_checked (append_checked .firstMoment Block82.first_moment_checked (append_checked .firstMoment Block83.first_moment_checked (append_checked .firstMoment Block84.first_moment_checked (append_checked .firstMoment Block85.first_moment_checked (append_checked .firstMoment Block86.first_moment_checked (append_checked .firstMoment Block87.first_moment_checked (append_checked .firstMoment Block88.first_moment_checked (append_checked .firstMoment Block89.first_moment_checked (append_checked .firstMoment Block90.first_moment_checked (append_checked .firstMoment Block91.first_moment_checked (append_checked .firstMoment Block92.first_moment_checked (append_checked .firstMoment Block93.first_moment_checked (append_checked .firstMoment Block94.first_moment_checked Block95.first_moment_checked)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem rows_eq (stat : Stat) : rows stat=(List.range 768).map (Data.row stat) := by
 cases stat <;> rfl
theorem recurrence (stat : Stat) (i : Nat) (hi : i < 768) :
 ∃ value,cell stat i=some value ∧
  ProofBox.add (Data.total stat i) value=Data.total stat (i+1) := by
 have member : Data.row stat i∈rows stat := by
  rw [rows_eq]
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
 exact @check_sound stat (Data.row stat i)
  ((List.all_eq_true.mp (checked stat)) _ member)
theorem prefix_value (stat : Stat) (n : Nat) (hn : n ≤ 768) :
 SynergyMomentMath.Cells.sum stat n=some (Data.total stat n) :=
 (congrFun (SynergyMomentMath.Fold.cell_sum_function stat) n).trans
  (SynergyMomentMath.Fold.sum_of_recurrence (cell stat) (Data.total stat)
   (Data.zero stat) (recurrence stat) n hn)
#print axioms checked
#print axioms rows_eq
#print axioms recurrence
#print axioms prefix_value
end
end SourceMomentSumsV1.All

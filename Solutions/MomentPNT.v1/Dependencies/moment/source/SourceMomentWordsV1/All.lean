/- Aggregate the96accepted pure highword blocks without reevaluating a point. -/
import SourceMomentWordsV1.Block00
import SourceMomentWordsV1.Block01
import SourceMomentWordsV1.Block02
import SourceMomentWordsV1.Block03
import SourceMomentWordsV1.Block04
import SourceMomentWordsV1.Block05
import SourceMomentWordsV1.Block06
import SourceMomentWordsV1.Block07
import SourceMomentWordsV1.Block08
import SourceMomentWordsV1.Block09
import SourceMomentWordsV1.Block10
import SourceMomentWordsV1.Block11
import SourceMomentWordsV1.Block12
import SourceMomentWordsV1.Block13
import SourceMomentWordsV1.Block14
import SourceMomentWordsV1.Block15
import SourceMomentWordsV1.Block16
import SourceMomentWordsV1.Block17
import SourceMomentWordsV1.Block18
import SourceMomentWordsV1.Block19
import SourceMomentWordsV1.Block20
import SourceMomentWordsV1.Block21
import SourceMomentWordsV1.Block22
import SourceMomentWordsV1.Block23
import SourceMomentWordsV1.Block24
import SourceMomentWordsV1.Block25
import SourceMomentWordsV1.Block26
import SourceMomentWordsV1.Block27
import SourceMomentWordsV1.Block28
import SourceMomentWordsV1.Block29
import SourceMomentWordsV1.Block30
import SourceMomentWordsV1.Block31
import SourceMomentWordsV1.Block32
import SourceMomentWordsV1.Block33
import SourceMomentWordsV1.Block34
import SourceMomentWordsV1.Block35
import SourceMomentWordsV1.Block36
import SourceMomentWordsV1.Block37
import SourceMomentWordsV1.Block38
import SourceMomentWordsV1.Block39
import SourceMomentWordsV1.Block40
import SourceMomentWordsV1.Block41
import SourceMomentWordsV1.Block42
import SourceMomentWordsV1.Block43
import SourceMomentWordsV1.Block44
import SourceMomentWordsV1.Block45
import SourceMomentWordsV1.Block46
import SourceMomentWordsV1.Block47
import SourceMomentWordsV1.Block48
import SourceMomentWordsV1.Block49
import SourceMomentWordsV1.Block50
import SourceMomentWordsV1.Block51
import SourceMomentWordsV1.Block52
import SourceMomentWordsV1.Block53
import SourceMomentWordsV1.Block54
import SourceMomentWordsV1.Block55
import SourceMomentWordsV1.Block56
import SourceMomentWordsV1.Block57
import SourceMomentWordsV1.Block58
import SourceMomentWordsV1.Block59
import SourceMomentWordsV1.Block60
import SourceMomentWordsV1.Block61
import SourceMomentWordsV1.Block62
import SourceMomentWordsV1.Block63
import SourceMomentWordsV1.Block64
import SourceMomentWordsV1.Block65
import SourceMomentWordsV1.Block66
import SourceMomentWordsV1.Block67
import SourceMomentWordsV1.Block68
import SourceMomentWordsV1.Block69
import SourceMomentWordsV1.Block70
import SourceMomentWordsV1.Block71
import SourceMomentWordsV1.Block72
import SourceMomentWordsV1.Block73
import SourceMomentWordsV1.Block74
import SourceMomentWordsV1.Block75
import SourceMomentWordsV1.Block76
import SourceMomentWordsV1.Block77
import SourceMomentWordsV1.Block78
import SourceMomentWordsV1.Block79
import SourceMomentWordsV1.Block80
import SourceMomentWordsV1.Block81
import SourceMomentWordsV1.Block82
import SourceMomentWordsV1.Block83
import SourceMomentWordsV1.Block84
import SourceMomentWordsV1.Block85
import SourceMomentWordsV1.Block86
import SourceMomentWordsV1.Block87
import SourceMomentWordsV1.Block88
import SourceMomentWordsV1.Block89
import SourceMomentWordsV1.Block90
import SourceMomentWordsV1.Block91
import SourceMomentWordsV1.Block92
import SourceMomentWordsV1.Block93
import SourceMomentWordsV1.Block94
import SourceMomentWordsV1.Block95
namespace SourceMomentWordsV1.All
open ScopedNumerical SynergyMomentMath.WordModel
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
def actual : List (ProofBox × ProofBox) :=
  (Block00.actual++(Block01.actual++(Block02.actual++(Block03.actual++(Block04.actual++(Block05.actual++(Block06.actual++(Block07.actual++(Block08.actual++(Block09.actual++(Block10.actual++(Block11.actual++(Block12.actual++(Block13.actual++(Block14.actual++(Block15.actual++(Block16.actual++(Block17.actual++(Block18.actual++(Block19.actual++(Block20.actual++(Block21.actual++(Block22.actual++(Block23.actual++(Block24.actual++(Block25.actual++(Block26.actual++(Block27.actual++(Block28.actual++(Block29.actual++(Block30.actual++(Block31.actual++(Block32.actual++(Block33.actual++(Block34.actual++(Block35.actual++(Block36.actual++(Block37.actual++(Block38.actual++(Block39.actual++(Block40.actual++(Block41.actual++(Block42.actual++(Block43.actual++(Block44.actual++(Block45.actual++(Block46.actual++(Block47.actual++(Block48.actual++(Block49.actual++(Block50.actual++(Block51.actual++(Block52.actual++(Block53.actual++(Block54.actual++(Block55.actual++(Block56.actual++(Block57.actual++(Block58.actual++(Block59.actual++(Block60.actual++(Block61.actual++(Block62.actual++(Block63.actual++(Block64.actual++(Block65.actual++(Block66.actual++(Block67.actual++(Block68.actual++(Block69.actual++(Block70.actual++(Block71.actual++(Block72.actual++(Block73.actual++(Block74.actual++(Block75.actual++(Block76.actual++(Block77.actual++(Block78.actual++(Block79.actual++(Block80.actual++(Block81.actual++(Block82.actual++(Block83.actual++(Block84.actual++(Block85.actual++(Block86.actual++(Block87.actual++(Block88.actual++(Block89.actual++(Block90.actual++(Block91.actual++(Block92.actual++(Block93.actual++(Block94.actual++Block95.actual)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def words : List (Int × Int) :=
  (Block00.words++(Block01.words++(Block02.words++(Block03.words++(Block04.words++(Block05.words++(Block06.words++(Block07.words++(Block08.words++(Block09.words++(Block10.words++(Block11.words++(Block12.words++(Block13.words++(Block14.words++(Block15.words++(Block16.words++(Block17.words++(Block18.words++(Block19.words++(Block20.words++(Block21.words++(Block22.words++(Block23.words++(Block24.words++(Block25.words++(Block26.words++(Block27.words++(Block28.words++(Block29.words++(Block30.words++(Block31.words++(Block32.words++(Block33.words++(Block34.words++(Block35.words++(Block36.words++(Block37.words++(Block38.words++(Block39.words++(Block40.words++(Block41.words++(Block42.words++(Block43.words++(Block44.words++(Block45.words++(Block46.words++(Block47.words++(Block48.words++(Block49.words++(Block50.words++(Block51.words++(Block52.words++(Block53.words++(Block54.words++(Block55.words++(Block56.words++(Block57.words++(Block58.words++(Block59.words++(Block60.words++(Block61.words++(Block62.words++(Block63.words++(Block64.words++(Block65.words++(Block66.words++(Block67.words++(Block68.words++(Block69.words++(Block70.words++(Block71.words++(Block72.words++(Block73.words++(Block74.words++(Block75.words++(Block76.words++(Block77.words++(Block78.words++(Block79.words++(Block80.words++(Block81.words++(Block82.words++(Block83.words++(Block84.words++(Block85.words++(Block86.words++(Block87.words++(Block88.words++(Block89.words++(Block90.words++(Block91.words++(Block92.words++(Block93.words++(Block94.words++Block95.words)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
private theorem append_checked {a b : List (ProofBox × ProofBox)}
    {x y : List (Int × Int)} (hl : a.length=x.length)
    (ha : (a.zip x).all (fun z=>decide (highPair z.1=z.2))=true)
    (hb : (b.zip y).all (fun z=>decide (highPair z.1=z.2))=true) :
    ((a++b).zip (x++y)).all (fun z=>decide (highPair z.1=z.2))=true := by
  rw [List.zip_append hl,List.all_append,ha,hb]
  rfl
theorem checked : (actual.zip words).all (fun z=>decide (highPair z.1=z.2))=true :=
  (append_checked (by rfl) Block00.checked (append_checked (by rfl) Block01.checked (append_checked (by rfl) Block02.checked (append_checked (by rfl) Block03.checked (append_checked (by rfl) Block04.checked (append_checked (by rfl) Block05.checked (append_checked (by rfl) Block06.checked (append_checked (by rfl) Block07.checked (append_checked (by rfl) Block08.checked (append_checked (by rfl) Block09.checked (append_checked (by rfl) Block10.checked (append_checked (by rfl) Block11.checked (append_checked (by rfl) Block12.checked (append_checked (by rfl) Block13.checked (append_checked (by rfl) Block14.checked (append_checked (by rfl) Block15.checked (append_checked (by rfl) Block16.checked (append_checked (by rfl) Block17.checked (append_checked (by rfl) Block18.checked (append_checked (by rfl) Block19.checked (append_checked (by rfl) Block20.checked (append_checked (by rfl) Block21.checked (append_checked (by rfl) Block22.checked (append_checked (by rfl) Block23.checked (append_checked (by rfl) Block24.checked (append_checked (by rfl) Block25.checked (append_checked (by rfl) Block26.checked (append_checked (by rfl) Block27.checked (append_checked (by rfl) Block28.checked (append_checked (by rfl) Block29.checked (append_checked (by rfl) Block30.checked (append_checked (by rfl) Block31.checked (append_checked (by rfl) Block32.checked (append_checked (by rfl) Block33.checked (append_checked (by rfl) Block34.checked (append_checked (by rfl) Block35.checked (append_checked (by rfl) Block36.checked (append_checked (by rfl) Block37.checked (append_checked (by rfl) Block38.checked (append_checked (by rfl) Block39.checked (append_checked (by rfl) Block40.checked (append_checked (by rfl) Block41.checked (append_checked (by rfl) Block42.checked (append_checked (by rfl) Block43.checked (append_checked (by rfl) Block44.checked (append_checked (by rfl) Block45.checked (append_checked (by rfl) Block46.checked (append_checked (by rfl) Block47.checked (append_checked (by rfl) Block48.checked (append_checked (by rfl) Block49.checked (append_checked (by rfl) Block50.checked (append_checked (by rfl) Block51.checked (append_checked (by rfl) Block52.checked (append_checked (by rfl) Block53.checked (append_checked (by rfl) Block54.checked (append_checked (by rfl) Block55.checked (append_checked (by rfl) Block56.checked (append_checked (by rfl) Block57.checked (append_checked (by rfl) Block58.checked (append_checked (by rfl) Block59.checked (append_checked (by rfl) Block60.checked (append_checked (by rfl) Block61.checked (append_checked (by rfl) Block62.checked (append_checked (by rfl) Block63.checked (append_checked (by rfl) Block64.checked (append_checked (by rfl) Block65.checked (append_checked (by rfl) Block66.checked (append_checked (by rfl) Block67.checked (append_checked (by rfl) Block68.checked (append_checked (by rfl) Block69.checked (append_checked (by rfl) Block70.checked (append_checked (by rfl) Block71.checked (append_checked (by rfl) Block72.checked (append_checked (by rfl) Block73.checked (append_checked (by rfl) Block74.checked (append_checked (by rfl) Block75.checked (append_checked (by rfl) Block76.checked (append_checked (by rfl) Block77.checked (append_checked (by rfl) Block78.checked (append_checked (by rfl) Block79.checked (append_checked (by rfl) Block80.checked (append_checked (by rfl) Block81.checked (append_checked (by rfl) Block82.checked (append_checked (by rfl) Block83.checked (append_checked (by rfl) Block84.checked (append_checked (by rfl) Block85.checked (append_checked (by rfl) Block86.checked (append_checked (by rfl) Block87.checked (append_checked (by rfl) Block88.checked (append_checked (by rfl) Block89.checked (append_checked (by rfl) Block90.checked (append_checked (by rfl) Block91.checked (append_checked (by rfl) Block92.checked (append_checked (by rfl) Block93.checked (append_checked (by rfl) Block94.checked Block95.checked)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem actual_eq : actual=(List.range 768).map outputs := by rfl
theorem word_count : words.length=768 := by rfl
def word (i : Nat) : Int × Int := words[i]?.getD (0,0)
theorem word_get (i : Nat) (hi : i < 768) : words[i]?=some (word i) := by
  have h : i < words.length := by rw [word_count]; exact hi
  have read : words[i]?=some words[i] := List.getElem?_eq_getElem h
  simp only [word,read,Option.getD_some]
theorem all_words (i : Nat) (hi : i < 768) : highPair (outputs i)=word i := by
  apply from_all actual words checked
  apply List.mem_iff_getElem?.mpr
  refine ⟨i,List.getElem?_zip_eq_some.mpr ⟨?_,word_get i hi⟩⟩
  rw [actual_eq,List.getElem?_map,List.getElem?_range hi]
  rfl
#print axioms checked
#print axioms actual_eq
#print axioms word_count
#print axioms word_get
#print axioms all_words
end SourceMomentWordsV1.All

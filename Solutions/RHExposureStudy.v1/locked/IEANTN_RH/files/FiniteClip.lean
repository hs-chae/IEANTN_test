import FullRH
import RamanujanPV.FullFiniteScalars
import RamanujanPV.PrimeBaseCombinedResult

open Real IEANTN RamanujanPV
namespace FiniteClip

/-- All existing strict scalar data can be retained. Only directed count
bounds are required; exact counts are not part of this new consumer contract. -/
theorem one_sided_cell (c : Cell) (hc : c.FixedPredicate) (he : c.Enclosures)
    (hP : Nat.primeCounting c.m ≤ c.P) (hQ : c.Q ≤ Nat.primeCounting c.j)
    {x : ℝ} (hx : (c.n:ℝ) ≤ x) (hu : x < (c.m:ℝ)+1) : Holds x := by
  let d : Cell := {c with P := Nat.primeCounting c.m, Q := Nat.primeCounting c.j}
  have hp : d.FixedPredicate := by
    have hs : (Nat.primeCounting c.m)^2 ≤ c.P^2 := Nat.pow_le_pow_left hP 2
    have hL := Nat.mul_le_mul_right c.logHigh hs
    have hR := Nat.mul_le_mul_left (c.eLow*c.n) hQ
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hL.trans_lt (hc.2.2.2.trans_le hR)⟩
  exact fixed_cell_sound d hp ⟨rfl,rfl⟩ he hx hu

theorem clipped (hRH : SharedRH.hypothesis)
    {start stop cut : ℕ} {rows : List RawFactoredCell}
    (sc : FullFiniteScalars.ScalarCertificate start stop rows)
    (hcut : cut ≤ stop)
    (directed : ∀ r ∈ rows, r.n < cut →
        Nat.primeCounting (r.next-1) ≤ r.P ∧ r.Q ≤ Nat.primeCounting r.j)
    (ray : SharedRH.hypothesis → ∀ x : ℝ, (cut:ℝ) ≤ x → Holds x) :
    ∀ x : ℝ, (start:ℝ) ≤ x → Holds x := by
  intro x hx
  by_cases hc : (cut:ℝ) ≤ x
  · exact ray hRH x hc
  have hh : x < (stop:ℝ) := (lt_of_not_ge hc).trans_le (by exact_mod_cast hcut)
  have chain := sc.1.toCellChain WindowCells.eLo WindowCells.eHi
  obtain ⟨c,hc',hn,hm⟩ := chain.covers hx hh
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc'
  have hnr : (r.n:ℝ) ≤ x := hn
  have hnc : r.n < cut := by exact_mod_cast hnr.trans_lt (lt_of_not_ge hc)
  have hp := directed r hr hnc
  exact one_sided_cell _ (sc.2 r hr).1 (sc.2 r hr).2 hp.1 hp.2 hn hm

#print axioms one_sided_cell
#print axioms clipped
end FiniteClip

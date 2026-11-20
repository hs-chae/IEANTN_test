/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellInverse
import RamanujanPV.FiniteProgramMillion

/-! Stronger selected consumer: only the C argument word bounds are checked
separately. Every remaining source-domain guard, including the log response and
A=floor(n*eLo/Lu), is derived from the actual C positive execution. No DomainFinal
certificate is used on this theorem's actual proof path. -/
namespace RamanujanPV.FiniteGuardedMillion
open WindowCells QuotientDemandCheck FiniteProgramCells
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def checkWords (r : RawFactoredCell) : Bool := decide
  (r.n<2^64 ∧r.next<2^64 ∧r.j<2^64 ∧r.P<2^64 ∧r.Q<2^64 ∧r.Lu<2^64 ∧r.A<2^64)

theorem word_fits {r : RawFactoredCell} (checked : checkWords r=true) : FiniteCellProtected.WordFits r := by
  have h : r.n<2^64 ∧r.next<2^64 ∧r.j<2^64 ∧r.P<2^64 ∧r.Q<2^64 ∧r.Lu<2^64 ∧r.A<2^64 :=
    of_decide_eq_true checked
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem all_words_checked : allFrom (fun i=>checkWords (LocalCellsMillion.rows.get i)) 0 285=true := by
  decide +kernel

theorem all_word_fits (i : Nat) (hi : i<285) : FiniteCellProtected.WordFits (LocalCellsMillion.rows.get i) :=
  word_fits (allFrom_at 285 0 all_words_checked i (by omega) (by omega))

/-- Every non-strict source guard is a CONCLUSION of that original row's C run. -/
theorem derived_domains : Domains LocalCellsMillion.rows 285 := by
  intro i hi
  obtain ⟨state,actual⟩:=(FiniteScalarMillion.all_cell_source i hi).actual
  exact (FiniteCellInverse.positive_domain (all_word_fits i hi) actual).1

theorem source_fixed (i : Nat) (hi : i<285) :
    ((LocalCellsMillion.rows.get i).toCell eLo eHi).FixedPredicate :=
  FiniteCellInverse.positive_fixed (all_word_fits i hi) (FiniteScalarMillion.all_cell_source i hi)

theorem complete_certificate : CompleteCertificate 38358837683 38359837684
    ((rawList LocalCellsMillion.rows LocalCellsMillion.rowCount).map (fun r=>r.toCell eLo eHi)) :=
  FiniteProgramCells.complete_certificate SegmentRamanujanMillion.p_provider
    SegmentRamanujanMillion.q_provider FiniteProgramMillion.layout_checked derived_domains
    FiniteScalarMillion.all_cell_source FiniteScalarMillion.all_log_source

theorem first_1000001_real_interval {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : Holds x :=
  complete_certificate_sound complete_certificate x lower upper

theorem uniform_gap {x : ℝ}
    (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) : (501901:ℝ)<gap x := by
  apply CertificateMargin.array_certificate complete_certificate _
    SegmentSourceMargins.million_margins_checked x lower upper
  intro i hi
  exact FinitePredicateBounds.floor_relation (derived_domains i hi).aFloor

#print axioms all_words_checked
#print axioms derived_domains
#print axioms source_fixed
#print axioms complete_certificate
#print axioms first_1000001_real_interval
#print axioms uniform_gap
end RamanujanPV.FiniteGuardedMillion

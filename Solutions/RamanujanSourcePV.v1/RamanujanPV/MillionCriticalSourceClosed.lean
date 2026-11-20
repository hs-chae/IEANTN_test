/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CriticalSourceClosed
import RamanujanPV.LocalCellsMillion.Final
import RamanujanPV.WindowMargin

/-! One million classified successor integers extend the same two complete
source executions to a real interval of width1,000,001. The generated local
prime certificates, cumulative classifiers, all285 rows and their final typed
audits must actually compile before this module can be accepted. -/
namespace RamanujanPV.MillionCriticalSourceClosed
open QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 0

theorem finite_certificate :
    CompleteCertificate 38358837683 38359837684
      ((WindowCells.rawList LocalCellsMillion.rows 285).map
        (fun r=>r.toCell WindowCells.eLo WindowCells.eHi)) :=
  LocalCellsMillion.conditional_certificate CriticalSourceClosed.p_source CriticalSourceClosed.q_source

theorem real_interval {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxStop : x < 38359837684) : Holds x :=
  complete_certificate_sound finite_certificate x hx hxStop

theorem margins_checked :
    allFrom (WindowMargin.check LocalCellsMillion.rows 501901) 0 285=true := by
  decide +kernel

/-- A strict uniform quantitative bound survives EVERY checked real cell. -/
theorem uniform_gap {x : ℝ}
    (hx : (38358837683:ℝ) ≤ x) (hxStop : x < 38359837684) :
    (501901:ℝ) < gap x :=
  WindowMargin.quantitative_window CriticalSourceClosed.p_source CriticalSourceClosed.q_source
    (LocalPrimeTree.bounded_prime_provider LocalWindowMillion.primes_good LocalWindowMillion.primeCount)
    LocalWindowMillion.p_checked LocalWindowMillion.q_checked LocalCellsMillion.checked margins_checked x hx hxStop

/-- Local source executions recover new exact large counts without another
multi-million-node quotient certificate for each new argument. -/
theorem p_endpoint_count : Nat.primeCounting 38359837683=1644714148 := by
  have h := LocalWindowMillion.p_increment 999999 (by decide)
  have last : (LocalWindowMillion.pEntries.get 999999).cumulative=40916 := by decide +kernel
  rw [last,DemandCriticalPair.pi_38358837683] at h
  exact h

theorem q_endpoint_count : Nat.primeCounting 14111795650=632223009 := by
  have h := LocalWindowMillion.q_increment 367879 (by decide)
  have last : (LocalWindowMillion.qEntries.get 367879).cumulative=15972 := by decide +kernel
  rw [last,DemandCriticalPair.pi_14111427770] at h
  exact h

theorem p_endpoint_source : QuotientCCell.SourceExecution 38359837683 1644714148 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num) p_endpoint_count

theorem q_endpoint_source : QuotientCCell.SourceExecution 14111795650 632223009 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num) q_endpoint_count

#print axioms finite_certificate
#print axioms real_interval
#print axioms margins_checked
#print axioms uniform_gap
#print axioms p_endpoint_count
#print axioms q_endpoint_count
#print axioms p_endpoint_source
#print axioms q_endpoint_source
end RamanujanPV.MillionCriticalSourceClosed

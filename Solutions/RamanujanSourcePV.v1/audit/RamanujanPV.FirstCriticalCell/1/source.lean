/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCCell
import RamanujanPV.AnalyticTransition

/-! The actual first critical finite interval, width56 above N0=38358837683.
Its scaled predicate, e/log enclosures and all55 composite steps are proved here.
The TWO large concrete numerical source executions remain explicit inputs until
their separate kernel numerical closures are completed. No particular count is
accepted by a bare hardcoded literal. Auxiliary proper-divisor checking is an
ordinary kernel certificate proof, not source-first PV by itself. -/
namespace RamanujanPV.FirstCriticalCell
open Finset
open AnalyticTransition QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 2000000

def N0 : Nat := 38358837683
def J0 : Nat := 14111427770
def P0 : Nat := 1644673232
def Q0 : Nat := 632207037
def eLo : Nat := 3133965575612453533
def eHi : Nat := eLo+22

def raw : RawFactoredCell where
  n := N0
  next := 38358837739
  j := J0
  P := P0
  Q := Q0
  Lu := 26795374111319
  A := 4486419048288114

def cell : Cell := raw.toCell eLo eHi

def properFactors : List Nat :=
  [2,5,2,3,2,17,2,31,2,3,2,5,2,709,2,3,2,47,2,1231,2,3,2,797,2,20177,2,3,
   2,7,2,5,2,3,2,23,2,32887,2,3,2,5,2,7,2,3,2,239,2,113,2,3,2,11,2]

/-- All55 supplied divisors are checked against the actual critical integers.
The result is a kernel-checked ordinary certificate, not a native computation. -/
theorem proper_factors_checked : ∀ k : Fin 55,
    2 ≤ properFactors[k.val]! ∧ properFactors[k.val]! < N0+k.val+1 ∧
      (N0+k.val+1)%properFactors[k.val]!=0 := by
  decide +kernel

theorem plateau_composite (k : Fin 55) : ¬Nat.Prime (N0+k.val+1) := by
  obtain ⟨h2,hlt,hmod⟩ := proper_factors_checked k
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) h2 hlt

/-- The exact55 composite integers imply π(N0+55)=π(N0), without enumerating
all integers up to the large endpoint. -/
theorem plateau_count : Nat.primeCounting (N0+55)=Nat.primeCounting N0 := by
  have sets : Nat.primesLE (N0+55)=Nat.primesLE N0 := by
    ext m
    rw [Nat.mem_primesLE,Nat.mem_primesLE]
    constructor
    · intro hm
      refine ⟨?_,hm.2⟩
      by_contra bad
      let k : Fin 55 := ⟨m-N0-1,by omega⟩
      have eq : N0+k.val+1=m := by dsimp [k]; omega
      exact plateau_composite k (eq.symm ▸ hm.2)
    · intro hm
      exact ⟨by omega,hm.2⟩
  rw [←Nat.primesLE_card_eq_primeCounting,←Nat.primesLE_card_eq_primeCounting,sets]

/-- Actual integer output of the twenty-term binary-normalized log algorithm.
The source-to-AST and word implementation for that log routine remains separate. -/
theorem actual_log_value : binaryLogUpper N0 (2^35) 35=26795374111319 := by
  decide +kernel

theorem fixed_predicate : cell.FixedPredicate := by
  apply RawFactoredCell.toCell_fixedPredicate
  all_goals norm_num [raw,N0,J0,P0,Q0,eLo,eHi]

/-- Full real enclosures, with actual e and actual log(N0), no assumed numerical
bound or endpoint positivity. The algorithms are analyzed by existing kernel proofs. -/
theorem real_enclosures : cell.Enclosures := by
  have he := finite_e_enclosure
  rw [finiteELow_value] at he
  have helo : (eLo:ℝ) ≤ Real.exp 1*(2:ℝ)^60 := by
    exact (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^60)).mp he.1
  have hehi : Real.exp 1*(2:ℝ)^60 ≤ (eHi:ℝ) := by
    exact (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^60)).mp he.2
  have hlog := binaryLogUpper_sound (n:=N0) (two:=2^35) (k:=35) rfl
    (by norm_num [N0]) (by norm_num [N0])
  rw [actual_log_value] at hlog
  have hlogScaled : Real.log (N0:ℝ)*(2:ℝ)^40 ≤ 26795374111319 :=
    (le_div_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^40)).mp hlog
  have hexp : Real.exp 1 ≤ (N0:ℝ) := by
    have h := Real.exp_one_lt_d9
    norm_num [N0]
    linarith
  exact RawFactoredCell.toCell_enclosures raw eLo eHi hexp helo hehi hlogScaled

/-- TWO source-linked numerical executions suffice for the actual critical
cell: the plateau replaces55 redundant source-count invocations. -/
theorem counts_from_source (runP : SourceExecution N0 P0) (runQ : SourceExecution J0 Q0) :
    cell.CountsCorrect := by
  have hP := source_execution_count runP
  have hQ := source_execution_count runQ
  constructor
  · change Nat.primeCounting (38358837739-1)=P0
    have hm : (38358837739-1:Nat)=N0+55 := by norm_num [N0]
    rw [hm,plateau_count,hP]
  · exact hQ

/-- Conditional only on the two explicitly pending, large source-linked count
executions. Everything else for every REAL x in this width56 interval is proved.
This theorem does not state that those concrete executions are already accepted. -/
theorem conditional_first_critical_interval
    (runP : SourceExecution N0 P0) (runQ : SourceExecution J0 Q0)
    {x : ℝ} (hx : (38358837683:ℝ) ≤ x) (hxNext : x < 38358837739) : Holds x := by
  apply fixed_cell_sound cell fixed_predicate (counts_from_source runP runQ) real_enclosures
  · exact hx
  · convert! hxNext using 1 <;> norm_num [cell,raw,RawFactoredCell.toCell]

#print axioms proper_factors_checked
#print axioms plateau_count
#print axioms actual_log_value
#print axioms fixed_predicate
#print axioms real_enclosures
#print axioms conditional_first_critical_interval
end RamanujanPV.FirstCriticalCell

/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.WindowCells
import RamanujanPV.RecoveredMargin

/-! Quantitative recovery from the same checked adaptive rows and source counts.
No new prime count, analytic estimate, or desired gap premise is introduced. -/
namespace RamanujanPV.WindowMargin
open WindowCells QuotientDemandCheck QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def check (rows : Lean.RArray RawFactoredCell) (D i : Nat) : Bool :=
  let r:=rows.get i
  decide (2^20*(r.P^2+D) < r.A*r.Q)

lemma row_gap {pBase qBase pCount qCount pValue qValue primeCount D : Nat}
    {primes : Lean.RArray Nat} {pEntries qEntries : Lean.RArray PrimeWindow.Entry}
    {r : RawFactoredCell} {x : ℝ}
    (pRun : SourceExecution pBase pValue) (qRun : SourceExecution qBase qValue)
    (good : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (pChecked : PrimeWindow.checkAll pBase primes primeCount pEntries pCount=true)
    (qChecked : PrimeWindow.checkAll qBase primes primeCount qEntries qCount=true)
    (spec : RowSpec pBase qBase pCount qCount pValue qValue pEntries qEntries r)
    (margin : 2^20*(r.P^2+D) < r.A*r.Q)
    (hnx : (r.n:ℝ) ≤ x) (hxm : x < (r.next-1:Nat)+1) : (D:ℝ) < gap x := by
  have counts := row_counts pRun qRun good pChecked qChecked spec
  obtain ⟨hn,heLo,heHi,hlogUnused⟩ := row_real_enclosures spec
  simp only [RawFactoredCell.toCell,Nat.cast_pow,Nat.cast_ofNat] at hn heLo heHi
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,strict,lo,hi,logval,m2,mhi,j2,jhi⟩ := spec
  have logBound := AnalyticTransition.binaryLogUpper_sound (n:=r.n) (two:=2^35) (k:=35) rfl lo hi
  rw [←logval] at logBound
  have hlog : Real.log (r.n:ℝ)*(2:ℝ)^40 ≤ (r.Lu:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^40)).mp logBound
  apply RecoveredMargin.factored_gap_lower hn
    (source_execution_count counts.1) (source_execution_count counts.2)
    heLo heHi hlog je ac _ hnx hxm
  exact_mod_cast margin

/-- Every real point receives the independently checked strict uniform margin.
The interval chain and prime counts are exactly those of CompleteCertificate. -/
theorem quantitative_window {pBase qBase pCount qCount pValue qValue stop count primeCount D : Nat}
    {primes : Lean.RArray Nat} {pEntries qEntries : Lean.RArray PrimeWindow.Entry}
    {rows : Lean.RArray RawFactoredCell}
    (pRun : SourceExecution pBase pValue) (qRun : SourceExecution qBase qValue)
    (good : ∀ j, j < primeCount → Nat.Prime (primes.get j))
    (pChecked : PrimeWindow.checkAll pBase primes primeCount pEntries pCount=true)
    (qChecked : PrimeWindow.checkAll qBase primes primeCount qEntries qCount=true)
    (checked : checkRows pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows=true)
    (margins : allFrom (check rows D) 0 count=true) :
    ∀ x : ℝ, (pBase:ℝ) ≤ x → x < (stop:ℝ) → (D:ℝ) < gap x := by
  intro x hx hs
  have cert := WindowCells.complete_certificate pRun qRun good pChecked qChecked checked
  obtain ⟨c,hc,hn,hm⟩ := cert.1.covers hx hs
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
  change r ∈ (List.range count).map rows.get at hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  have bound : i < count := List.mem_range.mp hi
  have parts : 0 < count ∧
      allFrom (checkRow pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count=true := by
    simpa [checkRows] using checked
  have spec := (checkRow_clauses (allFrom_at count 0 parts.2 i (by omega) (by omega))).1
  have num := allFrom_at count 0 margins i (by omega) (by omega)
  have margin : 2^20*((rows.get i).P^2+D) < (rows.get i).A*(rows.get i).Q := by
    exact of_decide_eq_true num
  apply row_gap pRun qRun good pChecked qChecked spec margin
  · exact hn
  · simpa only [RawFactoredCell.toCell,Nat.cast_add,Nat.cast_one] using hm

#print axioms row_gap
#print axioms quantitative_window
end RamanujanPV.WindowMargin

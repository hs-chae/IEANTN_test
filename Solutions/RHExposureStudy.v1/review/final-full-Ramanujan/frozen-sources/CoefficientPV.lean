import RamanujanPV.FiniteScalarEval

namespace CoefficientPV
open LCMSourcePV.Witness.C
open RamanujanPV RamanujanPV.FiniteScalarMachine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def d (v : String) (e : Expr) : Stmt := .declare [⟨"uint64_t",v,some e⟩]
def a (v : String) (e : Expr) : Stmt := .eval (.binary "=" (.var v) e)
def fn : Function := ⟨"uint64_t","rh_coeff",[("uint64_t","n")],
  .sequence [
    d "lhs" (.nat 1), d "f" (.nat 1),
    .forLoop (d "j" (.nat 1)) (some (.binary "<=" (.var "j") (.var "n")))
      (.unary "++" (.var "j")) (.sequence [
        a "lhs" (.binary "+" (.binary "*" (.var "j") (.var "lhs")) (.nat 1)),
        a "f" (.binary "*" (.var "f") (.var "j"))]),
    d "rhs" (.var "f"), d "a" (.nat 1), d "b" (.var "f"),
    .forLoop (d "i" (.nat 1)) (some (.binary "<=" (.var "i") (.var "n")))
      (.unary "++" (.var "i")) (.sequence [
        a "a" (.binary "*" (.var "a") (.var "i")),
        a "b" (.binary "/" (.var "b") (.binary "-" (.binary "+" (.var "n") (.nat 1)) (.var "i"))),
        a "rhs" (.binary "+" (.var "rhs") (.binary "*" (.var "a") (.var "b")))]),
    .returnStmt (.binary "-" (.var "lhs") (.var "rhs"))]⟩
def render (_ : Unit) : Option String := do
  return "#include <stdint.h>\n\n" ++ (← renderFunctions [fn])
def actual : String := include_str "rh_coeff.c"

theorem source : LCMSourcePV.RestrictedC.SourceCorresponds render actual () := by
  refine ⟨(render ()).getD "", ?_, ?_, ?_⟩ <;> decide +kernel

def noneP : Prototypes := fun _ ↦ none
def noneC : Service := fun _ _ ↦ none
def start (j : ℕ) : State := ⟨bind empty.env "n" (word64 j)⟩
def lhs (j : ℕ) : ℕ := ∑ i ∈ Finset.range (j+1), i.factorial * j.choose i
def rhs (j : ℕ) : ℕ := ∑ i ∈ Finset.range (j+1), i.factorial * (j-i).factorial
def coeff (j : ℕ) : ℕ := lhs j - rhs j

theorem numerical (j : Fin 21) :
    FiniteScalarEval.returnedValue noneP noneC 150 fn.body (start j) =
      some (word64 (coeff j)) := by
  revert j
  decide +kernel

theorem order (j : Fin 21) : rhs j ≤ lhs j := by
  revert j
  decide +kernel

theorem source_runs (j : Fin 21) :
    ∃ t, Run noneP noneC fn.body (start j) (.returned t (word64 (coeff j))) :=
  FiniteScalarEval.returned_value_sound (numerical j)

theorem returned_coefficient {j : Fin 21} {t : State} {v : Value}
    (h : Run noneP noneC fn.body (start j) (.returned t v)) :
    (v.number : ℝ) = (lhs j : ℝ) - (rhs j : ℝ) := by
  obtain ⟨t', ht'⟩ := source_runs j
  have same : v = word64 (coeff j) := by
    -- determinism of the reused execution relation
    have hh := run_unique h ht'
    exact (LCMSourcePV.ASTLoops.Flow.returned.inj hh).2
  rw [same]
  change (↑(lhs j - rhs j) : ℝ) = _
  exact Nat.cast_sub (order j)

def firstCoeffs : List ℕ := [0,0,0,0,1,14,145,1412]

theorem prefix_values (j : Fin 8) :
    coeff j = firstCoeffs[j.val]! := by
  revert j
  decide +kernel

/-- Arithmetic consumer: the semantic results mathematically imply a bound
on the entire degree-20 polynomial, not just on the executable's output. -/
theorem poly_lower (u : ℝ) (hu : 0 ≤ u) :
    u^4 + 14*u^5 + 145*u^6 + 1412*u^7 ≤
      ∑ j ∈ Finset.range 21, ((lhs j : ℝ) - (rhs j : ℝ)) * u^j := by
  have h (j : ℕ) (hj : j < 21) : (coeff j : ℝ) = (lhs j : ℝ)-(rhs j : ℝ) := by
    obtain ⟨t,ht⟩ := source_runs ⟨j,hj⟩
    exact returned_coefficient ht
  have hh : ∑ j ∈ Finset.range 21, ((lhs j : ℝ)-(rhs j : ℝ))*u^j =
      ∑ j ∈ Finset.range 21, (coeff j : ℝ)*u^j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j (Finset.mem_range.mp hj)]
  rw [hh]
  have hsplit : ∑ j ∈ Finset.range 8, (coeff j : ℝ)*u^j ≤
      ∑ j ∈ Finset.range 21, (coeff j : ℝ)*u^j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset.mpr (by norm_num; omega))
    intro j hj ht
    positivity
  convert hsplit using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have e0 : coeff 0 = 0 := by decide +kernel
  have e1 : coeff 1 = 0 := by decide +kernel
  have e2 : coeff 2 = 0 := by decide +kernel
  have e3 : coeff 3 = 0 := by decide +kernel
  have e4 : coeff 4 = 1 := by decide +kernel
  have e5 : coeff 5 = 14 := by decide +kernel
  have e6 : coeff 6 = 145 := by decide +kernel
  have e7 : coeff 7 = 1412 := by decide +kernel
  rw [e0,e1,e2,e3,e4,e5,e6,e7]
  push_cast
  ring

theorem source_and_poly (u : ℝ) (hu : 0 ≤ u) :
    LCMSourcePV.RestrictedC.SourceCorresponds render actual () ∧
    u^4+14*u^5+145*u^6+1412*u^7 ≤
      ∑ j ∈ Finset.range 21, ((lhs j : ℝ)-(rhs j : ℝ))*u^j :=
  ⟨source, poly_lower u hu⟩

#print axioms source
#print axioms numerical
#print axioms source_and_poly
end CoefficientPV

import CounterRendererSound
import HighDriverSource

/-! Independent syntax binding for the unchanged counter and high-input driver.
All finite profile checks are kernel checked. Existing exact-byte theorems are
reused; the general acceptance theorem, rather than token equality, supplies the
independent source-to-AST grammar derivation. -/
namespace RHOcticPush.CounterSyntax
open LCMSourcePV.Witness.C
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- This checks the actual AST, not an expected numerical execution result. -/
theorem actual_counter_profile :
    RamanujanPV.QuotientCSourceV2.functions.all functionGuard = true := by decide +kernel

theorem actual_driver_profile : driverGuard HighDriverSource.program = true := by decide +kernel

theorem actual_counter_render : counterRender RamanujanPV.QuotientCSourceV2.functions =
    some RamanujanPV.QuotientCSourceV2.actualSource :=
  RamanujanPV.QuotientCSourceV2.actual_source_bytes

theorem actual_counter_accepted : checkedCounter RamanujanPV.QuotientCSourceV2.actualSource
    RamanujanPV.QuotientCSourceV2.functions = true := by
  simp only [checkedCounter,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨by decide +kernel,actual_counter_profile⟩,actual_counter_render⟩

theorem actual_driver_accepted :
    checkedDriver HighDriverSource.actualSource HighDriverSource.program = true := by
  simp only [checkedDriver,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨actual_driver_profile,HighDriverSource.actual_source_bytes⟩

/-- This final actual-source fact genuinely consumes general checker soundness. -/
theorem actual_counter_syntax : CounterProgram RamanujanPV.QuotientCSourceV2.actualSource
    RamanujanPV.QuotientCSourceV2.functions := checkedCounter_sound actual_counter_accepted

theorem actual_driver_syntax : DriverProgram HighDriverSource.actualSource
    HighDriverSource.program := checkedDriver_sound actual_driver_accepted

/-- Arbitrary invalid operator and identifier strings used to be printable.
They cannot enter the guarded fragment. Tests supplement the general proof. -/
theorem mutation_bad_operator :
    expressionGuard 1000 (.binary ";return 7;" (.nat 1) (.nat 2)) = false := by decide +kernel

theorem mutation_bad_identifier :
    expressionGuard 1000 (.var "x);return 7;/*") = false := by decide +kernel

theorem mutation_bad_type : declarationGuard ⟨"uint64_t);return 7;(","n",none⟩ = false :=
  by decide +kernel

theorem mutation_non_lvalue :
    expressionGuard 1000 (.unary "++" (.nat 1)) = false := by decide +kernel

theorem mutation_bad_assignment :
    expressionGuard 1000 (.binary "=" (.nat 1) (.var "x")) = false := by decide +kernel

theorem mutation_declaration_controlled : statementGuard 1000
    (.branch (.nat 1) (.declare [⟨"uint64_t","n",none⟩]) .skip) = false := by decide +kernel

theorem mutation_bad_for_initializer : statementGuard 1000
    (.forLoop (.eval (.nat 0)) none (.nat 0) .skip) = false := by decide +kernel

theorem mutation_nonblock_function : functionGuard ⟨"int","main",[],.returnStmt (.nat 0)⟩ =
    false := by decide +kernel

theorem checked_counter_exact {text : String}
    (accepted : checkedCounter text RamanujanPV.QuotientCSourceV2.functions = true) :
    text = RamanujanPV.QuotientCSourceV2.actualSource := by
  simp only [checkedCounter,Bool.and_eq_true,decide_eq_true_eq] at accepted
  rw [actual_counter_render] at accepted
  exact (Option.some.inj accepted.2).symm

theorem checked_driver_exact {text : String}
    (accepted : checkedDriver text HighDriverSource.program = true) :
    text = HighDriverSource.actualSource := by
  simp only [checkedDriver,Bool.and_eq_true,decide_eq_true_eq] at accepted
  rw [HighDriverSource.actual_source_bytes] at accepted
  exact (Option.some.inj accepted.2).symm

theorem mutation_counter_extra_semicolon : checkedCounter
    (RamanujanPV.QuotientCSourceV2.actualSource++";")
    RamanujanPV.QuotientCSourceV2.functions = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have h := congrArg String.length (checked_counter_exact accepted)
  simp only [String.length_append] at h
  have hs : ";".length = 1 := rfl
  rw [hs] at h
  omega

theorem mutation_driver_extra_semicolon : checkedDriver
    (HighDriverSource.actualSource++";") HighDriverSource.program = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have h := congrArg String.length (checked_driver_exact accepted)
  simp only [String.length_append] at h
  have hs : ";".length = 1 := rfl
  rw [hs] at h
  omega

#print axioms actual_counter_profile
#print axioms actual_driver_profile
#print axioms actual_counter_accepted
#print axioms actual_driver_accepted
#print axioms actual_counter_syntax
#print axioms actual_driver_syntax
#print axioms mutation_counter_extra_semicolon
#print axioms mutation_driver_extra_semicolon
end RHOcticPush.CounterSyntax

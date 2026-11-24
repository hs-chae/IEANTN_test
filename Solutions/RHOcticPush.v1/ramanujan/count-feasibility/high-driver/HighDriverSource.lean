import RamanujanPV.QuotientDriverSource

/-! Additive fixed high-input main; the original driver remains unchanged.
The existing restricted renderer/model interpretation is an explicit boundary;
this does not assert an independently verified C frontend. -/
namespace RHOcticPush.HighDriverSource
open LCMSourcePV.Witness.C
open RamanujanPV.QuotientDriverSource
set_option maxRecDepth 100000

def input : Nat := 1490000000000
def counterCall : Expr := .call (.var "rpc_quotient_count")
  [.nat input, .nat capacity, .var "rpc_small", .var "rpc_large"]
def mainFunction : Function :=
  ⟨"int", "main", [], .sequence [
    .declare [⟨"uint64_t", "result", some counterCall⟩],
    .branch (.binary "!=" (.call (.var "fwrite")
      [.unary "&" (.var "result"), .nat 8, .nat 1, .var "stdout"]) (.nat 1))
      (.returnStmt (.nat 1)) .skip,
    .branch (.binary "!=" (.call (.var "fflush") [.var "stdout"]) (.nat 0))
      (.returnStmt (.nat 1)) .skip,
    .returnStmt (.nat 0)]⟩
def program : TranslationUnit := ⟨counterPrototype, arrays, mainFunction⟩
def actualSource : String := include_str "c/verified_quotient_driver_high.c"

theorem actual_source_bytes : render program = some actualSource := by decide +kernel
theorem actual_source_checked :
    LCMSourcePV.RestrictedC.SourceCorresponds render actualSource program :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource program
    actual_source_bytes (by decide +kernel)

theorem same_actual_static_arrays :
    program.globals = RamanujanPV.QuotientDriverSource.program.globals := rfl
theorem same_actual_counter_prototype :
    program.prototype.returnType = RamanujanPV.QuotientCSourceV2.countFunction.returnType ∧
    program.prototype.name = RamanujanPV.QuotientCSourceV2.countFunction.name ∧
    program.prototype.parameters = RamanujanPV.QuotientCSourceV2.countFunction.parameters :=
  ⟨rfl, rfl, rfl⟩

#print axioms actual_source_bytes
#print axioms actual_source_checked
#print axioms same_actual_static_arrays
#print axioms same_actual_counter_prototype
end RHOcticPush.HighDriverSource

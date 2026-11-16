/- New entry mutates only the local high word which is actually consumed.
The old entry/source and every original model are preserved. -/
import SynergyMomentC.SourceBindings
import SynergyMomentC.Model
namespace SynergyMomentCHi
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
open SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def highUpdate : Stmt := .eval (.binary "=" (.field "." (.var "c") "hi")
  (.call (.var "addU") [.field "." (.var "c") "hi",
    .call (.var "mulU") [.cast "U" (.nat 21600),.var "S"]]))
def loopStatements (kind : Kind) : List Stmt :=
  (SynergyMomentC.loopStatements kind).take 4++[highUpdate]++
    (SynergyMomentC.loopStatements kind).drop 5
def entry (kind : Kind) : Function :=
  {SynergyHeightC.Generated.f_main with name:="__wrap_main",body:=.sequence (
    SynergyHeightC.PointExecuteAPI.mainStatements.take 6++
    [.whileLoop (.binary "<" (.var "i") (.var "cells")) (.sequence (loopStatements kind))]++
    SynergyHeightC.PointExecuteAPI.mainStatements.drop 7)}
def code (kind : Kind) : List Function := SynergyHeightC.Bundle.code++[entry kind]
def massSource : String := include_str "../../source/mass-entry.cpp"
def momentSource : String := include_str "../../source/first_moment-entry.cpp"
def massUnit : String := include_str "../../source/mass.cpp"
def momentUnit : String := include_str "../../source/first_moment.cpp"

theorem actual_mass_source : renderCLinkageFunction (entry .mass)=some massSource := by
  decide +kernel
theorem actual_moment_source : renderCLinkageFunction (entry .firstMoment)=some momentSource := by
  decide +kernel
theorem actual_mass_unit :
    massUnit="#include \"../../moment-program-v1/source/base/height_bundle.cpp\"\n"++massSource := rfl
theorem actual_moment_unit :
    momentUnit="#include \"../../moment-program-v1/source/base/height_bundle.cpp\"\n"++momentSource := rfl

def patched (c : ProofBox) : ProofBox :=
  ⟨c.lo,(SynergyHeightC.MainWeightModel.adjustedC c).hi⟩
theorem low_preserved (c : ProofBox) : (patched c).lo=c.lo := rfl
theorem high_same (c : ProofBox) :
    (patched c).hi=(SynergyHeightC.MainWeightModel.adjustedC c).hi := rfl
theorem fc_same (c : ProofBox) : (⟨(patched c).hi,(patched c).hi⟩ : ProofBox)=
    SynergyHeightC.MainWeightModel.fc c := rfl

theorem literal_shift : (ProofBox.literal 128 21600 1).hi=21600*ProofBox.scale 128 := by
  decide +kernel
theorem high_integer_exact (c : ProofBox) : (patched c).hi=c.hi+21600*ProofBox.scale 128 := by
  change c.hi+(ProofBox.literal 128 21600 1).hi=_
  rw [literal_shift]

theorem source_term_same (kind : Kind) (left right c d : ProofBox) :
    Model.termFromWords kind left right (patched c).hi d.hi=Model.term kind left right c d := by
  exact (Model.term_from_high_words kind left right c d rfl rfl).symm

theorem old_execution_preserved (kind : Kind) {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (old : ArraySourceCalls.SourceCall SynergyC.Header.layout SynergyHeightC.Bundle.code
      rank name args s v t) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout (code kind) rank name args s v t :=
  ArraySourceCalls.code_extension (fun _ h=>List.mem_append_left _ h) old

#print axioms actual_mass_source
#print axioms actual_moment_source
#print axioms actual_mass_unit
#print axioms actual_moment_unit
#print axioms low_preserved
#print axioms high_same
#print axioms fc_same
#print axioms literal_shift
#print axioms high_integer_exact
#print axioms source_term_same
#print axioms old_execution_preserved
end SynergyMomentCHi

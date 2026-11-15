/- Actual C-linkage entry sources and their exact ordinary C statement ASTs.
The extern-C prefix gives a generic C-linkage symbol; linker/CRT entry mapping
and observed execution association are separate explicit obligations. -/
import SynergyHeightC.PointExecuteDefinitions
import ScopedC.SourceCallExtension
namespace SynergyMomentC
open ScopedC ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

inductive Kind where
  | mass
  | firstMoment
  deriving DecidableEq

def massTerm : Expr := .call (.var "mul")
  [.call (.var "rat") [.nat 2,.nat 1],.call (.var "mul") [.var "w",.var "fc"]]
def contribution : Kind → Expr
  | .mass => massTerm
  | .firstMoment => .call (.var "mul") [massTerm,.var "fd"]
def accumulation (kind : Kind) : Stmt := .eval (.binary "=" (.var "total")
  (.call (.var "add") [.var "total",contribution kind]))
def loopStatements (kind : Kind) : List Stmt :=
  SynergyHeightC.PointExecuteAPI.loopStatements.take 8++[accumulation kind]++
    SynergyHeightC.PointExecuteAPI.loopStatements.drop 9
def statements (kind : Kind) : List Stmt :=
  SynergyHeightC.PointExecuteAPI.mainStatements.take 6++
    [.whileLoop (.binary "<" (.var "i") (.var "cells")) (.sequence (loopStatements kind))]++
    SynergyHeightC.PointExecuteAPI.mainStatements.drop 7
def entry (kind : Kind) : Function :=
  {SynergyHeightC.Generated.f_main with name:="__wrap_main",body:=.sequence (statements kind)}
def code (kind : Kind) : List Function := SynergyHeightC.Bundle.code++[entry kind]

/-- The selected existing C syntax renderer with the actual standard C++
external-C linkage prefix. This records the own application header bytes;
compiler/linker linkage behavior stays at its explicit generic boundary. -/
def renderCLinkageFunction (f : Function) : Option String := do
  pure ("extern \"C\" "++(←renderFunction f))
def massSource : String := include_str "../../source/mass-entry.cpp"
def firstMomentSource : String := include_str "../../source/first_moment-entry.cpp"
def massUnit : String := include_str "../../source/mass.cpp"
def firstMomentUnit : String := include_str "../../source/first_moment.cpp"

theorem actual_mass_source : renderCLinkageFunction (entry .mass)=some massSource := by
  decide +kernel
theorem actual_first_moment_source :
    renderCLinkageFunction (entry .firstMoment)=some firstMomentSource := by
  decide +kernel
theorem actual_mass_translation_unit :
    massUnit="#include \"base/height_bundle.cpp\"\n"++massSource := rfl
theorem actual_first_moment_translation_unit :
    firstMomentUnit="#include \"base/height_bundle.cpp\"\n"++firstMomentSource := rfl

theorem entry_symbol (kind : Kind) : (entry kind).name="__wrap_main" := rfl
theorem original_code_included (kind : Kind) (f : Function)
    (old : f ∈ SynergyHeightC.Bundle.code) : f ∈ code kind := List.mem_append_left _ old

theorem old_execution_preserved (kind : Kind) {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (old : ArraySourceCalls.SourceCall SynergyC.Header.layout SynergyHeightC.Bundle.code
      rank name args s v t) :
    ArraySourceCalls.SourceCall SynergyC.Header.layout (code kind) rank name args s v t :=
  ArraySourceCalls.code_extension (original_code_included kind) old

#print axioms actual_mass_source
#print axioms actual_first_moment_source
#print axioms actual_mass_translation_unit
#print axioms actual_first_moment_translation_unit
#print axioms entry_symbol
#print axioms original_code_included
#print axioms old_execution_preserved
end SynergyMomentC

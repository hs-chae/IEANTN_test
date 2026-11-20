/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCSourceV2

/-! Complete source binding for a fixed-input driver. The structured translation
unit contains its actual global arrays and counter prototype, not only main.
The I/O functions have explicit source calls, whose operational composition is
separate from this source identity and static-initialization development. -/
namespace RamanujanPV.QuotientDriverSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def input : Nat := 38358837683
def capacity : Nat := 1500000

inductive ElementType where
  | uint64
  deriving Repr, DecidableEq

/-- C static-storage arrays without explicit initializers are zero-initialized.
The static storage class and fixed uint64 element type are part of this node. -/
structure StaticArray where
  name : String
  element : ElementType
  count : Nat
  deriving Repr, DecidableEq

structure Prototype where
  returnType : String
  name : String
  parameters : List (String × String)
  deriving Repr

structure TranslationUnit where
  prototype : Prototype
  globals : List StaticArray
  main : Function
  deriving Repr

def arrays : List StaticArray :=
  [⟨"rpc_small", .uint64, capacity⟩, ⟨"rpc_large", .uint64, capacity⟩]

def counterPrototype : Prototype :=
  ⟨"uint64_t", "rpc_quotient_count",
   [("uint64_t", "n"), ("uint64_t", "capacity"),
    ("uint64_t*", "small"), ("uint64_t*", "large")]⟩

def counterCall : Expr :=
  .call (.var "rpc_quotient_count")
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

def renderArray (array : StaticArray) : String :=
  match array.element with
  | .uint64 => "static uint64_t " ++ array.name ++ "[" ++ toString array.count ++ "];\n"

def renderPrototype (prototype : Prototype) : String :=
  "extern " ++ prototype.returnType ++ " " ++ prototype.name ++ "(" ++
  join (prototype.parameters.map (fun (type, name) => type ++ " " ++ name)) ++ ");\n"

def render (unit : TranslationUnit) : Option String := do
  return "/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n#include <stdio.h>\n\n" ++
    renderPrototype unit.prototype ++ String.join (unit.globals.map renderArray) ++
    "\n" ++ (← renderFunction unit.main)

def actualSource : String := include_str "../c/verified_quotient_driver_n0.c"

theorem actual_source_bytes : render program = some actualSource := by decide +kernel

theorem actual_source_checked :
    LCMSourcePV.RestrictedC.SourceCorresponds render actualSource program :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource program
    actual_source_bytes (by decide +kernel)

theorem actual_globals : program.globals =
    [⟨"rpc_small", .uint64, 1500000⟩, ⟨"rpc_large", .uint64, 1500000⟩] := rfl

theorem actual_counter_prototype :
    program.prototype.returnType = QuotientCSourceV2.countFunction.returnType ∧
    program.prototype.name = QuotientCSourceV2.countFunction.name ∧
    program.prototype.parameters = QuotientCSourceV2.countFunction.parameters := by
  exact ⟨rfl, rfl, rfl⟩

theorem actual_counter_call : counterCall = .call (.var "rpc_quotient_count")
    [.nat 38358837683, .nat 1500000, .var "rpc_small", .var "rpc_large"] := rfl

#print axioms actual_source_bytes
#print axioms actual_source_checked
#print axioms actual_counter_prototype
end RamanujanPV.QuotientDriverSource

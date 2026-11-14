/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.Machine

namespace ScopedC.Header
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false

inductive TypeDecl where
  | alias (underlying name : String)
  | record (name : String) (fields : List (String × String))

def typeDeclarations : List TypeDecl := [
  .alias "lean_object*" "N",
  .record "S" [("N","mag"),("unsigned","neg")],
  .record "Q" [("S","num"),("N","den")],
  .record "RI" [("Q","lo"),("Q","hi")],
  .record "I" [("S","lo"),("S","hi"),("unsigned","ok")],
  .record "Node" [("unsigned","op"),("unsigned","a"),("unsigned","b"),
    ("const char*","num"),("const char*","den")],
  .record "Row" [("const Node*","nodes"),("unsigned","count"),("unsigned","cells")]]

def globals : List Decl := [
  {type:="N",name:="pool",value:=none,arrayExtent:=some 4000000},
  {type:="unsigned",name:="poolTop",value:=some (.nat 0)},
  {type:="unsigned",name:="poolHigh",value:=some (.nat 0)},
  {type:="unsigned",name:="depth",value:=some (.nat 24)},
  {type:="N",name:="scale100",value:=none},
  {type:="Q",name:="expCoeffs",value:=none,arrayExtent:=some 65},
  {type:="Q",name:="atanhCoeffs",value:=none,arrayExtent:=some 65},
  {type:="RI",name:="preparedLn2",value:=none}]

def renderTypeDecl : TypeDecl → String
  | .alias underlying name => "typedef "++underlying++" "++name++";\n"
  | .record name fields => "struct "++name++"{"++String.join
      (fields.map (fun (t,n) => t++" "++n++";"))++"};\n"

/-- Only pinned generic external headers and the exact runtime initialization
prototype. All application type/array/initializer declarations are structured
above. Header implementation and physical ABI contracts remain disclosed. -/
def externalPrelude : String :=
  "#include <lean/lean.h>\n#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n"++
  "extern \"C\" void lean_initialize_runtime_module(void);\n"

def render : Option String := do
  let gs ← globals.mapM (fun d => do return "static "++(←renderDecl d)++";\n")
  pure (externalPrelude++String.join (typeDeclarations.map renderTypeDecl)++String.join gs)

def records : List (String × List (String × String)) :=
  typeDeclarations.filterMap (fun d => match d with
    | .alias _ _ => none
    | .record n fs => some (n,fs.map (fun (t,n) => (n,t))))

def layout : Layout := {
  integers := [("unsigned",⟨false,32⟩),("unsigned int",⟨false,32⟩),
    ("int",⟨true,32⟩),("char",⟨true,8⟩),("uint8_t",⟨false,8⟩),
    ("uint64_t",⟨false,64⟩),("size_t",⟨false,64⟩)]
  records := records
  booleanType := ⟨false,1⟩ }

/-- Static initialization is computed from the actual declared type. A
runtime Nat pointer begins null, rather than as an assumed valid Nat object. -/
def zeroValue : Nat → String → Option Value
  | 0,_ => none
  | fuel+1,t => do
    let type := normalizeType t
    if type == "N" || isPointerType type then pure .null
    else if let some ti := layout.integers.lookup type then
      pure (.integer (←Scalar.checked ti 0))
    else
      let fs ← records.lookup type
      let vs ← fs.mapM (fun f => zeroValue fuel f.2)
      pure (.record type vs)

theorem actual_S_layout : fieldsOf layout "S" = some [("mag","N"),("neg","unsigned")] := by decide +kernel
theorem static_N_starts_null : zeroValue 10 "N" = some .null := by
  have mark : (match zeroValue 10 "N" with | some .null => true | _ => false) = true := by
    decide +kernel
  cases he : zeroValue 10 "N" with
  | none => simp [he] at mark
  | some v => cases v <;> simp_all

#print axioms actual_S_layout
#print axioms static_N_starts_null
end ScopedC.Header

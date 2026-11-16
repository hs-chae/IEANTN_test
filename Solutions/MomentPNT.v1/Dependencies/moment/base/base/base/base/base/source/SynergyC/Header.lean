/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.Header
namespace SynergyC.Header
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Width is structured data, not an opaque application declaration. -/
inductive TypeDecl where
  | unsignedAlias (name : String) (width : Nat)
  | record (name : String) (fields : List (String × String))

def types : List TypeDecl := [
  .unsignedAlias "U" 512,
  .record "I" [("U","lo"),("U","hi")]]
def renderType : TypeDecl → String
  | .unsignedAlias name width => "typedef unsigned _BitInt("++toString width++") "++name++";\n"
  | .record name fields => ScopedC.Header.renderTypeDecl (.record name fields)
def globals : List Decl := [
  {type:="const U",name:="S",value:=some (.binary "<<" (.cast "U" (.nat 1)) (.nat 128))},
  {type:="const U",name:="MAXU",value:=some (.cast "U" (.unary "-" (.nat 1)))},
  {type:="I",name:="ln2",value:=none}]
def externalPrelude : String := "#include <stdint.h>\n#include <stdio.h>\n#include <stdlib.h>\n"
def aliasIntegers : List (String × ScopedC.Scalar.IntType) :=
  types.filterMap (fun t => match t with
    | .unsignedAlias name width => some (name,⟨false,width⟩)
    | _ => none)
def records : List (String × List (String × String)) :=
  types.filterMap (fun t => match t with
    | .record name fields => some (name,fields.map (fun(t,n)=>(n,t)))
    | _ => none)
def layout : Layout := {
  integers:=aliasIntegers++[("unsigned",⟨false,32⟩),("unsigned int",⟨false,32⟩),
    ("int",⟨true,32⟩),("char",⟨true,8⟩),("uint64_t",⟨false,64⟩),("size_t",⟨false,64⟩)]
  records:=records
  booleanType:=⟨false,1⟩}

theorem actual_U_declaration : ScopedC.RestrictedC.tokens (renderType (.unsignedAlias "U" 512)) =
    some ["typedef","unsigned","_BitInt","(","512",")","U",";"] := by decide +kernel
theorem U_has_width512 : layout.integers.lookup "U" = some ⟨false,512⟩ := by decide +kernel
theorem I_has_two_U_fields : fieldsOf layout "I" = some [("lo","U"),("hi","U")] := by decide +kernel

#print axioms actual_U_declaration
#print axioms U_has_width512
end SynergyC.Header

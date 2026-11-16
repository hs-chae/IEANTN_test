/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.Bundle
namespace SynergyC.Bundle
open ScopedC.SourceBundle
set_option maxHeartbeats 0

def sourceTypes : List Header.TypeDecl := tree.values.filterMap (fun p => match p with
  | .typeDecl t => some t | _ => none)
def sourceGlobals : List ScopedC.Syntax.Decl := tree.values.filterMap (fun p => match p with
  | .global d => some d | _ => none)
def entry : File := ⟨"basis_bundle.cpp",include_str "../../bundle-source/basis_bundle.cpp"⟩
theorem types_exact : sourceTypes = Header.types := by rfl
theorem globals_exact : sourceGlobals = Header.globals := by rfl
theorem entry_exact : entry.text = directive tree.file.name := by decide +kernel
#print axioms types_exact
#print axioms globals_exact
#print axioms entry_exact
end SynergyC.Bundle

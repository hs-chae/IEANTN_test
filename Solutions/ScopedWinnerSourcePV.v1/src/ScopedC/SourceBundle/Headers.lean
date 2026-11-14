/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
namespace ScopedC.SourceBundle.Headers
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def file0 : File := ⟨"header_prelude.inc",include_str "../../../source/header_prelude.inc"⟩
def piece0 : Piece := .prelude
theorem bound0 : Piece.Bound piece0 file0 := .prelude (by decide +kernel)
def file1 : File := ⟨"header_type_0.inc",include_str "../../../source/header_type_0.inc"⟩
def piece1 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨0,by decide⟩)
theorem bound1 : Piece.Bound piece1 file1 := .typeDecl (by decide +kernel)
def file2 : File := ⟨"header_type_1.inc",include_str "../../../source/header_type_1.inc"⟩
def piece2 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨1,by decide⟩)
theorem bound2 : Piece.Bound piece2 file2 := .typeDecl (by decide +kernel)
def file3 : File := ⟨"header_type_2.inc",include_str "../../../source/header_type_2.inc"⟩
def piece3 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨2,by decide⟩)
theorem bound3 : Piece.Bound piece3 file3 := .typeDecl (by decide +kernel)
def file4 : File := ⟨"header_type_3.inc",include_str "../../../source/header_type_3.inc"⟩
def piece4 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨3,by decide⟩)
theorem bound4 : Piece.Bound piece4 file4 := .typeDecl (by decide +kernel)
def file5 : File := ⟨"header_type_4.inc",include_str "../../../source/header_type_4.inc"⟩
def piece5 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨4,by decide⟩)
theorem bound5 : Piece.Bound piece5 file5 := .typeDecl (by decide +kernel)
def file6 : File := ⟨"header_type_5.inc",include_str "../../../source/header_type_5.inc"⟩
def piece6 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨5,by decide⟩)
theorem bound6 : Piece.Bound piece6 file6 := .typeDecl (by decide +kernel)
def file7 : File := ⟨"header_type_6.inc",include_str "../../../source/header_type_6.inc"⟩
def piece7 : Piece := .typeDecl (ScopedC.Header.typeDeclarations.get ⟨6,by decide⟩)
theorem bound7 : Piece.Bound piece7 file7 := .typeDecl (by decide +kernel)
def file8 : File := ⟨"header_global_0.inc",include_str "../../../source/header_global_0.inc"⟩
def piece8 : Piece := .global (ScopedC.Header.globals.get ⟨0,by decide⟩)
theorem bound8 : Piece.Bound piece8 file8 := .global (by decide +kernel)
def file9 : File := ⟨"header_global_1.inc",include_str "../../../source/header_global_1.inc"⟩
def piece9 : Piece := .global (ScopedC.Header.globals.get ⟨1,by decide⟩)
theorem bound9 : Piece.Bound piece9 file9 := .global (by decide +kernel)
def file10 : File := ⟨"header_global_2.inc",include_str "../../../source/header_global_2.inc"⟩
def piece10 : Piece := .global (ScopedC.Header.globals.get ⟨2,by decide⟩)
theorem bound10 : Piece.Bound piece10 file10 := .global (by decide +kernel)
def file11 : File := ⟨"header_global_3.inc",include_str "../../../source/header_global_3.inc"⟩
def piece11 : Piece := .global (ScopedC.Header.globals.get ⟨3,by decide⟩)
theorem bound11 : Piece.Bound piece11 file11 := .global (by decide +kernel)
def file12 : File := ⟨"header_global_4.inc",include_str "../../../source/header_global_4.inc"⟩
def piece12 : Piece := .global (ScopedC.Header.globals.get ⟨4,by decide⟩)
theorem bound12 : Piece.Bound piece12 file12 := .global (by decide +kernel)
def file13 : File := ⟨"header_global_5.inc",include_str "../../../source/header_global_5.inc"⟩
def piece13 : Piece := .global (ScopedC.Header.globals.get ⟨5,by decide⟩)
theorem bound13 : Piece.Bound piece13 file13 := .global (by decide +kernel)
def file14 : File := ⟨"header_global_6.inc",include_str "../../../source/header_global_6.inc"⟩
def piece14 : Piece := .global (ScopedC.Header.globals.get ⟨6,by decide⟩)
theorem bound14 : Piece.Bound piece14 file14 := .global (by decide +kernel)
def file15 : File := ⟨"header_global_7.inc",include_str "../../../source/header_global_7.inc"⟩
def piece15 : Piece := .global (ScopedC.Header.globals.get ⟨7,by decide⟩)
theorem bound15 : Piece.Bound piece15 file15 := .global (by decide +kernel)
def pieces : List Piece := [piece0,piece1,piece2,piece3,piece4,piece5,piece6,piece7,piece8,piece9,piece10,piece11,piece12,piece13,piece14,piece15]
def files : List File := [file0,file1,file2,file3,file4,file5,file6,file7,file8,file9,file10,file11,file12,file13,file14,file15]
theorem types_exact : pieces.flatMap Piece.types = ScopedC.Header.typeDeclarations := by rfl
theorem globals_exact : pieces.flatMap Piece.globals = ScopedC.Header.globals := by rfl
theorem all_bound : List.Forall₂ Piece.Bound pieces files := by
  exact List.Forall₂.cons bound0 (List.Forall₂.cons bound1 (List.Forall₂.cons bound2 (List.Forall₂.cons bound3 (List.Forall₂.cons bound4 (List.Forall₂.cons bound5 (List.Forall₂.cons bound6 (List.Forall₂.cons bound7 (List.Forall₂.cons bound8 (List.Forall₂.cons bound9 (List.Forall₂.cons bound10 (List.Forall₂.cons bound11 (List.Forall₂.cons bound12 (List.Forall₂.cons bound13 (List.Forall₂.cons bound14 (List.Forall₂.cons bound15 (List.Forall₂.nil))))))))))))))))
#print axioms all_bound
end ScopedC.SourceBundle.Headers

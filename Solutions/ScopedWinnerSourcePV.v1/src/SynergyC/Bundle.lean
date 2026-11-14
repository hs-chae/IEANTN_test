/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import SynergyC.Header
import SynergyC.Generated
namespace SynergyC.Bundle
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 100000
inductive Piece where
  | prelude
  | typeDecl (d : Header.TypeDecl)
  | global (d : Decl)
  | function (f : Function)
inductive Piece.Bound : Piece → File → Prop where
  | prelude {file} (h : file.text = Header.externalPrelude) : Bound .prelude file
  | typeDecl {d file} (h : file.text = Header.renderType d) : Bound (.typeDecl d) file
  | global {d file} (h : (do pure ("static "++(←renderDecl d)++";\n")) = some file.text) : Bound (.global d) file
  | function {f file} (h : renderFunction f = some file.text) : Bound (.function f) file

def file0 : File := ⟨"prelude.inc",include_str "../../bundle-source/prelude.inc"⟩
def piece0 : Piece := .prelude
theorem bound0 : Piece.Bound piece0 file0 := .prelude (by rfl)
def tree0 : ScopedC.SourceBundle.Tree Piece := .leaf file0 piece0
theorem tree_bound0 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree0 := .leaf bound0
def file1 : File := ⟨"type_U.inc",include_str "../../bundle-source/type_U.inc"⟩
def piece1 : Piece := .typeDecl (.unsignedAlias "U" 512)
theorem bound1 : Piece.Bound piece1 file1 := .typeDecl (by rfl)
def tree1 : ScopedC.SourceBundle.Tree Piece := .leaf file1 piece1
theorem tree_bound1 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree1 := .leaf bound1
def file2 : File := ⟨"type_I.inc",include_str "../../bundle-source/type_I.inc"⟩
def piece2 : Piece := .typeDecl (.record "I" [("U","lo"),("U","hi")])
theorem bound2 : Piece.Bound piece2 file2 := .typeDecl (by rfl)
def tree2 : ScopedC.SourceBundle.Tree Piece := .leaf file2 piece2
theorem tree_bound2 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree2 := .leaf bound2
def file3 : File := ⟨"global_S.inc",include_str "../../bundle-source/global_S.inc"⟩
def piece3 : Piece := .global {type:="const U",name:="S",value:=(some (.binary "<<" (.cast "U" (.nat 1)) (.nat 128))),arrayExtent:=none}
theorem bound3 : Piece.Bound piece3 file3 := .global (by decide +kernel)
def tree3 : ScopedC.SourceBundle.Tree Piece := .leaf file3 piece3
theorem tree_bound3 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree3 := .leaf bound3
def file4 : File := ⟨"global_MAXU.inc",include_str "../../bundle-source/global_MAXU.inc"⟩
def piece4 : Piece := .global {type:="const U",name:="MAXU",value:=(some (.cast "U" (.unary "-" (.nat 1)))),arrayExtent:=none}
theorem bound4 : Piece.Bound piece4 file4 := .global (by decide +kernel)
def tree4 : ScopedC.SourceBundle.Tree Piece := .leaf file4 piece4
theorem tree_bound4 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree4 := .leaf bound4
def file5 : File := ⟨"global_ln2.inc",include_str "../../bundle-source/global_ln2.inc"⟩
def piece5 : Piece := .global {type:="I",name:="ln2",value:=none,arrayExtent:=none}
theorem bound5 : Piece.Bound piece5 file5 := .global (by decide +kernel)
def tree5 : ScopedC.SourceBundle.Tree Piece := .leaf file5 piece5
theorem tree_bound5 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree5 := .leaf bound5
def file6 : File := ⟨"function_fail.inc",include_str "../../bundle-source/function_fail.inc"⟩
def piece6 : Piece := .function Generated.f_fail
theorem bound6 : Piece.Bound piece6 file6 := .function (by simpa only [file6] using Generated.render_fail)
def tree6 : ScopedC.SourceBundle.Tree Piece := .leaf file6 piece6
theorem tree_bound6 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree6 := .leaf bound6
def file7 : File := ⟨"function_addU.inc",include_str "../../bundle-source/function_addU.inc"⟩
def piece7 : Piece := .function Generated.f_addU
theorem bound7 : Piece.Bound piece7 file7 := .function (by simpa only [file7] using Generated.render_addU)
def tree7 : ScopedC.SourceBundle.Tree Piece := .leaf file7 piece7
theorem tree_bound7 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree7 := .leaf bound7
def file8 : File := ⟨"function_mulU.inc",include_str "../../bundle-source/function_mulU.inc"⟩
def piece8 : Piece := .function Generated.f_mulU
theorem bound8 : Piece.Bound piece8 file8 := .function (by simpa only [file8] using Generated.render_mulU)
def tree8 : ScopedC.SourceBundle.Tree Piece := .leaf file8 piece8
theorem tree_bound8 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree8 := .leaf bound8
def file9 : File := ⟨"function_ceilDiv.inc",include_str "../../bundle-source/function_ceilDiv.inc"⟩
def piece9 : Piece := .function Generated.f_ceilDiv
theorem bound9 : Piece.Bound piece9 file9 := .function (by simpa only [file9] using Generated.render_ceilDiv)
def tree9 : ScopedC.SourceBundle.Tree Piece := .leaf file9 piece9
theorem tree_bound9 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree9 := .leaf bound9
def file10 : File := ⟨"function_rat.inc",include_str "../../bundle-source/function_rat.inc"⟩
def piece10 : Piece := .function Generated.f_rat
theorem bound10 : Piece.Bound piece10 file10 := .function (by simpa only [file10] using Generated.render_rat)
def tree10 : ScopedC.SourceBundle.Tree Piece := .leaf file10 piece10
theorem tree_bound10 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree10 := .leaf bound10
def file11 : File := ⟨"function_unit.inc",include_str "../../bundle-source/function_unit.inc"⟩
def piece11 : Piece := .function Generated.f_unit
theorem bound11 : Piece.Bound piece11 file11 := .function (by simpa only [file11] using Generated.render_unit)
def tree11 : ScopedC.SourceBundle.Tree Piece := .leaf file11 piece11
theorem tree_bound11 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree11 := .leaf bound11
def file12 : File := ⟨"function_zero.inc",include_str "../../bundle-source/function_zero.inc"⟩
def piece12 : Piece := .function Generated.f_zero
theorem bound12 : Piece.Bound piece12 file12 := .function (by simpa only [file12] using Generated.render_zero)
def tree12 : ScopedC.SourceBundle.Tree Piece := .leaf file12 piece12
theorem tree_bound12 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree12 := .leaf bound12
def file13 : File := ⟨"function_add.inc",include_str "../../bundle-source/function_add.inc"⟩
def piece13 : Piece := .function Generated.f_add
theorem bound13 : Piece.Bound piece13 file13 := .function (by simpa only [file13] using Generated.render_add)
def tree13 : ScopedC.SourceBundle.Tree Piece := .leaf file13 piece13
theorem tree_bound13 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree13 := .leaf bound13
def file14 : File := ⟨"function_mul.inc",include_str "../../bundle-source/function_mul.inc"⟩
def piece14 : Piece := .function Generated.f_mul
theorem bound14 : Piece.Bound piece14 file14 := .function (by simpa only [file14] using Generated.render_mul)
def tree14 : ScopedC.SourceBundle.Tree Piece := .leaf file14 piece14
theorem tree_bound14 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree14 := .leaf bound14
def file15 : File := ⟨"function_divI.inc",include_str "../../bundle-source/function_divI.inc"⟩
def piece15 : Piece := .function Generated.f_divI
theorem bound15 : Piece.Bound piece15 file15 := .function (by simpa only [file15] using Generated.render_divI)
def tree15 : ScopedC.SourceBundle.Tree Piece := .leaf file15 piece15
theorem tree_bound15 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree15 := .leaf bound15
def file16 : File := ⟨"function_divN.inc",include_str "../../bundle-source/function_divN.inc"⟩
def piece16 : Piece := .function Generated.f_divN
theorem bound16 : Piece.Bound piece16 file16 := .function (by simpa only [file16] using Generated.render_divN)
def tree16 : ScopedC.SourceBundle.Tree Piece := .leaf file16 piece16
theorem tree_bound16 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree16 := .leaf bound16
def file17 : File := ⟨"function_positiveSub.inc",include_str "../../bundle-source/function_positiveSub.inc"⟩
def piece17 : Piece := .function Generated.f_positiveSub
theorem bound17 : Piece.Bound piece17 file17 := .function (by simpa only [file17] using Generated.render_positiveSub)
def tree17 : ScopedC.SourceBundle.Tree Piece := .leaf file17 piece17
theorem tree_bound17 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree17 := .leaf bound17
def file18 : File := ⟨"function_expNeg.inc",include_str "../../bundle-source/function_expNeg.inc"⟩
def piece18 : Piece := .function Generated.f_expNeg
theorem bound18 : Piece.Bound piece18 file18 := .function (by simpa only [file18] using Generated.render_expNeg)
def tree18 : ScopedC.SourceBundle.Tree Piece := .leaf file18 piece18
theorem tree_bound18 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree18 := .leaf bound18
def file19 : File := ⟨"function_atanh2.inc",include_str "../../bundle-source/function_atanh2.inc"⟩
def piece19 : Piece := .function Generated.f_atanh2
theorem bound19 : Piece.Bound piece19 file19 := .function (by simpa only [file19] using Generated.render_atanh2)
def tree19 : ScopedC.SourceBundle.Tree Piece := .leaf file19 piece19
theorem tree_bound19 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree19 := .leaf bound19
def file20 : File := ⟨"function_logPos.inc",include_str "../../bundle-source/function_logPos.inc"⟩
def piece20 : Piece := .function Generated.f_logPos
theorem bound20 : Piece.Bound piece20 file20 := .function (by simpa only [file20] using Generated.render_logPos)
def tree20 : ScopedC.SourceBundle.Tree Piece := .leaf file20 piece20
theorem tree_bound20 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree20 := .leaf bound20
def file21 : File := ⟨"function_floorCube.inc",include_str "../../bundle-source/function_floorCube.inc"⟩
def piece21 : Piece := .function Generated.f_floorCube
theorem bound21 : Piece.Bound piece21 file21 := .function (by simpa only [file21] using Generated.render_floorCube)
def tree21 : ScopedC.SourceBundle.Tree Piece := .leaf file21 piece21
theorem tree_bound21 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree21 := .leaf bound21
def file22 : File := ⟨"function_cubeRoot.inc",include_str "../../bundle-source/function_cubeRoot.inc"⟩
def piece22 : Piece := .function Generated.f_cubeRoot
theorem bound22 : Piece.Bound piece22 file22 := .function (by simpa only [file22] using Generated.render_cubeRoot)
def tree22 : ScopedC.SourceBundle.Tree Piece := .leaf file22 piece22
theorem tree_bound22 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree22 := .leaf bound22
def file23 : File := ⟨"function_gaussianCell.inc",include_str "../../bundle-source/function_gaussianCell.inc"⟩
def piece23 : Piece := .function Generated.f_gaussianCell
theorem bound23 : Piece.Bound piece23 file23 := .function (by simpa only [file23] using Generated.render_gaussianCell)
def tree23 : ScopedC.SourceBundle.Tree Piece := .leaf file23 piece23
theorem tree_bound23 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree23 := .leaf bound23
def file24 : File := ⟨"function_main.inc",include_str "../../bundle-source/function_main.inc"⟩
def piece24 : Piece := .function Generated.f_main
theorem bound24 : Piece.Bound piece24 file24 := .function (by simpa only [file24] using Generated.render_main)
def tree24 : ScopedC.SourceBundle.Tree Piece := .leaf file24 piece24
theorem tree_bound24 : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree24 := .leaf bound24
def join_file0 : File := ⟨"join_000.inc",include_str "../../bundle-source/join_000.inc"⟩
def join_tree0 : ScopedC.SourceBundle.Tree Piece := .pair join_file0 tree1 tree2
theorem join_bound0 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree0 := .pair tree_bound1 tree_bound2 (by decide +kernel)
def join_file1 : File := ⟨"join_001.inc",include_str "../../bundle-source/join_001.inc"⟩
def join_tree1 : ScopedC.SourceBundle.Tree Piece := .pair join_file1 tree0 join_tree0
theorem join_bound1 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree1 := .pair tree_bound0 join_bound0 (by decide +kernel)
def join_file2 : File := ⟨"join_002.inc",include_str "../../bundle-source/join_002.inc"⟩
def join_tree2 : ScopedC.SourceBundle.Tree Piece := .pair join_file2 tree4 tree5
theorem join_bound2 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree2 := .pair tree_bound4 tree_bound5 (by decide +kernel)
def join_file3 : File := ⟨"join_003.inc",include_str "../../bundle-source/join_003.inc"⟩
def join_tree3 : ScopedC.SourceBundle.Tree Piece := .pair join_file3 tree3 join_tree2
theorem join_bound3 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree3 := .pair tree_bound3 join_bound2 (by decide +kernel)
def join_file4 : File := ⟨"join_004.inc",include_str "../../bundle-source/join_004.inc"⟩
def join_tree4 : ScopedC.SourceBundle.Tree Piece := .pair join_file4 join_tree1 join_tree3
theorem join_bound4 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree4 := .pair join_bound1 join_bound3 (by decide +kernel)
def join_file5 : File := ⟨"join_005.inc",include_str "../../bundle-source/join_005.inc"⟩
def join_tree5 : ScopedC.SourceBundle.Tree Piece := .pair join_file5 tree7 tree8
theorem join_bound5 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree5 := .pair tree_bound7 tree_bound8 (by decide +kernel)
def join_file6 : File := ⟨"join_006.inc",include_str "../../bundle-source/join_006.inc"⟩
def join_tree6 : ScopedC.SourceBundle.Tree Piece := .pair join_file6 tree6 join_tree5
theorem join_bound6 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree6 := .pair tree_bound6 join_bound5 (by decide +kernel)
def join_file7 : File := ⟨"join_007.inc",include_str "../../bundle-source/join_007.inc"⟩
def join_tree7 : ScopedC.SourceBundle.Tree Piece := .pair join_file7 tree10 tree11
theorem join_bound7 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree7 := .pair tree_bound10 tree_bound11 (by decide +kernel)
def join_file8 : File := ⟨"join_008.inc",include_str "../../bundle-source/join_008.inc"⟩
def join_tree8 : ScopedC.SourceBundle.Tree Piece := .pair join_file8 tree9 join_tree7
theorem join_bound8 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree8 := .pair tree_bound9 join_bound7 (by decide +kernel)
def join_file9 : File := ⟨"join_009.inc",include_str "../../bundle-source/join_009.inc"⟩
def join_tree9 : ScopedC.SourceBundle.Tree Piece := .pair join_file9 join_tree6 join_tree8
theorem join_bound9 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree9 := .pair join_bound6 join_bound8 (by decide +kernel)
def join_file10 : File := ⟨"join_010.inc",include_str "../../bundle-source/join_010.inc"⟩
def join_tree10 : ScopedC.SourceBundle.Tree Piece := .pair join_file10 join_tree4 join_tree9
theorem join_bound10 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree10 := .pair join_bound4 join_bound9 (by decide +kernel)
def join_file11 : File := ⟨"join_011.inc",include_str "../../bundle-source/join_011.inc"⟩
def join_tree11 : ScopedC.SourceBundle.Tree Piece := .pair join_file11 tree13 tree14
theorem join_bound11 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree11 := .pair tree_bound13 tree_bound14 (by decide +kernel)
def join_file12 : File := ⟨"join_012.inc",include_str "../../bundle-source/join_012.inc"⟩
def join_tree12 : ScopedC.SourceBundle.Tree Piece := .pair join_file12 tree12 join_tree11
theorem join_bound12 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree12 := .pair tree_bound12 join_bound11 (by decide +kernel)
def join_file13 : File := ⟨"join_013.inc",include_str "../../bundle-source/join_013.inc"⟩
def join_tree13 : ScopedC.SourceBundle.Tree Piece := .pair join_file13 tree16 tree17
theorem join_bound13 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree13 := .pair tree_bound16 tree_bound17 (by decide +kernel)
def join_file14 : File := ⟨"join_014.inc",include_str "../../bundle-source/join_014.inc"⟩
def join_tree14 : ScopedC.SourceBundle.Tree Piece := .pair join_file14 tree15 join_tree13
theorem join_bound14 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree14 := .pair tree_bound15 join_bound13 (by decide +kernel)
def join_file15 : File := ⟨"join_015.inc",include_str "../../bundle-source/join_015.inc"⟩
def join_tree15 : ScopedC.SourceBundle.Tree Piece := .pair join_file15 join_tree12 join_tree14
theorem join_bound15 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree15 := .pair join_bound12 join_bound14 (by decide +kernel)
def join_file16 : File := ⟨"join_016.inc",include_str "../../bundle-source/join_016.inc"⟩
def join_tree16 : ScopedC.SourceBundle.Tree Piece := .pair join_file16 tree19 tree20
theorem join_bound16 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree16 := .pair tree_bound19 tree_bound20 (by decide +kernel)
def join_file17 : File := ⟨"join_017.inc",include_str "../../bundle-source/join_017.inc"⟩
def join_tree17 : ScopedC.SourceBundle.Tree Piece := .pair join_file17 tree18 join_tree16
theorem join_bound17 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree17 := .pair tree_bound18 join_bound16 (by decide +kernel)
def join_file18 : File := ⟨"join_018.inc",include_str "../../bundle-source/join_018.inc"⟩
def join_tree18 : ScopedC.SourceBundle.Tree Piece := .pair join_file18 tree21 tree22
theorem join_bound18 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree18 := .pair tree_bound21 tree_bound22 (by decide +kernel)
def join_file19 : File := ⟨"join_019.inc",include_str "../../bundle-source/join_019.inc"⟩
def join_tree19 : ScopedC.SourceBundle.Tree Piece := .pair join_file19 tree23 tree24
theorem join_bound19 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree19 := .pair tree_bound23 tree_bound24 (by decide +kernel)
def join_file20 : File := ⟨"join_020.inc",include_str "../../bundle-source/join_020.inc"⟩
def join_tree20 : ScopedC.SourceBundle.Tree Piece := .pair join_file20 join_tree18 join_tree19
theorem join_bound20 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree20 := .pair join_bound18 join_bound19 (by decide +kernel)
def join_file21 : File := ⟨"join_021.inc",include_str "../../bundle-source/join_021.inc"⟩
def join_tree21 : ScopedC.SourceBundle.Tree Piece := .pair join_file21 join_tree17 join_tree20
theorem join_bound21 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree21 := .pair join_bound17 join_bound20 (by decide +kernel)
def join_file22 : File := ⟨"join_022.inc",include_str "../../bundle-source/join_022.inc"⟩
def join_tree22 : ScopedC.SourceBundle.Tree Piece := .pair join_file22 join_tree15 join_tree21
theorem join_bound22 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree22 := .pair join_bound15 join_bound21 (by decide +kernel)
def join_file23 : File := ⟨"join_023.inc",include_str "../../bundle-source/join_023.inc"⟩
def join_tree23 : ScopedC.SourceBundle.Tree Piece := .pair join_file23 join_tree10 join_tree22
theorem join_bound23 : ScopedC.SourceBundle.Tree.Bound Piece.Bound join_tree23 := .pair join_bound10 join_bound22 (by decide +kernel)
def tree : ScopedC.SourceBundle.Tree Piece := join_tree23
theorem bound : ScopedC.SourceBundle.Tree.Bound Piece.Bound tree := join_bound23
def code : List Function := tree.values.flatMap (fun p => match p with | .function f => [f] | _ => [])
theorem code_exact : code = Generated.functions := by rfl
def actualFiles : List File := tree.files ++ [⟨"basis_bundle.cpp",include_str "../../bundle-source/basis_bundle.cpp"⟩]
#print axioms bound
#print axioms code_exact
end SynergyC.Bundle

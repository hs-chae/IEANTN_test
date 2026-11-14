/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact1Row0
namespace ScopedC.SourceBundle.Arrays.Fact1Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(-75),2⟩,⟨6,0,0,(0),0⟩,⟨0,0,0,(72931),10000⟩,⟨0,0,0,(54281),10000⟩,⟨0,0,0,(3),4⟩,⟨0,0,0,(7),8⟩,⟨4,5,0,(0),0⟩,⟨2,4,6,(0),0⟩,⟨3,3,7,(0),0⟩,⟨6,8,0,(0),0⟩,⟨3,2,9,(0),0⟩,⟨0,0,0,(2),1⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(8),1⟩,⟨3,13,4,(0),0⟩,⟨0,0,0,(5),1⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact1_row0_part_000.inc",include_str "../../../../source/fact1_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨4,15,0,(0),0⟩,⟨2,14,16,(0),0⟩,⟨0,0,0,(3),1⟩,⟨5,18,0,(0),0⟩,⟨3,17,19,(0),0⟩,⟨0,0,0,(3000000000000),1⟩,⟨7,21,0,(0),0⟩,⟨3,20,22,(0),0⟩,⟨4,23,0,(0),0⟩,⟨3,11,4,(0),0⟩,⟨4,25,0,(0),0⟩,⟨2,15,26,(0),0⟩,⟨7,22,0,(0),0⟩,⟨3,27,28,(0),0⟩,⟨2,24,29,(0),0⟩,⟨6,30,0,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact1_row0_part_001.inc",include_str "../../../../source/fact1_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨3,12,31,(0),0⟩,⟨5,23,0,(0),0⟩,⟨3,27,33,(0),0⟩,⟨2,12,34,(0),0⟩,⟨4,12,0,(0),0⟩,⟨2,27,36,(0),0⟩,⟨3,27,37,(0),0⟩,⟨3,23,12,(0),0⟩,⟨3,23,39,(0),0⟩,⟨5,40,0,(0),0⟩,⟨3,38,41,(0),0⟩,⟨2,35,42,(0),0⟩,⟨4,11,0,(0),0⟩,⟨2,27,44,(0),0⟩,⟨3,38,45,(0),0⟩,⟨3,23,40,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact1_row0_part_002.inc",include_str "../../../../source/fact1_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact1_row0_join_00024.inc",include_str "../../../../source/fact1_row0_join_00024.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree1 tree2
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound1 bound2 (by decide +kernel)
def joinFile1 : File := ⟨"fact1_row0_join_00025.inc",include_str "../../../../source/fact1_row0_join_00025.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree0 joinTree0
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 joinBound0 (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨5,47,0,(0),0⟩,⟨3,46,48,(0),0⟩,⟨2,43,49,(0),0⟩,⟨4,18,0,(0),0⟩,⟨2,27,51,(0),0⟩,⟨3,46,52,(0),0⟩,⟨3,23,47,(0),0⟩,⟨5,54,0,(0),0⟩,⟨3,53,55,(0),0⟩,⟨2,50,56,(0),0⟩,⟨3,32,57,(0),0⟩,⟨5,20,0,(0),0⟩,⟨3,58,59,(0),0⟩,⟨0,0,0,(0),1⟩,⟨3,22,12,(0),0⟩,⟨3,22,62,(0),0⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact1_row0_part_003.inc",include_str "../../../../source/fact1_row0_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes4 : List ScopedNumerical.Input.Node := [⟨3,11,22,(0),0⟩,⟨2,63,64,(0),0⟩,⟨2,65,11,(0),0⟩,⟨3,61,66,(0),0⟩,⟨2,60,67,(0),0⟩,⟨3,11,68,(0),0⟩,⟨0,0,0,(4),1⟩,⟨8,0,0,(0),0⟩,⟨3,70,71,(0),0⟩,⟨0,0,0,(100),1⟩,⟨3,20,73,(0),0⟩,⟨4,74,0,(0),0⟩,⟨7,73,0,(0),0⟩,⟨3,27,76,(0),0⟩,⟨2,75,77,(0),0⟩,⟨6,78,0,(0),0⟩]
def fragment4 : Fragment := ⟨true,nodes4.map ScopedC.CData.nodeInitializer⟩
def file4 : File := ⟨"fact1_row0_part_004.inc",include_str "../../../../source/fact1_row0_part_004.inc"⟩
def tree4 : Tree Fragment := .leaf file4 fragment4
theorem bound4 : tree4.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes5 : List ScopedNumerical.Input.Node := [⟨3,12,79,(0),0⟩,⟨0,0,0,(-100),1⟩,⟨6,81,0,(0),0⟩,⟨3,61,82,(0),0⟩,⟨2,80,83,(0),0⟩,⟨3,72,84,(0),0⟩,⟨2,69,85,(0),0⟩,⟨3,10,86,(0),0⟩,⟨0,0,0,(6),1⟩,⟨3,61,31,(0),0⟩,⟨3,89,57,(0),0⟩,⟨3,90,59,(0),0⟩,⟨0,0,0,(1),3000000000000⟩,⟨3,92,66,(0),0⟩,⟨2,91,93,(0),0⟩,⟨3,11,94,(0),0⟩]
def fragment5 : Fragment := ⟨true,nodes5.map ScopedC.CData.nodeInitializer⟩
def file5 : File := ⟨"fact1_row0_part_005.inc",include_str "../../../../source/fact1_row0_part_005.inc"⟩
def tree5 : Tree Fragment := .leaf file5 fragment5
theorem bound5 : tree5.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile2 : File := ⟨"fact1_row0_join_00026.inc",include_str "../../../../source/fact1_row0_join_00026.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 tree4 tree5
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair bound4 bound5 (by decide +kernel)
def joinFile3 : File := ⟨"fact1_row0_join_00027.inc",include_str "../../../../source/fact1_row0_join_00027.inc"⟩
def joinTree3 : Tree Fragment := .pair joinFile3 tree3 joinTree2
theorem joinBound3 : joinTree3.Bound (fun f file => renderFragment f = some file.text) := .pair bound3 joinBound2 (by decide +kernel)
def joinFile4 : File := ⟨"fact1_row0_join_00028.inc",include_str "../../../../source/fact1_row0_join_00028.inc"⟩
def joinTree4 : Tree Fragment := .pair joinFile4 joinTree1 joinTree3
theorem joinBound4 : joinTree4.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound1 joinBound3 (by decide +kernel)
def nodes6 : List ScopedNumerical.Input.Node := [⟨3,61,79,(0),0⟩,⟨0,0,0,(10000),1⟩,⟨3,97,82,(0),0⟩,⟨2,96,98,(0),0⟩,⟨3,72,99,(0),0⟩,⟨2,95,100,(0),0⟩,⟨3,88,101,(0),0⟩,⟨2,87,102,(0),0⟩,⟨3,11,9,(0),0⟩,⟨0,0,0,(233),10000⟩,⟨2,22,12,(0),0⟩,⟨3,20,106,(0),0⟩,⟨4,107,0,(0),0⟩,⟨7,106,0,(0),0⟩,⟨3,27,109,(0),0⟩,⟨2,108,110,(0),0⟩]
def fragment6 : Fragment := ⟨true,nodes6.map ScopedC.CData.nodeInitializer⟩
def file6 : File := ⟨"fact1_row0_part_006.inc",include_str "../../../../source/fact1_row0_part_006.inc"⟩
def tree6 : Tree Fragment := .leaf file6 fragment6
theorem bound6 : tree6.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes7 : List ScopedNumerical.Input.Node := [⟨6,111,0,(0),0⟩,⟨3,112,59,(0),0⟩,⟨5,107,0,(0),0⟩,⟨3,27,114,(0),0⟩,⟨2,12,115,(0),0⟩,⟨3,107,12,(0),0⟩,⟨3,107,117,(0),0⟩,⟨5,118,0,(0),0⟩,⟨3,38,119,(0),0⟩,⟨2,116,120,(0),0⟩,⟨3,107,118,(0),0⟩,⟨5,122,0,(0),0⟩,⟨3,46,123,(0),0⟩,⟨2,121,124,(0),0⟩,⟨3,113,125,(0),0⟩,⟨3,105,126,(0),0⟩]
def fragment7 : Fragment := ⟨true,nodes7.map ScopedC.CData.nodeInitializer⟩
def file7 : File := ⟨"fact1_row0_part_007.inc",include_str "../../../../source/fact1_row0_part_007.inc"⟩
def tree7 : Tree Fragment := .leaf file7 fragment7
theorem bound7 : tree7.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes8 : List ScopedNumerical.Input.Node := [⟨0,0,0,(43),2000⟩,⟨2,22,11,(0),0⟩,⟨3,20,129,(0),0⟩,⟨4,130,0,(0),0⟩,⟨7,129,0,(0),0⟩,⟨3,27,132,(0),0⟩,⟨2,131,133,(0),0⟩,⟨6,134,0,(0),0⟩,⟨3,135,59,(0),0⟩,⟨5,130,0,(0),0⟩,⟨3,27,137,(0),0⟩,⟨2,12,138,(0),0⟩,⟨3,130,12,(0),0⟩,⟨3,130,140,(0),0⟩,⟨5,141,0,(0),0⟩,⟨3,38,142,(0),0⟩]
def fragment8 : Fragment := ⟨true,nodes8.map ScopedC.CData.nodeInitializer⟩
def file8 : File := ⟨"fact1_row0_part_008.inc",include_str "../../../../source/fact1_row0_part_008.inc"⟩
def tree8 : Tree Fragment := .leaf file8 fragment8
theorem bound8 : tree8.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile5 : File := ⟨"fact1_row0_join_00029.inc",include_str "../../../../source/fact1_row0_join_00029.inc"⟩
def joinTree5 : Tree Fragment := .pair joinFile5 tree7 tree8
theorem joinBound5 : joinTree5.Bound (fun f file => renderFragment f = some file.text) := .pair bound7 bound8 (by decide +kernel)
def joinFile6 : File := ⟨"fact1_row0_join_00030.inc",include_str "../../../../source/fact1_row0_join_00030.inc"⟩
def joinTree6 : Tree Fragment := .pair joinFile6 tree6 joinTree5
theorem joinBound6 : joinTree6.Bound (fun f file => renderFragment f = some file.text) := .pair bound6 joinBound5 (by decide +kernel)
def nodes9 : List ScopedNumerical.Input.Node := [⟨2,139,143,(0),0⟩,⟨3,130,141,(0),0⟩,⟨5,145,0,(0),0⟩,⟨3,46,146,(0),0⟩,⟨2,144,147,(0),0⟩,⟨3,136,148,(0),0⟩,⟨3,128,149,(0),0⟩,⟨2,127,150,(0),0⟩,⟨0,0,0,(49),1250⟩,⟨2,22,70,(0),0⟩,⟨3,20,153,(0),0⟩,⟨4,154,0,(0),0⟩,⟨7,153,0,(0),0⟩,⟨3,27,156,(0),0⟩,⟨2,155,157,(0),0⟩,⟨6,158,0,(0),0⟩]
def fragment9 : Fragment := ⟨true,nodes9.map ScopedC.CData.nodeInitializer⟩
def file9 : File := ⟨"fact1_row0_part_009.inc",include_str "../../../../source/fact1_row0_part_009.inc"⟩
def tree9 : Tree Fragment := .leaf file9 fragment9
theorem bound9 : tree9.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes10 : List ScopedNumerical.Input.Node := [⟨3,159,59,(0),0⟩,⟨5,154,0,(0),0⟩,⟨3,27,161,(0),0⟩,⟨2,12,162,(0),0⟩,⟨3,154,12,(0),0⟩,⟨3,154,164,(0),0⟩,⟨5,165,0,(0),0⟩,⟨3,38,166,(0),0⟩,⟨2,163,167,(0),0⟩,⟨3,154,165,(0),0⟩,⟨5,169,0,(0),0⟩,⟨3,46,170,(0),0⟩,⟨2,168,171,(0),0⟩,⟨3,160,172,(0),0⟩,⟨3,152,173,(0),0⟩,⟨2,151,174,(0),0⟩]
def fragment10 : Fragment := ⟨true,nodes10.map ScopedC.CData.nodeInitializer⟩
def file10 : File := ⟨"fact1_row0_part_010.inc",include_str "../../../../source/fact1_row0_part_010.inc"⟩
def tree10 : Tree Fragment := .leaf file10 fragment10
theorem bound10 : tree10.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile7 : File := ⟨"fact1_row0_join_00031.inc",include_str "../../../../source/fact1_row0_join_00031.inc"⟩
def joinTree7 : Tree Fragment := .pair joinFile7 tree9 tree10
theorem joinBound7 : joinTree7.Bound (fun f file => renderFragment f = some file.text) := .pair bound9 bound10 (by decide +kernel)
def nodes11 : List ScopedNumerical.Input.Node := [⟨3,104,175,(0),0⟩,⟨4,176,0,(0),0⟩,⟨2,103,177,(0),0⟩,⟨3,1,178,(0),0⟩,⟨2,91,67,(0),0⟩,⟨3,11,180,(0),0⟩,⟨2,96,83,(0),0⟩,⟨3,72,182,(0),0⟩,⟨2,181,183,(0),0⟩,⟨3,1,184,(0),0⟩,⟨0,0,0,(100000000001),1000000000⟩,⟨3,186,12,(0),0⟩,⟨3,186,187,(0),0⟩,⟨3,11,71,(0),0⟩,⟨5,189,0,(0),0⟩,⟨3,188,190,(0),0⟩]
def fragment11 : Fragment := ⟨true,nodes11.map ScopedC.CData.nodeInitializer⟩
def file11 : File := ⟨"fact1_row0_part_011.inc",include_str "../../../../source/fact1_row0_part_011.inc"⟩
def tree11 : Tree Fragment := .leaf file11 fragment11
theorem bound11 : tree11.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes12 : List ScopedNumerical.Input.Node := [⟨5,71,0,(0),0⟩,⟨3,12,192,(0),0⟩,⟨2,11,193,(0),0⟩,⟨3,194,186,(0),0⟩,⟨2,191,195,(0),0⟩,⟨3,1,196,(0),0⟩,⟨0,0,0,(1),1000000000000⟩,⟨2,197,198,(0),0⟩,⟨2,185,199,(0),0⟩,⟨2,179,200,(0),0⟩]
def fragment12 : Fragment := ⟨true,nodes12.map ScopedC.CData.nodeInitializer⟩
def file12 : File := ⟨"fact1_row0_part_012.inc",include_str "../../../../source/fact1_row0_part_012.inc"⟩
def tree12 : Tree Fragment := .leaf file12 fragment12
theorem bound12 : tree12.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile8 : File := ⟨"fact1_row0_join_00032.inc",include_str "../../../../source/fact1_row0_join_00032.inc"⟩
def joinTree8 : Tree Fragment := .pair joinFile8 tree11 tree12
theorem joinBound8 : joinTree8.Bound (fun f file => renderFragment f = some file.text) := .pair bound11 bound12 (by decide +kernel)
def joinFile9 : File := ⟨"fact1_row0_join_00033.inc",include_str "../../../../source/fact1_row0_join_00033.inc"⟩
def joinTree9 : Tree Fragment := .pair joinFile9 joinTree7 joinTree8
theorem joinBound9 : joinTree9.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound7 joinBound8 (by decide +kernel)
def joinFile10 : File := ⟨"fact1_row0_join_00034.inc",include_str "../../../../source/fact1_row0_join_00034.inc"⟩
def joinTree10 : Tree Fragment := .pair joinFile10 joinTree6 joinTree9
theorem joinBound10 : joinTree10.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound6 joinBound9 (by decide +kernel)
def joinFile11 : File := ⟨"fact1_row0_join_00035.inc",include_str "../../../../source/fact1_row0_join_00035.inc"⟩
def joinTree11 : Tree Fragment := .pair joinFile11 joinTree4 joinTree10
theorem joinBound11 : joinTree11.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound4 joinBound10 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact1Row0.nodes := by rfl
def body : Tree Fragment := joinTree11
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound11
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact1Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12,nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12]
def actual : File := ⟨"fact1_row0_array.inc",include_str "../../../../source/fact1_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact1_row0" ScopedNumerical.InputData.Fact1Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact1Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact1Row0

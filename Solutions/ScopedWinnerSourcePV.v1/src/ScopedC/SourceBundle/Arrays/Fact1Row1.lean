/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact1Row1
namespace ScopedC.SourceBundle.Arrays.Fact1Row1
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(300),1⟩,⟨0,0,0,(3),4⟩,⟨1,0,0,(0),0⟩,⟨0,0,0,(65536),1⟩,⟨5,3,0,(0),0⟩,⟨3,2,4,(0),0⟩,⟨2,1,5,(0),0⟩,⟨0,0,0,(1),65536⟩,⟨2,6,7,(0),0⟩,⟨0,0,0,(7),8⟩,⟨4,9,0,(0),0⟩,⟨2,8,10,(0),0⟩,⟨3,0,11,(0),0⟩,⟨6,12,0,(0),0⟩,⟨2,6,10,(0),0⟩,⟨3,0,14,(0),0⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact1_row1_part_000.inc",include_str "../../../../source/fact1_row1_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨6,15,0,(0),0⟩,⟨4,16,0,(0),0⟩,⟨2,13,17,(0),0⟩,⟨0,0,0,(72931),10000⟩,⟨0,0,0,(54281),10000⟩,⟨3,20,14,(0),0⟩,⟨6,21,0,(0),0⟩,⟨3,19,22,(0),0⟩,⟨0,0,0,(2),1⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(8),1⟩,⟨3,26,6,(0),0⟩,⟨0,0,0,(5),1⟩,⟨4,28,0,(0),0⟩,⟨2,27,29,(0),0⟩,⟨0,0,0,(3),1⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact1_row1_part_001.inc",include_str "../../../../source/fact1_row1_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨5,31,0,(0),0⟩,⟨3,30,32,(0),0⟩,⟨0,0,0,(3000000000000),1⟩,⟨7,34,0,(0),0⟩,⟨3,33,35,(0),0⟩,⟨4,36,0,(0),0⟩,⟨3,24,6,(0),0⟩,⟨4,38,0,(0),0⟩,⟨2,28,39,(0),0⟩,⟨7,35,0,(0),0⟩,⟨3,40,41,(0),0⟩,⟨2,37,42,(0),0⟩,⟨6,43,0,(0),0⟩,⟨3,25,44,(0),0⟩,⟨5,36,0,(0),0⟩,⟨3,40,46,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact1_row1_part_002.inc",include_str "../../../../source/fact1_row1_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact1_row1_join_00036.inc",include_str "../../../../source/fact1_row1_join_00036.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree1 tree2
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound1 bound2 (by decide +kernel)
def joinFile1 : File := ⟨"fact1_row1_join_00037.inc",include_str "../../../../source/fact1_row1_join_00037.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree0 joinTree0
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 joinBound0 (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨2,25,47,(0),0⟩,⟨4,25,0,(0),0⟩,⟨2,40,49,(0),0⟩,⟨3,40,50,(0),0⟩,⟨3,36,25,(0),0⟩,⟨3,36,52,(0),0⟩,⟨5,53,0,(0),0⟩,⟨3,51,54,(0),0⟩,⟨2,48,55,(0),0⟩,⟨4,24,0,(0),0⟩,⟨2,40,57,(0),0⟩,⟨3,51,58,(0),0⟩,⟨3,36,53,(0),0⟩,⟨5,60,0,(0),0⟩,⟨3,59,61,(0),0⟩,⟨2,56,62,(0),0⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact1_row1_part_003.inc",include_str "../../../../source/fact1_row1_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes4 : List ScopedNumerical.Input.Node := [⟨4,31,0,(0),0⟩,⟨2,40,64,(0),0⟩,⟨3,59,65,(0),0⟩,⟨3,36,60,(0),0⟩,⟨5,67,0,(0),0⟩,⟨3,66,68,(0),0⟩,⟨2,63,69,(0),0⟩,⟨3,45,70,(0),0⟩,⟨5,33,0,(0),0⟩,⟨3,71,72,(0),0⟩,⟨0,0,0,(0),1⟩,⟨3,35,25,(0),0⟩,⟨3,35,75,(0),0⟩,⟨3,24,35,(0),0⟩,⟨2,76,77,(0),0⟩,⟨2,78,24,(0),0⟩]
def fragment4 : Fragment := ⟨true,nodes4.map ScopedC.CData.nodeInitializer⟩
def file4 : File := ⟨"fact1_row1_part_004.inc",include_str "../../../../source/fact1_row1_part_004.inc"⟩
def tree4 : Tree Fragment := .leaf file4 fragment4
theorem bound4 : tree4.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes5 : List ScopedNumerical.Input.Node := [⟨3,74,79,(0),0⟩,⟨2,73,80,(0),0⟩,⟨3,24,81,(0),0⟩,⟨0,0,0,(4),1⟩,⟨8,0,0,(0),0⟩,⟨3,83,84,(0),0⟩,⟨0,0,0,(100),1⟩,⟨3,33,86,(0),0⟩,⟨4,87,0,(0),0⟩,⟨7,86,0,(0),0⟩,⟨3,40,89,(0),0⟩,⟨2,88,90,(0),0⟩,⟨6,91,0,(0),0⟩,⟨3,25,92,(0),0⟩,⟨0,0,0,(-100),1⟩,⟨6,94,0,(0),0⟩]
def fragment5 : Fragment := ⟨true,nodes5.map ScopedC.CData.nodeInitializer⟩
def file5 : File := ⟨"fact1_row1_part_005.inc",include_str "../../../../source/fact1_row1_part_005.inc"⟩
def tree5 : Tree Fragment := .leaf file5 fragment5
theorem bound5 : tree5.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile2 : File := ⟨"fact1_row1_join_00038.inc",include_str "../../../../source/fact1_row1_join_00038.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 tree4 tree5
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair bound4 bound5 (by decide +kernel)
def joinFile3 : File := ⟨"fact1_row1_join_00039.inc",include_str "../../../../source/fact1_row1_join_00039.inc"⟩
def joinTree3 : Tree Fragment := .pair joinFile3 tree3 joinTree2
theorem joinBound3 : joinTree3.Bound (fun f file => renderFragment f = some file.text) := .pair bound3 joinBound2 (by decide +kernel)
def joinFile4 : File := ⟨"fact1_row1_join_00040.inc",include_str "../../../../source/fact1_row1_join_00040.inc"⟩
def joinTree4 : Tree Fragment := .pair joinFile4 joinTree1 joinTree3
theorem joinBound4 : joinTree4.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound1 joinBound3 (by decide +kernel)
def nodes6 : List ScopedNumerical.Input.Node := [⟨3,74,95,(0),0⟩,⟨2,93,96,(0),0⟩,⟨3,85,97,(0),0⟩,⟨2,82,98,(0),0⟩,⟨3,23,99,(0),0⟩,⟨0,0,0,(6),1⟩,⟨3,74,44,(0),0⟩,⟨3,102,70,(0),0⟩,⟨3,103,72,(0),0⟩,⟨0,0,0,(1),3000000000000⟩,⟨3,105,79,(0),0⟩,⟨2,104,106,(0),0⟩,⟨3,24,107,(0),0⟩,⟨3,74,92,(0),0⟩,⟨0,0,0,(10000),1⟩,⟨3,110,95,(0),0⟩]
def fragment6 : Fragment := ⟨true,nodes6.map ScopedC.CData.nodeInitializer⟩
def file6 : File := ⟨"fact1_row1_part_006.inc",include_str "../../../../source/fact1_row1_part_006.inc"⟩
def tree6 : Tree Fragment := .leaf file6 fragment6
theorem bound6 : tree6.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes7 : List ScopedNumerical.Input.Node := [⟨2,109,111,(0),0⟩,⟨3,85,112,(0),0⟩,⟨2,108,113,(0),0⟩,⟨3,101,114,(0),0⟩,⟨2,100,115,(0),0⟩,⟨3,24,22,(0),0⟩,⟨0,0,0,(233),10000⟩,⟨2,35,25,(0),0⟩,⟨3,33,119,(0),0⟩,⟨4,120,0,(0),0⟩,⟨7,119,0,(0),0⟩,⟨3,40,122,(0),0⟩,⟨2,121,123,(0),0⟩,⟨6,124,0,(0),0⟩,⟨3,125,72,(0),0⟩,⟨5,120,0,(0),0⟩]
def fragment7 : Fragment := ⟨true,nodes7.map ScopedC.CData.nodeInitializer⟩
def file7 : File := ⟨"fact1_row1_part_007.inc",include_str "../../../../source/fact1_row1_part_007.inc"⟩
def tree7 : Tree Fragment := .leaf file7 fragment7
theorem bound7 : tree7.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes8 : List ScopedNumerical.Input.Node := [⟨3,40,127,(0),0⟩,⟨2,25,128,(0),0⟩,⟨3,120,25,(0),0⟩,⟨3,120,130,(0),0⟩,⟨5,131,0,(0),0⟩,⟨3,51,132,(0),0⟩,⟨2,129,133,(0),0⟩,⟨3,120,131,(0),0⟩,⟨5,135,0,(0),0⟩,⟨3,59,136,(0),0⟩,⟨2,134,137,(0),0⟩,⟨3,126,138,(0),0⟩,⟨3,118,139,(0),0⟩,⟨0,0,0,(43),2000⟩,⟨2,35,24,(0),0⟩,⟨3,33,142,(0),0⟩]
def fragment8 : Fragment := ⟨true,nodes8.map ScopedC.CData.nodeInitializer⟩
def file8 : File := ⟨"fact1_row1_part_008.inc",include_str "../../../../source/fact1_row1_part_008.inc"⟩
def tree8 : Tree Fragment := .leaf file8 fragment8
theorem bound8 : tree8.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile5 : File := ⟨"fact1_row1_join_00041.inc",include_str "../../../../source/fact1_row1_join_00041.inc"⟩
def joinTree5 : Tree Fragment := .pair joinFile5 tree7 tree8
theorem joinBound5 : joinTree5.Bound (fun f file => renderFragment f = some file.text) := .pair bound7 bound8 (by decide +kernel)
def joinFile6 : File := ⟨"fact1_row1_join_00042.inc",include_str "../../../../source/fact1_row1_join_00042.inc"⟩
def joinTree6 : Tree Fragment := .pair joinFile6 tree6 joinTree5
theorem joinBound6 : joinTree6.Bound (fun f file => renderFragment f = some file.text) := .pair bound6 joinBound5 (by decide +kernel)
def nodes9 : List ScopedNumerical.Input.Node := [⟨4,143,0,(0),0⟩,⟨7,142,0,(0),0⟩,⟨3,40,145,(0),0⟩,⟨2,144,146,(0),0⟩,⟨6,147,0,(0),0⟩,⟨3,148,72,(0),0⟩,⟨5,143,0,(0),0⟩,⟨3,40,150,(0),0⟩,⟨2,25,151,(0),0⟩,⟨3,143,25,(0),0⟩,⟨3,143,153,(0),0⟩,⟨5,154,0,(0),0⟩,⟨3,51,155,(0),0⟩,⟨2,152,156,(0),0⟩,⟨3,143,154,(0),0⟩,⟨5,158,0,(0),0⟩]
def fragment9 : Fragment := ⟨true,nodes9.map ScopedC.CData.nodeInitializer⟩
def file9 : File := ⟨"fact1_row1_part_009.inc",include_str "../../../../source/fact1_row1_part_009.inc"⟩
def tree9 : Tree Fragment := .leaf file9 fragment9
theorem bound9 : tree9.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes10 : List ScopedNumerical.Input.Node := [⟨3,59,159,(0),0⟩,⟨2,157,160,(0),0⟩,⟨3,149,161,(0),0⟩,⟨3,141,162,(0),0⟩,⟨2,140,163,(0),0⟩,⟨0,0,0,(49),1250⟩,⟨2,35,83,(0),0⟩,⟨3,33,166,(0),0⟩,⟨4,167,0,(0),0⟩,⟨7,166,0,(0),0⟩,⟨3,40,169,(0),0⟩,⟨2,168,170,(0),0⟩,⟨6,171,0,(0),0⟩,⟨3,172,72,(0),0⟩,⟨5,167,0,(0),0⟩,⟨3,40,174,(0),0⟩]
def fragment10 : Fragment := ⟨true,nodes10.map ScopedC.CData.nodeInitializer⟩
def file10 : File := ⟨"fact1_row1_part_010.inc",include_str "../../../../source/fact1_row1_part_010.inc"⟩
def tree10 : Tree Fragment := .leaf file10 fragment10
theorem bound10 : tree10.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile7 : File := ⟨"fact1_row1_join_00043.inc",include_str "../../../../source/fact1_row1_join_00043.inc"⟩
def joinTree7 : Tree Fragment := .pair joinFile7 tree9 tree10
theorem joinBound7 : joinTree7.Bound (fun f file => renderFragment f = some file.text) := .pair bound9 bound10 (by decide +kernel)
def nodes11 : List ScopedNumerical.Input.Node := [⟨2,25,175,(0),0⟩,⟨3,167,25,(0),0⟩,⟨3,167,177,(0),0⟩,⟨5,178,0,(0),0⟩,⟨3,51,179,(0),0⟩,⟨2,176,180,(0),0⟩,⟨3,167,178,(0),0⟩,⟨5,182,0,(0),0⟩,⟨3,59,183,(0),0⟩,⟨2,181,184,(0),0⟩,⟨3,173,185,(0),0⟩,⟨3,165,186,(0),0⟩,⟨2,164,187,(0),0⟩,⟨3,117,188,(0),0⟩,⟨4,189,0,(0),0⟩,⟨2,116,190,(0),0⟩]
def fragment11 : Fragment := ⟨true,nodes11.map ScopedC.CData.nodeInitializer⟩
def file11 : File := ⟨"fact1_row1_part_011.inc",include_str "../../../../source/fact1_row1_part_011.inc"⟩
def tree11 : Tree Fragment := .leaf file11 fragment11
theorem bound11 : tree11.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes12 : List ScopedNumerical.Input.Node := [⟨3,18,191,(0),0⟩]
def fragment12 : Fragment := ⟨true,nodes12.map ScopedC.CData.nodeInitializer⟩
def file12 : File := ⟨"fact1_row1_part_012.inc",include_str "../../../../source/fact1_row1_part_012.inc"⟩
def tree12 : Tree Fragment := .leaf file12 fragment12
theorem bound12 : tree12.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile8 : File := ⟨"fact1_row1_join_00044.inc",include_str "../../../../source/fact1_row1_join_00044.inc"⟩
def joinTree8 : Tree Fragment := .pair joinFile8 tree11 tree12
theorem joinBound8 : joinTree8.Bound (fun f file => renderFragment f = some file.text) := .pair bound11 bound12 (by decide +kernel)
def joinFile9 : File := ⟨"fact1_row1_join_00045.inc",include_str "../../../../source/fact1_row1_join_00045.inc"⟩
def joinTree9 : Tree Fragment := .pair joinFile9 joinTree7 joinTree8
theorem joinBound9 : joinTree9.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound7 joinBound8 (by decide +kernel)
def joinFile10 : File := ⟨"fact1_row1_join_00046.inc",include_str "../../../../source/fact1_row1_join_00046.inc"⟩
def joinTree10 : Tree Fragment := .pair joinFile10 joinTree6 joinTree9
theorem joinBound10 : joinTree10.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound6 joinBound9 (by decide +kernel)
def joinFile11 : File := ⟨"fact1_row1_join_00047.inc",include_str "../../../../source/fact1_row1_join_00047.inc"⟩
def joinTree11 : Tree Fragment := .pair joinFile11 joinTree4 joinTree10
theorem joinBound11 : joinTree11.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound4 joinBound10 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact1Row1.nodes := by rfl
def body : Tree Fragment := joinTree11
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound11
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact1Row1.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12,nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12]
def actual : File := ⟨"fact1_row1_array.inc",include_str "../../../../source/fact1_row1_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact1_row1" ScopedNumerical.InputData.Fact1Row1.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact1Row1.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact1Row1

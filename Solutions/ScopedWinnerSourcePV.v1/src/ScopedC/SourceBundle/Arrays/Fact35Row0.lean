/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact35Row0
namespace ScopedC.SourceBundle.Arrays.Fact35Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(601),625⟩,⟨0,0,0,(601),2500⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(3599),10000⟩,⟨0,0,0,(3000000000000),1⟩,⟨0,0,0,(0),1⟩,⟨6,5,0,(0),0⟩,⟨3,4,6,(0),0⟩,⟨7,7,0,(0),0⟩,⟨5,8,0,(0),0⟩,⟨3,3,9,(0),0⟩,⟨2,2,10,(0),0⟩,⟨5,7,0,(0),0⟩,⟨3,11,12,(0),0⟩,⟨3,13,13,(0),0⟩,⟨3,1,14,(0),0⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact35_row0_part_000.inc",include_str "../../../../source/fact35_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨6,15,0,(0),0⟩,⟨3,0,16,(0),0⟩,⟨8,0,0,(0),0⟩,⟨0,0,0,(2),3⟩,⟨0,0,0,(6),5⟩,⟨7,20,0,(0),0⟩,⟨0,0,0,(2),1⟩,⟨5,22,0,(0),0⟩,⟨3,21,23,(0),0⟩,⟨6,24,0,(0),0⟩,⟨3,19,25,(0),0⟩,⟨2,2,26,(0),0⟩,⟨7,27,0,(0),0⟩,⟨3,28,23,(0),0⟩,⟨6,29,0,(0),0⟩,⟨3,18,30,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact35_row0_part_001.inc",include_str "../../../../source/fact35_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact35_row0_join_00171.inc",include_str "../../../../source/fact35_row0_join_00171.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree0 tree1
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 bound1 (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨0,0,0,(529),1000⟩,⟨3,31,32,(0),0⟩,⟨0,0,0,(3599),5000⟩,⟨5,34,0,(0),0⟩,⟨3,33,35,(0),0⟩,⟨3,34,9,(0),0⟩,⟨2,2,37,(0),0⟩,⟨3,38,38,(0),0⟩,⟨3,36,39,(0),0⟩,⟨0,0,0,(1040111),2500000⟩,⟨3,41,9,(0),0⟩,⟨6,42,0,(0),0⟩,⟨3,40,43,(0),0⟩,⟨0,0,0,(3599),2000⟩,⟨6,3,0,(0),0⟩,⟨3,45,46,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact35_row0_part_002.inc",include_str "../../../../source/fact35_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨5,47,0,(0),0⟩,⟨3,32,48,(0),0⟩,⟨3,11,11,(0),0⟩,⟨3,49,50,(0),0⟩,⟨0,0,0,(121),200⟩,⟨0,0,0,(-3599),5000⟩,⟨6,53,0,(0),0⟩,⟨3,52,54,(0),0⟩,⟨3,8,8,(0),0⟩,⟨5,56,0,(0),0⟩,⟨3,55,57,(0),0⟩,⟨2,51,58,(0),0⟩,⟨3,59,18,(0),0⟩,⟨3,60,30,(0),0⟩,⟨3,61,12,(0),0⟩,⟨2,44,62,(0),0⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact35_row0_part_003.inc",include_str "../../../../source/fact35_row0_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes4 : List ScopedNumerical.Input.Node := [⟨0,0,0,(601),1250⟩,⟨5,64,0,(0),0⟩,⟨3,63,65,(0),0⟩,⟨7,18,0,(0),0⟩,⟨3,67,23,(0),0⟩,⟨6,68,0,(0),0⟩,⟨3,59,69,(0),0⟩,⟨7,1,0,(0),0⟩,⟨3,71,23,(0),0⟩,⟨6,72,0,(0),0⟩,⟨3,0,73,(0),0⟩,⟨5,74,0,(0),0⟩,⟨3,70,75,(0),0⟩,⟨2,66,76,(0),0⟩,⟨3,17,77,(0),0⟩]
def fragment4 : Fragment := ⟨true,nodes4.map ScopedC.CData.nodeInitializer⟩
def file4 : File := ⟨"fact35_row0_part_004.inc",include_str "../../../../source/fact35_row0_part_004.inc"⟩
def tree4 : Tree Fragment := .leaf file4 fragment4
theorem bound4 : tree4.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile1 : File := ⟨"fact35_row0_join_00172.inc",include_str "../../../../source/fact35_row0_join_00172.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree3 tree4
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound3 bound4 (by decide +kernel)
def joinFile2 : File := ⟨"fact35_row0_join_00173.inc",include_str "../../../../source/fact35_row0_join_00173.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 tree2 joinTree1
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair bound2 joinBound1 (by decide +kernel)
def joinFile3 : File := ⟨"fact35_row0_join_00174.inc",include_str "../../../../source/fact35_row0_join_00174.inc"⟩
def joinTree3 : Tree Fragment := .pair joinFile3 joinTree0 joinTree2
theorem joinBound3 : joinTree3.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound0 joinBound2 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3,nodes4]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact35Row0.nodes := by rfl
def body : Tree Fragment := joinTree3
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound3
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3,fragment4] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact35Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,fragment4,nodes0,nodes1,nodes2,nodes3,nodes4]
def actual : File := ⟨"fact35_row0_array.inc",include_str "../../../../source/fact35_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact35_row0" ScopedNumerical.InputData.Fact35Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact35Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact35Row0

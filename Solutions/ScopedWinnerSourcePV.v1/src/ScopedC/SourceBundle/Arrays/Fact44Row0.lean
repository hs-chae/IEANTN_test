/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact44Row0
namespace ScopedC.SourceBundle.Arrays.Fact44Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(2),1⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(507),2000⟩,⟨3,0,2,(0),0⟩,⟨2,1,3,(0),0⟩,⟨3,0,4,(0),0⟩,⟨8,0,0,(0),0⟩,⟨3,0,6,(0),0⟩,⟨2,1,2,(0),0⟩,⟨3,7,8,(0),0⟩,⟨2,5,9,(0),0⟩,⟨7,0,0,(0),0⟩,⟨5,11,0,(0),0⟩,⟨3,10,12,(0),0⟩,⟨3,6,12,(0),0⟩,⟨0,0,0,(227),1⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact44_row0_part_000.inc",include_str "../../../../source/fact44_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨7,15,0,(0),0⟩,⟨0,0,0,(675),1⟩,⟨7,17,0,(0),0⟩,⟨2,16,18,(0),0⟩,⟨0,0,0,(1000000000),1⟩,⟨7,20,0,(0),0⟩,⟨3,8,21,(0),0⟩,⟨3,2,21,(0),0⟩,⟨6,23,0,(0),0⟩,⟨3,2,24,(0),0⟩,⟨5,25,0,(0),0⟩,⟨3,22,26,(0),0⟩,⟨5,23,0,(0),0⟩,⟨2,1,28,(0),0⟩,⟨5,21,0,(0),0⟩,⟨2,29,30,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact44_row0_part_001.inc",include_str "../../../../source/fact44_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact44_row0_join_00187.inc",include_str "../../../../source/fact44_row0_join_00187.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree0 tree1
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 bound1 (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨0,0,0,(7),1⟩,⟨3,32,2,(0),0⟩,⟨0,0,0,(12),1⟩,⟨3,34,8,(0),0⟩,⟨3,35,20,(0),0⟩,⟨3,36,21,(0),0⟩,⟨5,37,0,(0),0⟩,⟨3,33,38,(0),0⟩,⟨2,31,39,(0),0⟩,⟨3,27,40,(0),0⟩,⟨3,41,41,(0),0⟩,⟨4,42,0,(0),0⟩,⟨2,1,43,(0),0⟩,⟨7,44,0,(0),0⟩,⟨3,0,45,(0),0⟩,⟨4,46,0,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact44_row0_part_002.inc",include_str "../../../../source/fact44_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨2,19,47,(0),0⟩,⟨3,14,48,(0),0⟩,⟨2,49,6,(0),0⟩,⟨0,0,0,(3000000000000),1⟩,⟨7,51,0,(0),0⟩,⟨5,52,0,(0),0⟩,⟨3,50,53,(0),0⟩,⟨2,13,54,(0),0⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact44_row0_part_003.inc",include_str "../../../../source/fact44_row0_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile1 : File := ⟨"fact44_row0_join_00188.inc",include_str "../../../../source/fact44_row0_join_00188.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree2 tree3
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound2 bound3 (by decide +kernel)
def joinFile2 : File := ⟨"fact44_row0_join_00189.inc",include_str "../../../../source/fact44_row0_join_00189.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 joinTree0 joinTree1
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound0 joinBound1 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact44Row0.nodes := by rfl
def body : Tree Fragment := joinTree2
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound2
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact44Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,nodes0,nodes1,nodes2,nodes3]
def actual : File := ⟨"fact44_row0_array.inc",include_str "../../../../source/fact44_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact44_row0" ScopedNumerical.InputData.Fact44Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact44Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact44Row0

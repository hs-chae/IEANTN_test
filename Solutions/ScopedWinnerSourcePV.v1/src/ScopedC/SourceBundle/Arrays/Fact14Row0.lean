/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact14Row0
namespace ScopedC.SourceBundle.Arrays.Fact14Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(1),2⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(3000000000000),1⟩,⟨4,1,0,(0),0⟩,⟨2,2,3,(0),0⟩,⟨5,4,0,(0),0⟩,⟨4,5,0,(0),0⟩,⟨2,1,6,(0),0⟩,⟨3,7,7,(0),0⟩,⟨5,8,0,(0),0⟩,⟨3,0,9,(0),0⟩,⟨0,0,0,(601),2500⟩,⟨0,0,0,(1),4⟩,⟨0,0,0,(12463),10000⟩,⟨7,13,0,(0),0⟩,⟨3,12,14,(0),0⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact14_row0_part_000.inc",include_str "../../../../source/fact14_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨0,0,0,(3),4⟩,⟨0,0,0,(71843),10000⟩,⟨7,17,0,(0),0⟩,⟨3,16,18,(0),0⟩,⟨2,15,19,(0),0⟩,⟨2,11,20,(0),0⟩,⟨0,0,0,(25521),20000⟩,⟨0,0,0,(4),3⟩,⟨0,0,0,(12463),71843⟩,⟨0,0,0,(-7349),3750⟩,⟨6,25,0,(0),0⟩,⟨3,24,26,(0),0⟩,⟨2,23,27,(0),0⟩,⟨3,22,28,(0),0⟩,⟨2,21,29,(0),0⟩,⟨6,30,0,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact14_row0_part_001.inc",include_str "../../../../source/fact14_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨3,10,31,(0),0⟩,⟨0,0,0,(2),1⟩,⟨8,0,0,(0),0⟩,⟨3,33,34,(0),0⟩,⟨0,0,0,(3681),10000⟩,⟨3,35,36,(0),0⟩,⟨5,37,0,(0),0⟩,⟨3,32,38,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact14_row0_part_002.inc",include_str "../../../../source/fact14_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact14_row0_join_00157.inc",include_str "../../../../source/fact14_row0_join_00157.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree1 tree2
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound1 bound2 (by decide +kernel)
def joinFile1 : File := ⟨"fact14_row0_join_00158.inc",include_str "../../../../source/fact14_row0_join_00158.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree0 joinTree0
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 joinBound0 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact14Row0.nodes := by rfl
def body : Tree Fragment := joinTree1
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound1
theorem values_exact : body.values = [fragment0,fragment1,fragment2] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact14Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,nodes0,nodes1,nodes2]
def actual : File := ⟨"fact14_row0_array.inc",include_str "../../../../source/fact14_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact14_row0" ScopedNumerical.InputData.Fact14Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact14Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact14Row0

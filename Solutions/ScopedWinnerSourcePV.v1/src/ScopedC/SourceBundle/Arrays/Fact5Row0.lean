/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact5Row0
namespace ScopedC.SourceBundle.Arrays.Fact5Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(5),2048⟩,⟨0,0,0,(2),1⟩,⟨0,0,0,(-20),1⟩,⟨1,0,0,(0),0⟩,⟨3,0,3,(0),0⟩,⟨2,2,4,(0),0⟩,⟨2,5,0,(0),0⟩,⟨3,1,6,(0),0⟩,⟨0,0,0,(601),2500⟩,⟨3,1,5,(0),0⟩,⟨6,9,0,(0),0⟩,⟨3,8,10,(0),0⟩,⟨4,11,0,(0),0⟩,⟨2,7,12,(0),0⟩,⟨6,13,0,(0),0⟩,⟨0,0,0,(643179),1000000⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact5_row0_part_000.inc",include_str "../../../../source/fact5_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨6,6,0,(0),0⟩,⟨3,15,16,(0),0⟩,⟨0,0,0,(43091),500000⟩,⟨2,17,18,(0),0⟩,⟨7,19,0,(0),0⟩,⟨5,1,0,(0),0⟩,⟨3,20,21,(0),0⟩,⟨6,22,0,(0),0⟩,⟨0,0,0,(6),1⟩,⟨5,24,0,(0),0⟩,⟨3,6,25,(0),0⟩,⟨6,26,0,(0),0⟩,⟨0,0,0,(1),1⟩,⟨0,0,0,(0),1⟩,⟨3,29,5,(0),0⟩,⟨0,0,0,(29729633),1000000⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact5_row0_part_001.inc",include_str "../../../../source/fact5_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨5,31,0,(0),0⟩,⟨3,30,32,(0),0⟩,⟨2,28,33,(0),0⟩,⟨3,27,34,(0),0⟩,⟨0,0,0,(109037),100000000⟩,⟨2,35,36,(0),0⟩,⟨3,23,37,(0),0⟩,⟨0,0,0,(7117),100000000⟩,⟨3,6,21,(0),0⟩,⟨6,40,0,(0),0⟩,⟨3,39,41,(0),0⟩,⟨2,38,42,(0),0⟩,⟨3,43,43,(0),0⟩,⟨3,14,44,(0),0⟩,⟨3,0,45,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact5_row0_part_002.inc",include_str "../../../../source/fact5_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact5_row0_join_00139.inc",include_str "../../../../source/fact5_row0_join_00139.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree1 tree2
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound1 bound2 (by decide +kernel)
def joinFile1 : File := ⟨"fact5_row0_join_00140.inc",include_str "../../../../source/fact5_row0_join_00140.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree0 joinTree0
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 joinBound0 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact5Row0.nodes := by rfl
def body : Tree Fragment := joinTree1
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound1
theorem values_exact : body.values = [fragment0,fragment1,fragment2] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact5Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,nodes0,nodes1,nodes2]
def actual : File := ⟨"fact5_row0_array.inc",include_str "../../../../source/fact5_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact5_row0" ScopedNumerical.InputData.Fact5Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact5Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact5Row0

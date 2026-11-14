/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact48Row0
namespace ScopedC.SourceBundle.Arrays.Fact48Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(1),1⟩,⟨0,0,0,(1237),1000⟩,⟨4,0,0,(0),0⟩,⟨2,1,2,(0),0⟩,⟨2,0,3,(0),0⟩,⟨0,0,0,(3000000000000),1⟩,⟨7,5,0,(0),0⟩,⟨3,4,6,(0),0⟩,⟨3,3,6,(0),0⟩,⟨6,8,0,(0),0⟩,⟨3,3,9,(0),0⟩,⟨5,10,0,(0),0⟩,⟨3,7,11,(0),0⟩,⟨5,8,0,(0),0⟩,⟨2,0,13,(0),0⟩,⟨5,6,0,(0),0⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact48_row0_part_000.inc",include_str "../../../../source/fact48_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨2,14,15,(0),0⟩,⟨0,0,0,(7),1⟩,⟨3,17,3,(0),0⟩,⟨0,0,0,(12),1⟩,⟨3,19,4,(0),0⟩,⟨3,20,5,(0),0⟩,⟨3,21,6,(0),0⟩,⟨5,22,0,(0),0⟩,⟨3,18,23,(0),0⟩,⟨2,16,24,(0),0⟩,⟨3,12,25,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact48_row0_part_001.inc",include_str "../../../../source/fact48_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact48_row0_join_00195.inc",include_str "../../../../source/fact48_row0_join_00195.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree0 tree1
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 bound1 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact48Row0.nodes := by rfl
def body : Tree Fragment := joinTree0
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound0
theorem values_exact : body.values = [fragment0,fragment1] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact48Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,nodes0,nodes1]
def actual : File := ⟨"fact48_row0_array.inc",include_str "../../../../source/fact48_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact48_row0" ScopedNumerical.InputData.Fact48Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact48Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact48Row0

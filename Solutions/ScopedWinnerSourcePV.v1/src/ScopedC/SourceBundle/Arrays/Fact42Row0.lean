/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact42Row0
namespace ScopedC.SourceBundle.Arrays.Fact42Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(2),1⟩,⟨0,0,0,(71843),12463⟩,⟨7,1,0,(0),0⟩,⟨3,0,2,(0),0⟩,⟨0,0,0,(3599),2500⟩,⟨0,0,0,(4),3⟩,⟨0,0,0,(12463),71843⟩,⟨0,0,0,(-7349),3750⟩,⟨6,7,0,(0),0⟩,⟨3,6,8,(0),0⟩,⟨2,5,9,(0),0⟩,⟨3,4,10,(0),0⟩,⟨2,3,11,(0),0⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact42_row0_part_000.inc",include_str "../../../../source/fact42_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact42Row0.nodes := by rfl
def body : Tree Fragment := tree0
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := bound0
theorem values_exact : body.values = [fragment0] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact42Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,nodes0]
def actual : File := ⟨"fact42_row0_array.inc",include_str "../../../../source/fact42_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact42_row0" ScopedNumerical.InputData.Fact42Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact42Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact42Row0

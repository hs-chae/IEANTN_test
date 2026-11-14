/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact45Row0
namespace ScopedC.SourceBundle.Arrays.Fact45Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(2),1⟩,⟨0,0,0,(3000000000000),1⟩,⟨7,1,0,(0),0⟩,⟨3,2,2,(0),0⟩,⟨3,0,3,(0),0⟩,⟨0,0,0,(1237),1000⟩,⟨3,0,5,(0),0⟩,⟨4,0,0,(0),0⟩,⟨2,6,7,(0),0⟩,⟨3,8,2,(0),0⟩,⟨6,9,0,(0),0⟩,⟨5,10,0,(0),0⟩,⟨3,4,11,(0),0⟩,⟨0,0,0,(4),1⟩,⟨3,13,5,(0),0⟩,⟨0,0,0,(1),1⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact45_row0_part_000.inc",include_str "../../../../source/fact45_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨0,0,0,(3),1⟩,⟨4,15,0,(0),0⟩,⟨2,6,17,(0),0⟩,⟨3,18,2,(0),0⟩,⟨5,19,0,(0),0⟩,⟨3,16,20,(0),0⟩,⟨2,15,21,(0),0⟩,⟨0,0,0,(6),1⟩,⟨3,19,19,(0),0⟩,⟨5,24,0,(0),0⟩,⟨3,23,25,(0),0⟩,⟨2,22,26,(0),0⟩,⟨3,24,19,(0),0⟩,⟨5,28,0,(0),0⟩,⟨3,23,29,(0),0⟩,⟨2,27,30,(0),0⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact45_row0_part_001.inc",include_str "../../../../source/fact45_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact45_row0_join_00190.inc",include_str "../../../../source/fact45_row0_join_00190.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree0 tree1
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 bound1 (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨3,14,31,(0),0⟩,⟨5,18,0,(0),0⟩,⟨3,32,33,(0),0⟩,⟨8,0,0,(0),0⟩,⟨3,0,35,(0),0⟩,⟨0,0,0,(2),3⟩,⟨0,0,0,(6),5⟩,⟨7,38,0,(0),0⟩,⟨5,0,0,(0),0⟩,⟨3,39,40,(0),0⟩,⟨6,41,0,(0),0⟩,⟨3,37,42,(0),0⟩,⟨2,15,43,(0),0⟩,⟨7,44,0,(0),0⟩,⟨3,45,40,(0),0⟩,⟨6,46,0,(0),0⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact45_row0_part_002.inc",include_str "../../../../source/fact45_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨3,36,47,(0),0⟩,⟨2,18,17,(0),0⟩,⟨3,49,2,(0),0⟩,⟨5,50,0,(0),0⟩,⟨3,16,51,(0),0⟩,⟨2,15,52,(0),0⟩,⟨3,50,50,(0),0⟩,⟨5,54,0,(0),0⟩,⟨3,23,55,(0),0⟩,⟨2,53,56,(0),0⟩,⟨3,54,50,(0),0⟩,⟨5,58,0,(0),0⟩,⟨3,23,59,(0),0⟩,⟨2,57,60,(0),0⟩,⟨3,18,61,(0),0⟩,⟨3,48,62,(0),0⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact45_row0_part_003.inc",include_str "../../../../source/fact45_row0_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes4 : List ScopedNumerical.Input.Node := [⟨2,5,17,(0),0⟩,⟨5,64,0,(0),0⟩,⟨3,63,65,(0),0⟩,⟨2,34,66,(0),0⟩,⟨3,12,67,(0),0⟩]
def fragment4 : Fragment := ⟨true,nodes4.map ScopedC.CData.nodeInitializer⟩
def file4 : File := ⟨"fact45_row0_part_004.inc",include_str "../../../../source/fact45_row0_part_004.inc"⟩
def tree4 : Tree Fragment := .leaf file4 fragment4
theorem bound4 : tree4.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile1 : File := ⟨"fact45_row0_join_00191.inc",include_str "../../../../source/fact45_row0_join_00191.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree3 tree4
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound3 bound4 (by decide +kernel)
def joinFile2 : File := ⟨"fact45_row0_join_00192.inc",include_str "../../../../source/fact45_row0_join_00192.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 tree2 joinTree1
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair bound2 joinBound1 (by decide +kernel)
def joinFile3 : File := ⟨"fact45_row0_join_00193.inc",include_str "../../../../source/fact45_row0_join_00193.inc"⟩
def joinTree3 : Tree Fragment := .pair joinFile3 joinTree0 joinTree2
theorem joinBound3 : joinTree3.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound0 joinBound2 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3,nodes4]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact45Row0.nodes := by rfl
def body : Tree Fragment := joinTree3
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound3
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3,fragment4] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact45Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,fragment4,nodes0,nodes1,nodes2,nodes3,nodes4]
def actual : File := ⟨"fact45_row0_array.inc",include_str "../../../../source/fact45_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact45_row0" ScopedNumerical.InputData.Fact45Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact45Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact45Row0

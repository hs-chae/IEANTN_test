/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.SourceBundle.Tree
import ScopedNumerical.InputData.Fact2Row0
namespace ScopedC.SourceBundle.Arrays.Fact2Row0
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def nodes0 : List ScopedNumerical.Input.Node := [⟨0,0,0,(0),1⟩,⟨0,0,0,(1),1⟩,⟨2,0,1,(0),0⟩,⟨0,0,0,(1),2⟩,⟨2,2,3,(0),0⟩,⟨0,0,0,(1),3⟩,⟨2,4,5,(0),0⟩,⟨0,0,0,(1),4⟩,⟨2,6,7,(0),0⟩,⟨0,0,0,(1),5⟩,⟨2,8,9,(0),0⟩,⟨0,0,0,(1),6⟩,⟨2,10,11,(0),0⟩,⟨0,0,0,(1),7⟩,⟨2,12,13,(0),0⟩,⟨0,0,0,(1),8⟩]
def fragment0 : Fragment := ⟨false,nodes0.map ScopedC.CData.nodeInitializer⟩
def file0 : File := ⟨"fact2_row0_part_000.inc",include_str "../../../../source/fact2_row0_part_000.inc"⟩
def tree0 : Tree Fragment := .leaf file0 fragment0
theorem bound0 : tree0.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes1 : List ScopedNumerical.Input.Node := [⟨2,14,15,(0),0⟩,⟨0,0,0,(1),9⟩,⟨2,16,17,(0),0⟩,⟨0,0,0,(1),10⟩,⟨2,18,19,(0),0⟩,⟨0,0,0,(1),11⟩,⟨2,20,21,(0),0⟩,⟨0,0,0,(1),12⟩,⟨2,22,23,(0),0⟩,⟨0,0,0,(1),13⟩,⟨2,24,25,(0),0⟩,⟨0,0,0,(1),14⟩,⟨2,26,27,(0),0⟩,⟨0,0,0,(1),15⟩,⟨2,28,29,(0),0⟩,⟨0,0,0,(1),16⟩]
def fragment1 : Fragment := ⟨true,nodes1.map ScopedC.CData.nodeInitializer⟩
def file1 : File := ⟨"fact2_row0_part_001.inc",include_str "../../../../source/fact2_row0_part_001.inc"⟩
def tree1 : Tree Fragment := .leaf file1 fragment1
theorem bound1 : tree1.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile0 : File := ⟨"fact2_row0_join_00048.inc",include_str "../../../../source/fact2_row0_join_00048.inc"⟩
def joinTree0 : Tree Fragment := .pair joinFile0 tree0 tree1
theorem joinBound0 : joinTree0.Bound (fun f file => renderFragment f = some file.text) := .pair bound0 bound1 (by decide +kernel)
def nodes2 : List ScopedNumerical.Input.Node := [⟨2,30,31,(0),0⟩,⟨0,0,0,(1),17⟩,⟨2,32,33,(0),0⟩,⟨0,0,0,(1),18⟩,⟨2,34,35,(0),0⟩,⟨0,0,0,(1),19⟩,⟨2,36,37,(0),0⟩,⟨0,0,0,(1),20⟩,⟨2,38,39,(0),0⟩,⟨0,0,0,(1),21⟩,⟨2,40,41,(0),0⟩,⟨0,0,0,(1),22⟩,⟨2,42,43,(0),0⟩,⟨0,0,0,(1),23⟩,⟨2,44,45,(0),0⟩,⟨0,0,0,(1),24⟩]
def fragment2 : Fragment := ⟨true,nodes2.map ScopedC.CData.nodeInitializer⟩
def file2 : File := ⟨"fact2_row0_part_002.inc",include_str "../../../../source/fact2_row0_part_002.inc"⟩
def tree2 : Tree Fragment := .leaf file2 fragment2
theorem bound2 : tree2.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes3 : List ScopedNumerical.Input.Node := [⟨2,46,47,(0),0⟩,⟨0,0,0,(1),25⟩,⟨2,48,49,(0),0⟩,⟨0,0,0,(1),26⟩,⟨2,50,51,(0),0⟩,⟨0,0,0,(1),27⟩,⟨2,52,53,(0),0⟩,⟨0,0,0,(1),28⟩,⟨2,54,55,(0),0⟩,⟨0,0,0,(1),29⟩,⟨2,56,57,(0),0⟩,⟨0,0,0,(1),30⟩,⟨2,58,59,(0),0⟩,⟨0,0,0,(1),31⟩,⟨2,60,61,(0),0⟩,⟨0,0,0,(1),32⟩]
def fragment3 : Fragment := ⟨true,nodes3.map ScopedC.CData.nodeInitializer⟩
def file3 : File := ⟨"fact2_row0_part_003.inc",include_str "../../../../source/fact2_row0_part_003.inc"⟩
def tree3 : Tree Fragment := .leaf file3 fragment3
theorem bound3 : tree3.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes4 : List ScopedNumerical.Input.Node := [⟨2,62,63,(0),0⟩,⟨0,0,0,(1),33⟩,⟨2,64,65,(0),0⟩,⟨0,0,0,(1),34⟩,⟨2,66,67,(0),0⟩,⟨0,0,0,(1),35⟩,⟨2,68,69,(0),0⟩,⟨0,0,0,(1),36⟩,⟨2,70,71,(0),0⟩,⟨0,0,0,(1),37⟩,⟨2,72,73,(0),0⟩,⟨0,0,0,(1),38⟩,⟨2,74,75,(0),0⟩,⟨0,0,0,(1),39⟩,⟨2,76,77,(0),0⟩,⟨0,0,0,(1),40⟩]
def fragment4 : Fragment := ⟨true,nodes4.map ScopedC.CData.nodeInitializer⟩
def file4 : File := ⟨"fact2_row0_part_004.inc",include_str "../../../../source/fact2_row0_part_004.inc"⟩
def tree4 : Tree Fragment := .leaf file4 fragment4
theorem bound4 : tree4.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile1 : File := ⟨"fact2_row0_join_00049.inc",include_str "../../../../source/fact2_row0_join_00049.inc"⟩
def joinTree1 : Tree Fragment := .pair joinFile1 tree3 tree4
theorem joinBound1 : joinTree1.Bound (fun f file => renderFragment f = some file.text) := .pair bound3 bound4 (by decide +kernel)
def joinFile2 : File := ⟨"fact2_row0_join_00050.inc",include_str "../../../../source/fact2_row0_join_00050.inc"⟩
def joinTree2 : Tree Fragment := .pair joinFile2 tree2 joinTree1
theorem joinBound2 : joinTree2.Bound (fun f file => renderFragment f = some file.text) := .pair bound2 joinBound1 (by decide +kernel)
def joinFile3 : File := ⟨"fact2_row0_join_00051.inc",include_str "../../../../source/fact2_row0_join_00051.inc"⟩
def joinTree3 : Tree Fragment := .pair joinFile3 joinTree0 joinTree2
theorem joinBound3 : joinTree3.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound0 joinBound2 (by decide +kernel)
def nodes5 : List ScopedNumerical.Input.Node := [⟨2,78,79,(0),0⟩,⟨0,0,0,(1),41⟩,⟨2,80,81,(0),0⟩,⟨0,0,0,(1),42⟩,⟨2,82,83,(0),0⟩,⟨0,0,0,(1),43⟩,⟨2,84,85,(0),0⟩,⟨0,0,0,(1),44⟩,⟨2,86,87,(0),0⟩,⟨0,0,0,(1),45⟩,⟨2,88,89,(0),0⟩,⟨0,0,0,(1),46⟩,⟨2,90,91,(0),0⟩,⟨0,0,0,(1),47⟩,⟨2,92,93,(0),0⟩,⟨0,0,0,(1),48⟩]
def fragment5 : Fragment := ⟨true,nodes5.map ScopedC.CData.nodeInitializer⟩
def file5 : File := ⟨"fact2_row0_part_005.inc",include_str "../../../../source/fact2_row0_part_005.inc"⟩
def tree5 : Tree Fragment := .leaf file5 fragment5
theorem bound5 : tree5.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes6 : List ScopedNumerical.Input.Node := [⟨2,94,95,(0),0⟩,⟨0,0,0,(1),49⟩,⟨2,96,97,(0),0⟩,⟨0,0,0,(1),50⟩,⟨2,98,99,(0),0⟩,⟨0,0,0,(1),51⟩,⟨2,100,101,(0),0⟩,⟨0,0,0,(1),52⟩,⟨2,102,103,(0),0⟩,⟨0,0,0,(1),53⟩,⟨2,104,105,(0),0⟩,⟨0,0,0,(1),54⟩,⟨2,106,107,(0),0⟩,⟨0,0,0,(1),55⟩,⟨2,108,109,(0),0⟩,⟨0,0,0,(1),56⟩]
def fragment6 : Fragment := ⟨true,nodes6.map ScopedC.CData.nodeInitializer⟩
def file6 : File := ⟨"fact2_row0_part_006.inc",include_str "../../../../source/fact2_row0_part_006.inc"⟩
def tree6 : Tree Fragment := .leaf file6 fragment6
theorem bound6 : tree6.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes7 : List ScopedNumerical.Input.Node := [⟨2,110,111,(0),0⟩,⟨0,0,0,(1),57⟩,⟨2,112,113,(0),0⟩,⟨0,0,0,(1),58⟩,⟨2,114,115,(0),0⟩,⟨0,0,0,(1),59⟩,⟨2,116,117,(0),0⟩,⟨0,0,0,(1),60⟩,⟨2,118,119,(0),0⟩,⟨0,0,0,(1),61⟩,⟨2,120,121,(0),0⟩,⟨0,0,0,(1),62⟩,⟨2,122,123,(0),0⟩,⟨0,0,0,(1),63⟩,⟨2,124,125,(0),0⟩,⟨0,0,0,(1),64⟩]
def fragment7 : Fragment := ⟨true,nodes7.map ScopedC.CData.nodeInitializer⟩
def file7 : File := ⟨"fact2_row0_part_007.inc",include_str "../../../../source/fact2_row0_part_007.inc"⟩
def tree7 : Tree Fragment := .leaf file7 fragment7
theorem bound7 : tree7.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile4 : File := ⟨"fact2_row0_join_00052.inc",include_str "../../../../source/fact2_row0_join_00052.inc"⟩
def joinTree4 : Tree Fragment := .pair joinFile4 tree6 tree7
theorem joinBound4 : joinTree4.Bound (fun f file => renderFragment f = some file.text) := .pair bound6 bound7 (by decide +kernel)
def joinFile5 : File := ⟨"fact2_row0_join_00053.inc",include_str "../../../../source/fact2_row0_join_00053.inc"⟩
def joinTree5 : Tree Fragment := .pair joinFile5 tree5 joinTree4
theorem joinBound5 : joinTree5.Bound (fun f file => renderFragment f = some file.text) := .pair bound5 joinBound4 (by decide +kernel)
def nodes8 : List ScopedNumerical.Input.Node := [⟨2,126,127,(0),0⟩,⟨0,0,0,(1),65⟩,⟨2,128,129,(0),0⟩,⟨0,0,0,(1),66⟩,⟨2,130,131,(0),0⟩,⟨0,0,0,(1),67⟩,⟨2,132,133,(0),0⟩,⟨0,0,0,(1),68⟩,⟨2,134,135,(0),0⟩,⟨0,0,0,(1),69⟩,⟨2,136,137,(0),0⟩,⟨0,0,0,(1),70⟩,⟨2,138,139,(0),0⟩,⟨0,0,0,(1),71⟩,⟨2,140,141,(0),0⟩,⟨0,0,0,(1),72⟩]
def fragment8 : Fragment := ⟨true,nodes8.map ScopedC.CData.nodeInitializer⟩
def file8 : File := ⟨"fact2_row0_part_008.inc",include_str "../../../../source/fact2_row0_part_008.inc"⟩
def tree8 : Tree Fragment := .leaf file8 fragment8
theorem bound8 : tree8.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes9 : List ScopedNumerical.Input.Node := [⟨2,142,143,(0),0⟩,⟨0,0,0,(1),73⟩,⟨2,144,145,(0),0⟩,⟨0,0,0,(1),74⟩,⟨2,146,147,(0),0⟩,⟨0,0,0,(1),75⟩,⟨2,148,149,(0),0⟩,⟨0,0,0,(1),76⟩,⟨2,150,151,(0),0⟩,⟨0,0,0,(1),77⟩,⟨2,152,153,(0),0⟩,⟨0,0,0,(1),78⟩,⟨2,154,155,(0),0⟩,⟨0,0,0,(1),79⟩,⟨2,156,157,(0),0⟩,⟨0,0,0,(1),80⟩]
def fragment9 : Fragment := ⟨true,nodes9.map ScopedC.CData.nodeInitializer⟩
def file9 : File := ⟨"fact2_row0_part_009.inc",include_str "../../../../source/fact2_row0_part_009.inc"⟩
def tree9 : Tree Fragment := .leaf file9 fragment9
theorem bound9 : tree9.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes10 : List ScopedNumerical.Input.Node := [⟨2,158,159,(0),0⟩,⟨0,0,0,(1),81⟩,⟨2,160,161,(0),0⟩,⟨0,0,0,(1),82⟩,⟨2,162,163,(0),0⟩,⟨0,0,0,(1),83⟩,⟨2,164,165,(0),0⟩,⟨0,0,0,(1),84⟩,⟨2,166,167,(0),0⟩,⟨0,0,0,(1),85⟩,⟨2,168,169,(0),0⟩,⟨0,0,0,(1),86⟩,⟨2,170,171,(0),0⟩,⟨0,0,0,(1),87⟩,⟨2,172,173,(0),0⟩,⟨0,0,0,(1),88⟩]
def fragment10 : Fragment := ⟨true,nodes10.map ScopedC.CData.nodeInitializer⟩
def file10 : File := ⟨"fact2_row0_part_010.inc",include_str "../../../../source/fact2_row0_part_010.inc"⟩
def tree10 : Tree Fragment := .leaf file10 fragment10
theorem bound10 : tree10.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile6 : File := ⟨"fact2_row0_join_00054.inc",include_str "../../../../source/fact2_row0_join_00054.inc"⟩
def joinTree6 : Tree Fragment := .pair joinFile6 tree9 tree10
theorem joinBound6 : joinTree6.Bound (fun f file => renderFragment f = some file.text) := .pair bound9 bound10 (by decide +kernel)
def joinFile7 : File := ⟨"fact2_row0_join_00055.inc",include_str "../../../../source/fact2_row0_join_00055.inc"⟩
def joinTree7 : Tree Fragment := .pair joinFile7 tree8 joinTree6
theorem joinBound7 : joinTree7.Bound (fun f file => renderFragment f = some file.text) := .pair bound8 joinBound6 (by decide +kernel)
def joinFile8 : File := ⟨"fact2_row0_join_00056.inc",include_str "../../../../source/fact2_row0_join_00056.inc"⟩
def joinTree8 : Tree Fragment := .pair joinFile8 joinTree5 joinTree7
theorem joinBound8 : joinTree8.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound5 joinBound7 (by decide +kernel)
def joinFile9 : File := ⟨"fact2_row0_join_00057.inc",include_str "../../../../source/fact2_row0_join_00057.inc"⟩
def joinTree9 : Tree Fragment := .pair joinFile9 joinTree3 joinTree8
theorem joinBound9 : joinTree9.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound3 joinBound8 (by decide +kernel)
def nodes11 : List ScopedNumerical.Input.Node := [⟨2,174,175,(0),0⟩,⟨0,0,0,(1),89⟩,⟨2,176,177,(0),0⟩,⟨0,0,0,(1),90⟩,⟨2,178,179,(0),0⟩,⟨0,0,0,(1),91⟩,⟨2,180,181,(0),0⟩,⟨0,0,0,(1),92⟩,⟨2,182,183,(0),0⟩,⟨0,0,0,(1),93⟩,⟨2,184,185,(0),0⟩,⟨0,0,0,(1),94⟩,⟨2,186,187,(0),0⟩,⟨0,0,0,(1),95⟩,⟨2,188,189,(0),0⟩,⟨0,0,0,(1),96⟩]
def fragment11 : Fragment := ⟨true,nodes11.map ScopedC.CData.nodeInitializer⟩
def file11 : File := ⟨"fact2_row0_part_011.inc",include_str "../../../../source/fact2_row0_part_011.inc"⟩
def tree11 : Tree Fragment := .leaf file11 fragment11
theorem bound11 : tree11.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes12 : List ScopedNumerical.Input.Node := [⟨2,190,191,(0),0⟩,⟨0,0,0,(1),97⟩,⟨2,192,193,(0),0⟩,⟨0,0,0,(1),98⟩,⟨2,194,195,(0),0⟩,⟨0,0,0,(1),99⟩,⟨2,196,197,(0),0⟩,⟨0,0,0,(1),100⟩,⟨2,198,199,(0),0⟩,⟨0,0,0,(1),101⟩,⟨2,200,201,(0),0⟩,⟨0,0,0,(1),102⟩,⟨2,202,203,(0),0⟩,⟨0,0,0,(1),103⟩,⟨2,204,205,(0),0⟩,⟨0,0,0,(1),104⟩]
def fragment12 : Fragment := ⟨true,nodes12.map ScopedC.CData.nodeInitializer⟩
def file12 : File := ⟨"fact2_row0_part_012.inc",include_str "../../../../source/fact2_row0_part_012.inc"⟩
def tree12 : Tree Fragment := .leaf file12 fragment12
theorem bound12 : tree12.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile10 : File := ⟨"fact2_row0_join_00058.inc",include_str "../../../../source/fact2_row0_join_00058.inc"⟩
def joinTree10 : Tree Fragment := .pair joinFile10 tree11 tree12
theorem joinBound10 : joinTree10.Bound (fun f file => renderFragment f = some file.text) := .pair bound11 bound12 (by decide +kernel)
def nodes13 : List ScopedNumerical.Input.Node := [⟨2,206,207,(0),0⟩,⟨0,0,0,(1),105⟩,⟨2,208,209,(0),0⟩,⟨0,0,0,(1),106⟩,⟨2,210,211,(0),0⟩,⟨0,0,0,(1),107⟩,⟨2,212,213,(0),0⟩,⟨0,0,0,(1),108⟩,⟨2,214,215,(0),0⟩,⟨0,0,0,(1),109⟩,⟨2,216,217,(0),0⟩,⟨0,0,0,(1),110⟩,⟨2,218,219,(0),0⟩,⟨0,0,0,(1),111⟩,⟨2,220,221,(0),0⟩,⟨0,0,0,(1),112⟩]
def fragment13 : Fragment := ⟨true,nodes13.map ScopedC.CData.nodeInitializer⟩
def file13 : File := ⟨"fact2_row0_part_013.inc",include_str "../../../../source/fact2_row0_part_013.inc"⟩
def tree13 : Tree Fragment := .leaf file13 fragment13
theorem bound13 : tree13.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes14 : List ScopedNumerical.Input.Node := [⟨2,222,223,(0),0⟩,⟨0,0,0,(1),113⟩,⟨2,224,225,(0),0⟩,⟨0,0,0,(1),114⟩,⟨2,226,227,(0),0⟩,⟨0,0,0,(1),115⟩,⟨2,228,229,(0),0⟩,⟨0,0,0,(1),116⟩,⟨2,230,231,(0),0⟩,⟨0,0,0,(1),117⟩,⟨2,232,233,(0),0⟩,⟨0,0,0,(1),118⟩,⟨2,234,235,(0),0⟩,⟨0,0,0,(1),119⟩,⟨2,236,237,(0),0⟩,⟨0,0,0,(1),120⟩]
def fragment14 : Fragment := ⟨true,nodes14.map ScopedC.CData.nodeInitializer⟩
def file14 : File := ⟨"fact2_row0_part_014.inc",include_str "../../../../source/fact2_row0_part_014.inc"⟩
def tree14 : Tree Fragment := .leaf file14 fragment14
theorem bound14 : tree14.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes15 : List ScopedNumerical.Input.Node := [⟨2,238,239,(0),0⟩,⟨0,0,0,(1),121⟩,⟨2,240,241,(0),0⟩,⟨0,0,0,(1),122⟩,⟨2,242,243,(0),0⟩,⟨0,0,0,(1),123⟩,⟨2,244,245,(0),0⟩,⟨0,0,0,(1),124⟩,⟨2,246,247,(0),0⟩,⟨0,0,0,(1),125⟩,⟨2,248,249,(0),0⟩,⟨0,0,0,(1),126⟩,⟨2,250,251,(0),0⟩,⟨0,0,0,(1),127⟩,⟨2,252,253,(0),0⟩,⟨0,0,0,(1),128⟩]
def fragment15 : Fragment := ⟨true,nodes15.map ScopedC.CData.nodeInitializer⟩
def file15 : File := ⟨"fact2_row0_part_015.inc",include_str "../../../../source/fact2_row0_part_015.inc"⟩
def tree15 : Tree Fragment := .leaf file15 fragment15
theorem bound15 : tree15.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile11 : File := ⟨"fact2_row0_join_00059.inc",include_str "../../../../source/fact2_row0_join_00059.inc"⟩
def joinTree11 : Tree Fragment := .pair joinFile11 tree14 tree15
theorem joinBound11 : joinTree11.Bound (fun f file => renderFragment f = some file.text) := .pair bound14 bound15 (by decide +kernel)
def joinFile12 : File := ⟨"fact2_row0_join_00060.inc",include_str "../../../../source/fact2_row0_join_00060.inc"⟩
def joinTree12 : Tree Fragment := .pair joinFile12 tree13 joinTree11
theorem joinBound12 : joinTree12.Bound (fun f file => renderFragment f = some file.text) := .pair bound13 joinBound11 (by decide +kernel)
def joinFile13 : File := ⟨"fact2_row0_join_00061.inc",include_str "../../../../source/fact2_row0_join_00061.inc"⟩
def joinTree13 : Tree Fragment := .pair joinFile13 joinTree10 joinTree12
theorem joinBound13 : joinTree13.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound10 joinBound12 (by decide +kernel)
def nodes16 : List ScopedNumerical.Input.Node := [⟨2,254,255,(0),0⟩,⟨0,0,0,(1),129⟩,⟨2,256,257,(0),0⟩,⟨0,0,0,(1),130⟩,⟨2,258,259,(0),0⟩,⟨0,0,0,(1),131⟩,⟨2,260,261,(0),0⟩,⟨0,0,0,(1),132⟩,⟨2,262,263,(0),0⟩,⟨0,0,0,(1),133⟩,⟨2,264,265,(0),0⟩,⟨0,0,0,(1),134⟩,⟨2,266,267,(0),0⟩,⟨0,0,0,(1),135⟩,⟨2,268,269,(0),0⟩,⟨0,0,0,(1),136⟩]
def fragment16 : Fragment := ⟨true,nodes16.map ScopedC.CData.nodeInitializer⟩
def file16 : File := ⟨"fact2_row0_part_016.inc",include_str "../../../../source/fact2_row0_part_016.inc"⟩
def tree16 : Tree Fragment := .leaf file16 fragment16
theorem bound16 : tree16.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes17 : List ScopedNumerical.Input.Node := [⟨2,270,271,(0),0⟩,⟨0,0,0,(1),137⟩,⟨2,272,273,(0),0⟩,⟨0,0,0,(1),138⟩,⟨2,274,275,(0),0⟩,⟨0,0,0,(1),139⟩,⟨2,276,277,(0),0⟩,⟨0,0,0,(1),140⟩,⟨2,278,279,(0),0⟩,⟨0,0,0,(1),141⟩,⟨2,280,281,(0),0⟩,⟨0,0,0,(1),142⟩,⟨2,282,283,(0),0⟩,⟨0,0,0,(1),143⟩,⟨2,284,285,(0),0⟩,⟨0,0,0,(1),144⟩]
def fragment17 : Fragment := ⟨true,nodes17.map ScopedC.CData.nodeInitializer⟩
def file17 : File := ⟨"fact2_row0_part_017.inc",include_str "../../../../source/fact2_row0_part_017.inc"⟩
def tree17 : Tree Fragment := .leaf file17 fragment17
theorem bound17 : tree17.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes18 : List ScopedNumerical.Input.Node := [⟨2,286,287,(0),0⟩,⟨0,0,0,(1),145⟩,⟨2,288,289,(0),0⟩,⟨0,0,0,(1),146⟩,⟨2,290,291,(0),0⟩,⟨0,0,0,(1),147⟩,⟨2,292,293,(0),0⟩,⟨0,0,0,(1),148⟩,⟨2,294,295,(0),0⟩,⟨0,0,0,(1),149⟩,⟨2,296,297,(0),0⟩,⟨0,0,0,(1),150⟩,⟨2,298,299,(0),0⟩,⟨0,0,0,(1),151⟩,⟨2,300,301,(0),0⟩,⟨0,0,0,(1),152⟩]
def fragment18 : Fragment := ⟨true,nodes18.map ScopedC.CData.nodeInitializer⟩
def file18 : File := ⟨"fact2_row0_part_018.inc",include_str "../../../../source/fact2_row0_part_018.inc"⟩
def tree18 : Tree Fragment := .leaf file18 fragment18
theorem bound18 : tree18.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile14 : File := ⟨"fact2_row0_join_00062.inc",include_str "../../../../source/fact2_row0_join_00062.inc"⟩
def joinTree14 : Tree Fragment := .pair joinFile14 tree17 tree18
theorem joinBound14 : joinTree14.Bound (fun f file => renderFragment f = some file.text) := .pair bound17 bound18 (by decide +kernel)
def joinFile15 : File := ⟨"fact2_row0_join_00063.inc",include_str "../../../../source/fact2_row0_join_00063.inc"⟩
def joinTree15 : Tree Fragment := .pair joinFile15 tree16 joinTree14
theorem joinBound15 : joinTree15.Bound (fun f file => renderFragment f = some file.text) := .pair bound16 joinBound14 (by decide +kernel)
def nodes19 : List ScopedNumerical.Input.Node := [⟨2,302,303,(0),0⟩,⟨0,0,0,(1),153⟩,⟨2,304,305,(0),0⟩,⟨0,0,0,(1),154⟩,⟨2,306,307,(0),0⟩,⟨0,0,0,(1),155⟩,⟨2,308,309,(0),0⟩,⟨0,0,0,(1),156⟩,⟨2,310,311,(0),0⟩,⟨0,0,0,(1),157⟩,⟨2,312,313,(0),0⟩,⟨0,0,0,(1),158⟩,⟨2,314,315,(0),0⟩,⟨0,0,0,(1),159⟩,⟨2,316,317,(0),0⟩,⟨0,0,0,(1),160⟩]
def fragment19 : Fragment := ⟨true,nodes19.map ScopedC.CData.nodeInitializer⟩
def file19 : File := ⟨"fact2_row0_part_019.inc",include_str "../../../../source/fact2_row0_part_019.inc"⟩
def tree19 : Tree Fragment := .leaf file19 fragment19
theorem bound19 : tree19.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes20 : List ScopedNumerical.Input.Node := [⟨2,318,319,(0),0⟩,⟨0,0,0,(1),161⟩,⟨2,320,321,(0),0⟩,⟨0,0,0,(1),162⟩,⟨2,322,323,(0),0⟩,⟨0,0,0,(1),163⟩,⟨2,324,325,(0),0⟩,⟨0,0,0,(1),164⟩,⟨2,326,327,(0),0⟩,⟨0,0,0,(1),165⟩,⟨2,328,329,(0),0⟩,⟨0,0,0,(1),166⟩,⟨2,330,331,(0),0⟩,⟨0,0,0,(1),167⟩,⟨2,332,333,(0),0⟩,⟨0,0,0,(1),168⟩]
def fragment20 : Fragment := ⟨true,nodes20.map ScopedC.CData.nodeInitializer⟩
def file20 : File := ⟨"fact2_row0_part_020.inc",include_str "../../../../source/fact2_row0_part_020.inc"⟩
def tree20 : Tree Fragment := .leaf file20 fragment20
theorem bound20 : tree20.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes21 : List ScopedNumerical.Input.Node := [⟨2,334,335,(0),0⟩,⟨0,0,0,(1),169⟩,⟨2,336,337,(0),0⟩,⟨0,0,0,(1),170⟩,⟨2,338,339,(0),0⟩,⟨0,0,0,(1),171⟩,⟨2,340,341,(0),0⟩,⟨0,0,0,(1),172⟩,⟨2,342,343,(0),0⟩,⟨0,0,0,(1),173⟩,⟨2,344,345,(0),0⟩,⟨0,0,0,(1),174⟩,⟨2,346,347,(0),0⟩,⟨0,0,0,(1),175⟩,⟨2,348,349,(0),0⟩,⟨0,0,0,(1),176⟩]
def fragment21 : Fragment := ⟨true,nodes21.map ScopedC.CData.nodeInitializer⟩
def file21 : File := ⟨"fact2_row0_part_021.inc",include_str "../../../../source/fact2_row0_part_021.inc"⟩
def tree21 : Tree Fragment := .leaf file21 fragment21
theorem bound21 : tree21.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile16 : File := ⟨"fact2_row0_join_00064.inc",include_str "../../../../source/fact2_row0_join_00064.inc"⟩
def joinTree16 : Tree Fragment := .pair joinFile16 tree20 tree21
theorem joinBound16 : joinTree16.Bound (fun f file => renderFragment f = some file.text) := .pair bound20 bound21 (by decide +kernel)
def joinFile17 : File := ⟨"fact2_row0_join_00065.inc",include_str "../../../../source/fact2_row0_join_00065.inc"⟩
def joinTree17 : Tree Fragment := .pair joinFile17 tree19 joinTree16
theorem joinBound17 : joinTree17.Bound (fun f file => renderFragment f = some file.text) := .pair bound19 joinBound16 (by decide +kernel)
def joinFile18 : File := ⟨"fact2_row0_join_00066.inc",include_str "../../../../source/fact2_row0_join_00066.inc"⟩
def joinTree18 : Tree Fragment := .pair joinFile18 joinTree15 joinTree17
theorem joinBound18 : joinTree18.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound15 joinBound17 (by decide +kernel)
def joinFile19 : File := ⟨"fact2_row0_join_00067.inc",include_str "../../../../source/fact2_row0_join_00067.inc"⟩
def joinTree19 : Tree Fragment := .pair joinFile19 joinTree13 joinTree18
theorem joinBound19 : joinTree19.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound13 joinBound18 (by decide +kernel)
def joinFile20 : File := ⟨"fact2_row0_join_00068.inc",include_str "../../../../source/fact2_row0_join_00068.inc"⟩
def joinTree20 : Tree Fragment := .pair joinFile20 joinTree9 joinTree19
theorem joinBound20 : joinTree20.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound9 joinBound19 (by decide +kernel)
def nodes22 : List ScopedNumerical.Input.Node := [⟨2,350,351,(0),0⟩,⟨0,0,0,(1),177⟩,⟨2,352,353,(0),0⟩,⟨0,0,0,(1),178⟩,⟨2,354,355,(0),0⟩,⟨0,0,0,(1),179⟩,⟨2,356,357,(0),0⟩,⟨0,0,0,(1),180⟩,⟨2,358,359,(0),0⟩,⟨0,0,0,(1),181⟩,⟨2,360,361,(0),0⟩,⟨0,0,0,(1),182⟩,⟨2,362,363,(0),0⟩,⟨0,0,0,(1),183⟩,⟨2,364,365,(0),0⟩,⟨0,0,0,(1),184⟩]
def fragment22 : Fragment := ⟨true,nodes22.map ScopedC.CData.nodeInitializer⟩
def file22 : File := ⟨"fact2_row0_part_022.inc",include_str "../../../../source/fact2_row0_part_022.inc"⟩
def tree22 : Tree Fragment := .leaf file22 fragment22
theorem bound22 : tree22.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes23 : List ScopedNumerical.Input.Node := [⟨2,366,367,(0),0⟩,⟨0,0,0,(1),185⟩,⟨2,368,369,(0),0⟩,⟨0,0,0,(1),186⟩,⟨2,370,371,(0),0⟩,⟨0,0,0,(1),187⟩,⟨2,372,373,(0),0⟩,⟨0,0,0,(1),188⟩,⟨2,374,375,(0),0⟩,⟨0,0,0,(1),189⟩,⟨2,376,377,(0),0⟩,⟨0,0,0,(1),190⟩,⟨2,378,379,(0),0⟩,⟨0,0,0,(1),191⟩,⟨2,380,381,(0),0⟩,⟨0,0,0,(1),192⟩]
def fragment23 : Fragment := ⟨true,nodes23.map ScopedC.CData.nodeInitializer⟩
def file23 : File := ⟨"fact2_row0_part_023.inc",include_str "../../../../source/fact2_row0_part_023.inc"⟩
def tree23 : Tree Fragment := .leaf file23 fragment23
theorem bound23 : tree23.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile21 : File := ⟨"fact2_row0_join_00069.inc",include_str "../../../../source/fact2_row0_join_00069.inc"⟩
def joinTree21 : Tree Fragment := .pair joinFile21 tree22 tree23
theorem joinBound21 : joinTree21.Bound (fun f file => renderFragment f = some file.text) := .pair bound22 bound23 (by decide +kernel)
def nodes24 : List ScopedNumerical.Input.Node := [⟨2,382,383,(0),0⟩,⟨0,0,0,(1),193⟩,⟨2,384,385,(0),0⟩,⟨0,0,0,(1),194⟩,⟨2,386,387,(0),0⟩,⟨0,0,0,(1),195⟩,⟨2,388,389,(0),0⟩,⟨0,0,0,(1),196⟩,⟨2,390,391,(0),0⟩,⟨0,0,0,(1),197⟩,⟨2,392,393,(0),0⟩,⟨0,0,0,(1),198⟩,⟨2,394,395,(0),0⟩,⟨0,0,0,(1),199⟩,⟨2,396,397,(0),0⟩,⟨0,0,0,(1),200⟩]
def fragment24 : Fragment := ⟨true,nodes24.map ScopedC.CData.nodeInitializer⟩
def file24 : File := ⟨"fact2_row0_part_024.inc",include_str "../../../../source/fact2_row0_part_024.inc"⟩
def tree24 : Tree Fragment := .leaf file24 fragment24
theorem bound24 : tree24.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes25 : List ScopedNumerical.Input.Node := [⟨2,398,399,(0),0⟩,⟨0,0,0,(1),201⟩,⟨2,400,401,(0),0⟩,⟨0,0,0,(1),202⟩,⟨2,402,403,(0),0⟩,⟨0,0,0,(1),203⟩,⟨2,404,405,(0),0⟩,⟨0,0,0,(1),204⟩,⟨2,406,407,(0),0⟩,⟨0,0,0,(1),205⟩,⟨2,408,409,(0),0⟩,⟨0,0,0,(1),206⟩,⟨2,410,411,(0),0⟩,⟨0,0,0,(1),207⟩,⟨2,412,413,(0),0⟩,⟨0,0,0,(1),208⟩]
def fragment25 : Fragment := ⟨true,nodes25.map ScopedC.CData.nodeInitializer⟩
def file25 : File := ⟨"fact2_row0_part_025.inc",include_str "../../../../source/fact2_row0_part_025.inc"⟩
def tree25 : Tree Fragment := .leaf file25 fragment25
theorem bound25 : tree25.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes26 : List ScopedNumerical.Input.Node := [⟨2,414,415,(0),0⟩,⟨0,0,0,(1),209⟩,⟨2,416,417,(0),0⟩,⟨0,0,0,(1),210⟩,⟨2,418,419,(0),0⟩,⟨0,0,0,(1),211⟩,⟨2,420,421,(0),0⟩,⟨0,0,0,(1),212⟩,⟨2,422,423,(0),0⟩,⟨0,0,0,(1),213⟩,⟨2,424,425,(0),0⟩,⟨0,0,0,(1),214⟩,⟨2,426,427,(0),0⟩,⟨0,0,0,(1),215⟩,⟨2,428,429,(0),0⟩,⟨0,0,0,(1),216⟩]
def fragment26 : Fragment := ⟨true,nodes26.map ScopedC.CData.nodeInitializer⟩
def file26 : File := ⟨"fact2_row0_part_026.inc",include_str "../../../../source/fact2_row0_part_026.inc"⟩
def tree26 : Tree Fragment := .leaf file26 fragment26
theorem bound26 : tree26.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile22 : File := ⟨"fact2_row0_join_00070.inc",include_str "../../../../source/fact2_row0_join_00070.inc"⟩
def joinTree22 : Tree Fragment := .pair joinFile22 tree25 tree26
theorem joinBound22 : joinTree22.Bound (fun f file => renderFragment f = some file.text) := .pair bound25 bound26 (by decide +kernel)
def joinFile23 : File := ⟨"fact2_row0_join_00071.inc",include_str "../../../../source/fact2_row0_join_00071.inc"⟩
def joinTree23 : Tree Fragment := .pair joinFile23 tree24 joinTree22
theorem joinBound23 : joinTree23.Bound (fun f file => renderFragment f = some file.text) := .pair bound24 joinBound22 (by decide +kernel)
def joinFile24 : File := ⟨"fact2_row0_join_00072.inc",include_str "../../../../source/fact2_row0_join_00072.inc"⟩
def joinTree24 : Tree Fragment := .pair joinFile24 joinTree21 joinTree23
theorem joinBound24 : joinTree24.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound21 joinBound23 (by decide +kernel)
def nodes27 : List ScopedNumerical.Input.Node := [⟨2,430,431,(0),0⟩,⟨0,0,0,(1),217⟩,⟨2,432,433,(0),0⟩,⟨0,0,0,(1),218⟩,⟨2,434,435,(0),0⟩,⟨0,0,0,(1),219⟩,⟨2,436,437,(0),0⟩,⟨0,0,0,(1),220⟩,⟨2,438,439,(0),0⟩,⟨0,0,0,(1),221⟩,⟨2,440,441,(0),0⟩,⟨0,0,0,(1),222⟩,⟨2,442,443,(0),0⟩,⟨0,0,0,(1),223⟩,⟨2,444,445,(0),0⟩,⟨0,0,0,(1),224⟩]
def fragment27 : Fragment := ⟨true,nodes27.map ScopedC.CData.nodeInitializer⟩
def file27 : File := ⟨"fact2_row0_part_027.inc",include_str "../../../../source/fact2_row0_part_027.inc"⟩
def tree27 : Tree Fragment := .leaf file27 fragment27
theorem bound27 : tree27.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes28 : List ScopedNumerical.Input.Node := [⟨2,446,447,(0),0⟩,⟨0,0,0,(1),225⟩,⟨2,448,449,(0),0⟩,⟨0,0,0,(1),226⟩,⟨2,450,451,(0),0⟩,⟨0,0,0,(1),227⟩,⟨2,452,453,(0),0⟩,⟨0,0,0,(1),228⟩,⟨2,454,455,(0),0⟩,⟨0,0,0,(1),229⟩,⟨2,456,457,(0),0⟩,⟨0,0,0,(1),230⟩,⟨2,458,459,(0),0⟩,⟨0,0,0,(1),231⟩,⟨2,460,461,(0),0⟩,⟨0,0,0,(1),232⟩]
def fragment28 : Fragment := ⟨true,nodes28.map ScopedC.CData.nodeInitializer⟩
def file28 : File := ⟨"fact2_row0_part_028.inc",include_str "../../../../source/fact2_row0_part_028.inc"⟩
def tree28 : Tree Fragment := .leaf file28 fragment28
theorem bound28 : tree28.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes29 : List ScopedNumerical.Input.Node := [⟨2,462,463,(0),0⟩,⟨0,0,0,(1),233⟩,⟨2,464,465,(0),0⟩,⟨0,0,0,(1),234⟩,⟨2,466,467,(0),0⟩,⟨0,0,0,(1),235⟩,⟨2,468,469,(0),0⟩,⟨0,0,0,(1),236⟩,⟨2,470,471,(0),0⟩,⟨0,0,0,(1),237⟩,⟨2,472,473,(0),0⟩,⟨0,0,0,(1),238⟩,⟨2,474,475,(0),0⟩,⟨0,0,0,(1),239⟩,⟨2,476,477,(0),0⟩,⟨0,0,0,(1),240⟩]
def fragment29 : Fragment := ⟨true,nodes29.map ScopedC.CData.nodeInitializer⟩
def file29 : File := ⟨"fact2_row0_part_029.inc",include_str "../../../../source/fact2_row0_part_029.inc"⟩
def tree29 : Tree Fragment := .leaf file29 fragment29
theorem bound29 : tree29.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile25 : File := ⟨"fact2_row0_join_00073.inc",include_str "../../../../source/fact2_row0_join_00073.inc"⟩
def joinTree25 : Tree Fragment := .pair joinFile25 tree28 tree29
theorem joinBound25 : joinTree25.Bound (fun f file => renderFragment f = some file.text) := .pair bound28 bound29 (by decide +kernel)
def joinFile26 : File := ⟨"fact2_row0_join_00074.inc",include_str "../../../../source/fact2_row0_join_00074.inc"⟩
def joinTree26 : Tree Fragment := .pair joinFile26 tree27 joinTree25
theorem joinBound26 : joinTree26.Bound (fun f file => renderFragment f = some file.text) := .pair bound27 joinBound25 (by decide +kernel)
def nodes30 : List ScopedNumerical.Input.Node := [⟨2,478,479,(0),0⟩,⟨0,0,0,(1),241⟩,⟨2,480,481,(0),0⟩,⟨0,0,0,(1),242⟩,⟨2,482,483,(0),0⟩,⟨0,0,0,(1),243⟩,⟨2,484,485,(0),0⟩,⟨0,0,0,(1),244⟩,⟨2,486,487,(0),0⟩,⟨0,0,0,(1),245⟩,⟨2,488,489,(0),0⟩,⟨0,0,0,(1),246⟩,⟨2,490,491,(0),0⟩,⟨0,0,0,(1),247⟩,⟨2,492,493,(0),0⟩,⟨0,0,0,(1),248⟩]
def fragment30 : Fragment := ⟨true,nodes30.map ScopedC.CData.nodeInitializer⟩
def file30 : File := ⟨"fact2_row0_part_030.inc",include_str "../../../../source/fact2_row0_part_030.inc"⟩
def tree30 : Tree Fragment := .leaf file30 fragment30
theorem bound30 : tree30.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes31 : List ScopedNumerical.Input.Node := [⟨2,494,495,(0),0⟩,⟨0,0,0,(1),249⟩,⟨2,496,497,(0),0⟩,⟨0,0,0,(1),250⟩,⟨2,498,499,(0),0⟩,⟨0,0,0,(1),251⟩,⟨2,500,501,(0),0⟩,⟨0,0,0,(1),252⟩,⟨2,502,503,(0),0⟩,⟨0,0,0,(1),253⟩,⟨2,504,505,(0),0⟩,⟨0,0,0,(1),254⟩,⟨2,506,507,(0),0⟩,⟨0,0,0,(1),255⟩,⟨2,508,509,(0),0⟩,⟨0,0,0,(1),256⟩]
def fragment31 : Fragment := ⟨true,nodes31.map ScopedC.CData.nodeInitializer⟩
def file31 : File := ⟨"fact2_row0_part_031.inc",include_str "../../../../source/fact2_row0_part_031.inc"⟩
def tree31 : Tree Fragment := .leaf file31 fragment31
theorem bound31 : tree31.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes32 : List ScopedNumerical.Input.Node := [⟨2,510,511,(0),0⟩,⟨0,0,0,(1),257⟩,⟨2,512,513,(0),0⟩,⟨0,0,0,(1),258⟩,⟨2,514,515,(0),0⟩,⟨0,0,0,(1),259⟩,⟨2,516,517,(0),0⟩,⟨0,0,0,(1),260⟩,⟨2,518,519,(0),0⟩,⟨0,0,0,(1),261⟩,⟨2,520,521,(0),0⟩,⟨0,0,0,(1),262⟩,⟨2,522,523,(0),0⟩,⟨0,0,0,(1),263⟩,⟨2,524,525,(0),0⟩,⟨0,0,0,(1),264⟩]
def fragment32 : Fragment := ⟨true,nodes32.map ScopedC.CData.nodeInitializer⟩
def file32 : File := ⟨"fact2_row0_part_032.inc",include_str "../../../../source/fact2_row0_part_032.inc"⟩
def tree32 : Tree Fragment := .leaf file32 fragment32
theorem bound32 : tree32.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile27 : File := ⟨"fact2_row0_join_00075.inc",include_str "../../../../source/fact2_row0_join_00075.inc"⟩
def joinTree27 : Tree Fragment := .pair joinFile27 tree31 tree32
theorem joinBound27 : joinTree27.Bound (fun f file => renderFragment f = some file.text) := .pair bound31 bound32 (by decide +kernel)
def joinFile28 : File := ⟨"fact2_row0_join_00076.inc",include_str "../../../../source/fact2_row0_join_00076.inc"⟩
def joinTree28 : Tree Fragment := .pair joinFile28 tree30 joinTree27
theorem joinBound28 : joinTree28.Bound (fun f file => renderFragment f = some file.text) := .pair bound30 joinBound27 (by decide +kernel)
def joinFile29 : File := ⟨"fact2_row0_join_00077.inc",include_str "../../../../source/fact2_row0_join_00077.inc"⟩
def joinTree29 : Tree Fragment := .pair joinFile29 joinTree26 joinTree28
theorem joinBound29 : joinTree29.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound26 joinBound28 (by decide +kernel)
def joinFile30 : File := ⟨"fact2_row0_join_00078.inc",include_str "../../../../source/fact2_row0_join_00078.inc"⟩
def joinTree30 : Tree Fragment := .pair joinFile30 joinTree24 joinTree29
theorem joinBound30 : joinTree30.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound24 joinBound29 (by decide +kernel)
def nodes33 : List ScopedNumerical.Input.Node := [⟨2,526,527,(0),0⟩,⟨0,0,0,(1),265⟩,⟨2,528,529,(0),0⟩,⟨0,0,0,(1),266⟩,⟨2,530,531,(0),0⟩,⟨0,0,0,(1),267⟩,⟨2,532,533,(0),0⟩,⟨0,0,0,(1),268⟩,⟨2,534,535,(0),0⟩,⟨0,0,0,(1),269⟩,⟨2,536,537,(0),0⟩,⟨0,0,0,(1),270⟩,⟨2,538,539,(0),0⟩,⟨0,0,0,(1),271⟩,⟨2,540,541,(0),0⟩,⟨0,0,0,(1),272⟩]
def fragment33 : Fragment := ⟨true,nodes33.map ScopedC.CData.nodeInitializer⟩
def file33 : File := ⟨"fact2_row0_part_033.inc",include_str "../../../../source/fact2_row0_part_033.inc"⟩
def tree33 : Tree Fragment := .leaf file33 fragment33
theorem bound33 : tree33.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes34 : List ScopedNumerical.Input.Node := [⟨2,542,543,(0),0⟩,⟨0,0,0,(1),273⟩,⟨2,544,545,(0),0⟩,⟨0,0,0,(1),274⟩,⟨2,546,547,(0),0⟩,⟨0,0,0,(1),275⟩,⟨2,548,549,(0),0⟩,⟨0,0,0,(1),276⟩,⟨2,550,551,(0),0⟩,⟨0,0,0,(1),277⟩,⟨2,552,553,(0),0⟩,⟨0,0,0,(1),278⟩,⟨2,554,555,(0),0⟩,⟨0,0,0,(1),279⟩,⟨2,556,557,(0),0⟩,⟨0,0,0,(1),280⟩]
def fragment34 : Fragment := ⟨true,nodes34.map ScopedC.CData.nodeInitializer⟩
def file34 : File := ⟨"fact2_row0_part_034.inc",include_str "../../../../source/fact2_row0_part_034.inc"⟩
def tree34 : Tree Fragment := .leaf file34 fragment34
theorem bound34 : tree34.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile31 : File := ⟨"fact2_row0_join_00079.inc",include_str "../../../../source/fact2_row0_join_00079.inc"⟩
def joinTree31 : Tree Fragment := .pair joinFile31 tree33 tree34
theorem joinBound31 : joinTree31.Bound (fun f file => renderFragment f = some file.text) := .pair bound33 bound34 (by decide +kernel)
def nodes35 : List ScopedNumerical.Input.Node := [⟨2,558,559,(0),0⟩,⟨0,0,0,(1),281⟩,⟨2,560,561,(0),0⟩,⟨0,0,0,(1),282⟩,⟨2,562,563,(0),0⟩,⟨0,0,0,(1),283⟩,⟨2,564,565,(0),0⟩,⟨0,0,0,(1),284⟩,⟨2,566,567,(0),0⟩,⟨0,0,0,(1),285⟩,⟨2,568,569,(0),0⟩,⟨0,0,0,(1),286⟩,⟨2,570,571,(0),0⟩,⟨0,0,0,(1),287⟩,⟨2,572,573,(0),0⟩,⟨0,0,0,(1),288⟩]
def fragment35 : Fragment := ⟨true,nodes35.map ScopedC.CData.nodeInitializer⟩
def file35 : File := ⟨"fact2_row0_part_035.inc",include_str "../../../../source/fact2_row0_part_035.inc"⟩
def tree35 : Tree Fragment := .leaf file35 fragment35
theorem bound35 : tree35.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes36 : List ScopedNumerical.Input.Node := [⟨2,574,575,(0),0⟩,⟨0,0,0,(1),289⟩,⟨2,576,577,(0),0⟩,⟨0,0,0,(1),290⟩,⟨2,578,579,(0),0⟩,⟨0,0,0,(1),291⟩,⟨2,580,581,(0),0⟩,⟨0,0,0,(1),292⟩,⟨2,582,583,(0),0⟩,⟨0,0,0,(1),293⟩,⟨2,584,585,(0),0⟩,⟨0,0,0,(1),294⟩,⟨2,586,587,(0),0⟩,⟨0,0,0,(1),295⟩,⟨2,588,589,(0),0⟩,⟨0,0,0,(1),296⟩]
def fragment36 : Fragment := ⟨true,nodes36.map ScopedC.CData.nodeInitializer⟩
def file36 : File := ⟨"fact2_row0_part_036.inc",include_str "../../../../source/fact2_row0_part_036.inc"⟩
def tree36 : Tree Fragment := .leaf file36 fragment36
theorem bound36 : tree36.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes37 : List ScopedNumerical.Input.Node := [⟨2,590,591,(0),0⟩,⟨0,0,0,(1),297⟩,⟨2,592,593,(0),0⟩,⟨0,0,0,(1),298⟩,⟨2,594,595,(0),0⟩,⟨0,0,0,(1),299⟩,⟨2,596,597,(0),0⟩,⟨0,0,0,(1),300⟩,⟨2,598,599,(0),0⟩,⟨0,0,0,(1),301⟩,⟨2,600,601,(0),0⟩,⟨0,0,0,(1),302⟩,⟨2,602,603,(0),0⟩,⟨0,0,0,(1),303⟩,⟨2,604,605,(0),0⟩,⟨0,0,0,(1),304⟩]
def fragment37 : Fragment := ⟨true,nodes37.map ScopedC.CData.nodeInitializer⟩
def file37 : File := ⟨"fact2_row0_part_037.inc",include_str "../../../../source/fact2_row0_part_037.inc"⟩
def tree37 : Tree Fragment := .leaf file37 fragment37
theorem bound37 : tree37.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile32 : File := ⟨"fact2_row0_join_00080.inc",include_str "../../../../source/fact2_row0_join_00080.inc"⟩
def joinTree32 : Tree Fragment := .pair joinFile32 tree36 tree37
theorem joinBound32 : joinTree32.Bound (fun f file => renderFragment f = some file.text) := .pair bound36 bound37 (by decide +kernel)
def joinFile33 : File := ⟨"fact2_row0_join_00081.inc",include_str "../../../../source/fact2_row0_join_00081.inc"⟩
def joinTree33 : Tree Fragment := .pair joinFile33 tree35 joinTree32
theorem joinBound33 : joinTree33.Bound (fun f file => renderFragment f = some file.text) := .pair bound35 joinBound32 (by decide +kernel)
def joinFile34 : File := ⟨"fact2_row0_join_00082.inc",include_str "../../../../source/fact2_row0_join_00082.inc"⟩
def joinTree34 : Tree Fragment := .pair joinFile34 joinTree31 joinTree33
theorem joinBound34 : joinTree34.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound31 joinBound33 (by decide +kernel)
def nodes38 : List ScopedNumerical.Input.Node := [⟨2,606,607,(0),0⟩,⟨0,0,0,(1),305⟩,⟨2,608,609,(0),0⟩,⟨0,0,0,(1),306⟩,⟨2,610,611,(0),0⟩,⟨0,0,0,(1),307⟩,⟨2,612,613,(0),0⟩,⟨0,0,0,(1),308⟩,⟨2,614,615,(0),0⟩,⟨0,0,0,(1),309⟩,⟨2,616,617,(0),0⟩,⟨0,0,0,(1),310⟩,⟨2,618,619,(0),0⟩,⟨0,0,0,(1),311⟩,⟨2,620,621,(0),0⟩,⟨0,0,0,(1),312⟩]
def fragment38 : Fragment := ⟨true,nodes38.map ScopedC.CData.nodeInitializer⟩
def file38 : File := ⟨"fact2_row0_part_038.inc",include_str "../../../../source/fact2_row0_part_038.inc"⟩
def tree38 : Tree Fragment := .leaf file38 fragment38
theorem bound38 : tree38.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes39 : List ScopedNumerical.Input.Node := [⟨2,622,623,(0),0⟩,⟨0,0,0,(1),313⟩,⟨2,624,625,(0),0⟩,⟨0,0,0,(1),314⟩,⟨2,626,627,(0),0⟩,⟨0,0,0,(1),315⟩,⟨2,628,629,(0),0⟩,⟨0,0,0,(1),316⟩,⟨2,630,631,(0),0⟩,⟨0,0,0,(1),317⟩,⟨2,632,633,(0),0⟩,⟨0,0,0,(1),318⟩,⟨2,634,635,(0),0⟩,⟨0,0,0,(1),319⟩,⟨2,636,637,(0),0⟩,⟨0,0,0,(1),320⟩]
def fragment39 : Fragment := ⟨true,nodes39.map ScopedC.CData.nodeInitializer⟩
def file39 : File := ⟨"fact2_row0_part_039.inc",include_str "../../../../source/fact2_row0_part_039.inc"⟩
def tree39 : Tree Fragment := .leaf file39 fragment39
theorem bound39 : tree39.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes40 : List ScopedNumerical.Input.Node := [⟨2,638,639,(0),0⟩,⟨0,0,0,(1),321⟩,⟨2,640,641,(0),0⟩,⟨0,0,0,(1),322⟩,⟨2,642,643,(0),0⟩,⟨0,0,0,(1),323⟩,⟨2,644,645,(0),0⟩,⟨0,0,0,(1),324⟩,⟨2,646,647,(0),0⟩,⟨0,0,0,(1),325⟩,⟨2,648,649,(0),0⟩,⟨0,0,0,(1),326⟩,⟨2,650,651,(0),0⟩,⟨0,0,0,(1),327⟩,⟨2,652,653,(0),0⟩,⟨0,0,0,(1),328⟩]
def fragment40 : Fragment := ⟨true,nodes40.map ScopedC.CData.nodeInitializer⟩
def file40 : File := ⟨"fact2_row0_part_040.inc",include_str "../../../../source/fact2_row0_part_040.inc"⟩
def tree40 : Tree Fragment := .leaf file40 fragment40
theorem bound40 : tree40.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile35 : File := ⟨"fact2_row0_join_00083.inc",include_str "../../../../source/fact2_row0_join_00083.inc"⟩
def joinTree35 : Tree Fragment := .pair joinFile35 tree39 tree40
theorem joinBound35 : joinTree35.Bound (fun f file => renderFragment f = some file.text) := .pair bound39 bound40 (by decide +kernel)
def joinFile36 : File := ⟨"fact2_row0_join_00084.inc",include_str "../../../../source/fact2_row0_join_00084.inc"⟩
def joinTree36 : Tree Fragment := .pair joinFile36 tree38 joinTree35
theorem joinBound36 : joinTree36.Bound (fun f file => renderFragment f = some file.text) := .pair bound38 joinBound35 (by decide +kernel)
def nodes41 : List ScopedNumerical.Input.Node := [⟨2,654,655,(0),0⟩,⟨0,0,0,(1),329⟩,⟨2,656,657,(0),0⟩,⟨0,0,0,(1),330⟩,⟨2,658,659,(0),0⟩,⟨0,0,0,(1),331⟩,⟨2,660,661,(0),0⟩,⟨0,0,0,(1),332⟩,⟨2,662,663,(0),0⟩,⟨0,0,0,(1),333⟩,⟨2,664,665,(0),0⟩,⟨0,0,0,(1),334⟩,⟨2,666,667,(0),0⟩,⟨0,0,0,(1),335⟩,⟨2,668,669,(0),0⟩,⟨0,0,0,(1),336⟩]
def fragment41 : Fragment := ⟨true,nodes41.map ScopedC.CData.nodeInitializer⟩
def file41 : File := ⟨"fact2_row0_part_041.inc",include_str "../../../../source/fact2_row0_part_041.inc"⟩
def tree41 : Tree Fragment := .leaf file41 fragment41
theorem bound41 : tree41.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes42 : List ScopedNumerical.Input.Node := [⟨2,670,671,(0),0⟩,⟨0,0,0,(1),337⟩,⟨2,672,673,(0),0⟩,⟨0,0,0,(1),338⟩,⟨2,674,675,(0),0⟩,⟨0,0,0,(1),339⟩,⟨2,676,677,(0),0⟩,⟨0,0,0,(1),340⟩,⟨2,678,679,(0),0⟩,⟨0,0,0,(1),341⟩,⟨2,680,681,(0),0⟩,⟨0,0,0,(1),342⟩,⟨2,682,683,(0),0⟩,⟨0,0,0,(1),343⟩,⟨2,684,685,(0),0⟩,⟨0,0,0,(1),344⟩]
def fragment42 : Fragment := ⟨true,nodes42.map ScopedC.CData.nodeInitializer⟩
def file42 : File := ⟨"fact2_row0_part_042.inc",include_str "../../../../source/fact2_row0_part_042.inc"⟩
def tree42 : Tree Fragment := .leaf file42 fragment42
theorem bound42 : tree42.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes43 : List ScopedNumerical.Input.Node := [⟨2,686,687,(0),0⟩,⟨0,0,0,(1),345⟩,⟨2,688,689,(0),0⟩,⟨0,0,0,(1),346⟩,⟨2,690,691,(0),0⟩,⟨0,0,0,(1),347⟩,⟨2,692,693,(0),0⟩,⟨0,0,0,(1),348⟩,⟨2,694,695,(0),0⟩,⟨0,0,0,(1),349⟩,⟨2,696,697,(0),0⟩,⟨0,0,0,(1),350⟩,⟨2,698,699,(0),0⟩,⟨0,0,0,(1),351⟩,⟨2,700,701,(0),0⟩,⟨0,0,0,(1),352⟩]
def fragment43 : Fragment := ⟨true,nodes43.map ScopedC.CData.nodeInitializer⟩
def file43 : File := ⟨"fact2_row0_part_043.inc",include_str "../../../../source/fact2_row0_part_043.inc"⟩
def tree43 : Tree Fragment := .leaf file43 fragment43
theorem bound43 : tree43.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile37 : File := ⟨"fact2_row0_join_00085.inc",include_str "../../../../source/fact2_row0_join_00085.inc"⟩
def joinTree37 : Tree Fragment := .pair joinFile37 tree42 tree43
theorem joinBound37 : joinTree37.Bound (fun f file => renderFragment f = some file.text) := .pair bound42 bound43 (by decide +kernel)
def joinFile38 : File := ⟨"fact2_row0_join_00086.inc",include_str "../../../../source/fact2_row0_join_00086.inc"⟩
def joinTree38 : Tree Fragment := .pair joinFile38 tree41 joinTree37
theorem joinBound38 : joinTree38.Bound (fun f file => renderFragment f = some file.text) := .pair bound41 joinBound37 (by decide +kernel)
def joinFile39 : File := ⟨"fact2_row0_join_00087.inc",include_str "../../../../source/fact2_row0_join_00087.inc"⟩
def joinTree39 : Tree Fragment := .pair joinFile39 joinTree36 joinTree38
theorem joinBound39 : joinTree39.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound36 joinBound38 (by decide +kernel)
def joinFile40 : File := ⟨"fact2_row0_join_00088.inc",include_str "../../../../source/fact2_row0_join_00088.inc"⟩
def joinTree40 : Tree Fragment := .pair joinFile40 joinTree34 joinTree39
theorem joinBound40 : joinTree40.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound34 joinBound39 (by decide +kernel)
def joinFile41 : File := ⟨"fact2_row0_join_00089.inc",include_str "../../../../source/fact2_row0_join_00089.inc"⟩
def joinTree41 : Tree Fragment := .pair joinFile41 joinTree30 joinTree40
theorem joinBound41 : joinTree41.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound30 joinBound40 (by decide +kernel)
def joinFile42 : File := ⟨"fact2_row0_join_00090.inc",include_str "../../../../source/fact2_row0_join_00090.inc"⟩
def joinTree42 : Tree Fragment := .pair joinFile42 joinTree20 joinTree41
theorem joinBound42 : joinTree42.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound20 joinBound41 (by decide +kernel)
def nodes44 : List ScopedNumerical.Input.Node := [⟨2,702,703,(0),0⟩,⟨0,0,0,(1),353⟩,⟨2,704,705,(0),0⟩,⟨0,0,0,(1),354⟩,⟨2,706,707,(0),0⟩,⟨0,0,0,(1),355⟩,⟨2,708,709,(0),0⟩,⟨0,0,0,(1),356⟩,⟨2,710,711,(0),0⟩,⟨0,0,0,(1),357⟩,⟨2,712,713,(0),0⟩,⟨0,0,0,(1),358⟩,⟨2,714,715,(0),0⟩,⟨0,0,0,(1),359⟩,⟨2,716,717,(0),0⟩,⟨0,0,0,(1),360⟩]
def fragment44 : Fragment := ⟨true,nodes44.map ScopedC.CData.nodeInitializer⟩
def file44 : File := ⟨"fact2_row0_part_044.inc",include_str "../../../../source/fact2_row0_part_044.inc"⟩
def tree44 : Tree Fragment := .leaf file44 fragment44
theorem bound44 : tree44.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes45 : List ScopedNumerical.Input.Node := [⟨2,718,719,(0),0⟩,⟨0,0,0,(1),361⟩,⟨2,720,721,(0),0⟩,⟨0,0,0,(1),362⟩,⟨2,722,723,(0),0⟩,⟨0,0,0,(1),363⟩,⟨2,724,725,(0),0⟩,⟨0,0,0,(1),364⟩,⟨2,726,727,(0),0⟩,⟨0,0,0,(1),365⟩,⟨2,728,729,(0),0⟩,⟨0,0,0,(1),366⟩,⟨2,730,731,(0),0⟩,⟨0,0,0,(1),367⟩,⟨2,732,733,(0),0⟩,⟨0,0,0,(1),368⟩]
def fragment45 : Fragment := ⟨true,nodes45.map ScopedC.CData.nodeInitializer⟩
def file45 : File := ⟨"fact2_row0_part_045.inc",include_str "../../../../source/fact2_row0_part_045.inc"⟩
def tree45 : Tree Fragment := .leaf file45 fragment45
theorem bound45 : tree45.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile43 : File := ⟨"fact2_row0_join_00091.inc",include_str "../../../../source/fact2_row0_join_00091.inc"⟩
def joinTree43 : Tree Fragment := .pair joinFile43 tree44 tree45
theorem joinBound43 : joinTree43.Bound (fun f file => renderFragment f = some file.text) := .pair bound44 bound45 (by decide +kernel)
def nodes46 : List ScopedNumerical.Input.Node := [⟨2,734,735,(0),0⟩,⟨0,0,0,(1),369⟩,⟨2,736,737,(0),0⟩,⟨0,0,0,(1),370⟩,⟨2,738,739,(0),0⟩,⟨0,0,0,(1),371⟩,⟨2,740,741,(0),0⟩,⟨0,0,0,(1),372⟩,⟨2,742,743,(0),0⟩,⟨0,0,0,(1),373⟩,⟨2,744,745,(0),0⟩,⟨0,0,0,(1),374⟩,⟨2,746,747,(0),0⟩,⟨0,0,0,(1),375⟩,⟨2,748,749,(0),0⟩,⟨0,0,0,(1),376⟩]
def fragment46 : Fragment := ⟨true,nodes46.map ScopedC.CData.nodeInitializer⟩
def file46 : File := ⟨"fact2_row0_part_046.inc",include_str "../../../../source/fact2_row0_part_046.inc"⟩
def tree46 : Tree Fragment := .leaf file46 fragment46
theorem bound46 : tree46.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes47 : List ScopedNumerical.Input.Node := [⟨2,750,751,(0),0⟩,⟨0,0,0,(1),377⟩,⟨2,752,753,(0),0⟩,⟨0,0,0,(1),378⟩,⟨2,754,755,(0),0⟩,⟨0,0,0,(1),379⟩,⟨2,756,757,(0),0⟩,⟨0,0,0,(1),380⟩,⟨2,758,759,(0),0⟩,⟨0,0,0,(1),381⟩,⟨2,760,761,(0),0⟩,⟨0,0,0,(1),382⟩,⟨2,762,763,(0),0⟩,⟨0,0,0,(1),383⟩,⟨2,764,765,(0),0⟩,⟨0,0,0,(1),384⟩]
def fragment47 : Fragment := ⟨true,nodes47.map ScopedC.CData.nodeInitializer⟩
def file47 : File := ⟨"fact2_row0_part_047.inc",include_str "../../../../source/fact2_row0_part_047.inc"⟩
def tree47 : Tree Fragment := .leaf file47 fragment47
theorem bound47 : tree47.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes48 : List ScopedNumerical.Input.Node := [⟨2,766,767,(0),0⟩,⟨0,0,0,(1),385⟩,⟨2,768,769,(0),0⟩,⟨0,0,0,(1),386⟩,⟨2,770,771,(0),0⟩,⟨0,0,0,(1),387⟩,⟨2,772,773,(0),0⟩,⟨0,0,0,(1),388⟩,⟨2,774,775,(0),0⟩,⟨0,0,0,(1),389⟩,⟨2,776,777,(0),0⟩,⟨0,0,0,(1),390⟩,⟨2,778,779,(0),0⟩,⟨0,0,0,(1),391⟩,⟨2,780,781,(0),0⟩,⟨0,0,0,(1),392⟩]
def fragment48 : Fragment := ⟨true,nodes48.map ScopedC.CData.nodeInitializer⟩
def file48 : File := ⟨"fact2_row0_part_048.inc",include_str "../../../../source/fact2_row0_part_048.inc"⟩
def tree48 : Tree Fragment := .leaf file48 fragment48
theorem bound48 : tree48.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile44 : File := ⟨"fact2_row0_join_00092.inc",include_str "../../../../source/fact2_row0_join_00092.inc"⟩
def joinTree44 : Tree Fragment := .pair joinFile44 tree47 tree48
theorem joinBound44 : joinTree44.Bound (fun f file => renderFragment f = some file.text) := .pair bound47 bound48 (by decide +kernel)
def joinFile45 : File := ⟨"fact2_row0_join_00093.inc",include_str "../../../../source/fact2_row0_join_00093.inc"⟩
def joinTree45 : Tree Fragment := .pair joinFile45 tree46 joinTree44
theorem joinBound45 : joinTree45.Bound (fun f file => renderFragment f = some file.text) := .pair bound46 joinBound44 (by decide +kernel)
def joinFile46 : File := ⟨"fact2_row0_join_00094.inc",include_str "../../../../source/fact2_row0_join_00094.inc"⟩
def joinTree46 : Tree Fragment := .pair joinFile46 joinTree43 joinTree45
theorem joinBound46 : joinTree46.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound43 joinBound45 (by decide +kernel)
def nodes49 : List ScopedNumerical.Input.Node := [⟨2,782,783,(0),0⟩,⟨0,0,0,(1),393⟩,⟨2,784,785,(0),0⟩,⟨0,0,0,(1),394⟩,⟨2,786,787,(0),0⟩,⟨0,0,0,(1),395⟩,⟨2,788,789,(0),0⟩,⟨0,0,0,(1),396⟩,⟨2,790,791,(0),0⟩,⟨0,0,0,(1),397⟩,⟨2,792,793,(0),0⟩,⟨0,0,0,(1),398⟩,⟨2,794,795,(0),0⟩,⟨0,0,0,(1),399⟩,⟨2,796,797,(0),0⟩,⟨0,0,0,(1),400⟩]
def fragment49 : Fragment := ⟨true,nodes49.map ScopedC.CData.nodeInitializer⟩
def file49 : File := ⟨"fact2_row0_part_049.inc",include_str "../../../../source/fact2_row0_part_049.inc"⟩
def tree49 : Tree Fragment := .leaf file49 fragment49
theorem bound49 : tree49.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes50 : List ScopedNumerical.Input.Node := [⟨2,798,799,(0),0⟩,⟨0,0,0,(1),401⟩,⟨2,800,801,(0),0⟩,⟨0,0,0,(1),402⟩,⟨2,802,803,(0),0⟩,⟨0,0,0,(1),403⟩,⟨2,804,805,(0),0⟩,⟨0,0,0,(1),404⟩,⟨2,806,807,(0),0⟩,⟨0,0,0,(1),405⟩,⟨2,808,809,(0),0⟩,⟨0,0,0,(1),406⟩,⟨2,810,811,(0),0⟩,⟨0,0,0,(1),407⟩,⟨2,812,813,(0),0⟩,⟨0,0,0,(1),408⟩]
def fragment50 : Fragment := ⟨true,nodes50.map ScopedC.CData.nodeInitializer⟩
def file50 : File := ⟨"fact2_row0_part_050.inc",include_str "../../../../source/fact2_row0_part_050.inc"⟩
def tree50 : Tree Fragment := .leaf file50 fragment50
theorem bound50 : tree50.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes51 : List ScopedNumerical.Input.Node := [⟨2,814,815,(0),0⟩,⟨0,0,0,(1),409⟩,⟨2,816,817,(0),0⟩,⟨0,0,0,(1),410⟩,⟨2,818,819,(0),0⟩,⟨0,0,0,(1),411⟩,⟨2,820,821,(0),0⟩,⟨0,0,0,(1),412⟩,⟨2,822,823,(0),0⟩,⟨0,0,0,(1),413⟩,⟨2,824,825,(0),0⟩,⟨0,0,0,(1),414⟩,⟨2,826,827,(0),0⟩,⟨0,0,0,(1),415⟩,⟨2,828,829,(0),0⟩,⟨0,0,0,(1),416⟩]
def fragment51 : Fragment := ⟨true,nodes51.map ScopedC.CData.nodeInitializer⟩
def file51 : File := ⟨"fact2_row0_part_051.inc",include_str "../../../../source/fact2_row0_part_051.inc"⟩
def tree51 : Tree Fragment := .leaf file51 fragment51
theorem bound51 : tree51.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile47 : File := ⟨"fact2_row0_join_00095.inc",include_str "../../../../source/fact2_row0_join_00095.inc"⟩
def joinTree47 : Tree Fragment := .pair joinFile47 tree50 tree51
theorem joinBound47 : joinTree47.Bound (fun f file => renderFragment f = some file.text) := .pair bound50 bound51 (by decide +kernel)
def joinFile48 : File := ⟨"fact2_row0_join_00096.inc",include_str "../../../../source/fact2_row0_join_00096.inc"⟩
def joinTree48 : Tree Fragment := .pair joinFile48 tree49 joinTree47
theorem joinBound48 : joinTree48.Bound (fun f file => renderFragment f = some file.text) := .pair bound49 joinBound47 (by decide +kernel)
def nodes52 : List ScopedNumerical.Input.Node := [⟨2,830,831,(0),0⟩,⟨0,0,0,(1),417⟩,⟨2,832,833,(0),0⟩,⟨0,0,0,(1),418⟩,⟨2,834,835,(0),0⟩,⟨0,0,0,(1),419⟩,⟨2,836,837,(0),0⟩,⟨0,0,0,(1),420⟩,⟨2,838,839,(0),0⟩,⟨0,0,0,(1),421⟩,⟨2,840,841,(0),0⟩,⟨0,0,0,(1),422⟩,⟨2,842,843,(0),0⟩,⟨0,0,0,(1),423⟩,⟨2,844,845,(0),0⟩,⟨0,0,0,(1),424⟩]
def fragment52 : Fragment := ⟨true,nodes52.map ScopedC.CData.nodeInitializer⟩
def file52 : File := ⟨"fact2_row0_part_052.inc",include_str "../../../../source/fact2_row0_part_052.inc"⟩
def tree52 : Tree Fragment := .leaf file52 fragment52
theorem bound52 : tree52.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes53 : List ScopedNumerical.Input.Node := [⟨2,846,847,(0),0⟩,⟨0,0,0,(1),425⟩,⟨2,848,849,(0),0⟩,⟨0,0,0,(1),426⟩,⟨2,850,851,(0),0⟩,⟨0,0,0,(1),427⟩,⟨2,852,853,(0),0⟩,⟨0,0,0,(1),428⟩,⟨2,854,855,(0),0⟩,⟨0,0,0,(1),429⟩,⟨2,856,857,(0),0⟩,⟨0,0,0,(1),430⟩,⟨2,858,859,(0),0⟩,⟨0,0,0,(1),431⟩,⟨2,860,861,(0),0⟩,⟨0,0,0,(1),432⟩]
def fragment53 : Fragment := ⟨true,nodes53.map ScopedC.CData.nodeInitializer⟩
def file53 : File := ⟨"fact2_row0_part_053.inc",include_str "../../../../source/fact2_row0_part_053.inc"⟩
def tree53 : Tree Fragment := .leaf file53 fragment53
theorem bound53 : tree53.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes54 : List ScopedNumerical.Input.Node := [⟨2,862,863,(0),0⟩,⟨0,0,0,(1),433⟩,⟨2,864,865,(0),0⟩,⟨0,0,0,(1),434⟩,⟨2,866,867,(0),0⟩,⟨0,0,0,(1),435⟩,⟨2,868,869,(0),0⟩,⟨0,0,0,(1),436⟩,⟨2,870,871,(0),0⟩,⟨0,0,0,(1),437⟩,⟨2,872,873,(0),0⟩,⟨0,0,0,(1),438⟩,⟨2,874,875,(0),0⟩,⟨0,0,0,(1),439⟩,⟨2,876,877,(0),0⟩,⟨0,0,0,(1),440⟩]
def fragment54 : Fragment := ⟨true,nodes54.map ScopedC.CData.nodeInitializer⟩
def file54 : File := ⟨"fact2_row0_part_054.inc",include_str "../../../../source/fact2_row0_part_054.inc"⟩
def tree54 : Tree Fragment := .leaf file54 fragment54
theorem bound54 : tree54.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile49 : File := ⟨"fact2_row0_join_00097.inc",include_str "../../../../source/fact2_row0_join_00097.inc"⟩
def joinTree49 : Tree Fragment := .pair joinFile49 tree53 tree54
theorem joinBound49 : joinTree49.Bound (fun f file => renderFragment f = some file.text) := .pair bound53 bound54 (by decide +kernel)
def joinFile50 : File := ⟨"fact2_row0_join_00098.inc",include_str "../../../../source/fact2_row0_join_00098.inc"⟩
def joinTree50 : Tree Fragment := .pair joinFile50 tree52 joinTree49
theorem joinBound50 : joinTree50.Bound (fun f file => renderFragment f = some file.text) := .pair bound52 joinBound49 (by decide +kernel)
def joinFile51 : File := ⟨"fact2_row0_join_00099.inc",include_str "../../../../source/fact2_row0_join_00099.inc"⟩
def joinTree51 : Tree Fragment := .pair joinFile51 joinTree48 joinTree50
theorem joinBound51 : joinTree51.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound48 joinBound50 (by decide +kernel)
def joinFile52 : File := ⟨"fact2_row0_join_00100.inc",include_str "../../../../source/fact2_row0_join_00100.inc"⟩
def joinTree52 : Tree Fragment := .pair joinFile52 joinTree46 joinTree51
theorem joinBound52 : joinTree52.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound46 joinBound51 (by decide +kernel)
def nodes55 : List ScopedNumerical.Input.Node := [⟨2,878,879,(0),0⟩,⟨0,0,0,(1),441⟩,⟨2,880,881,(0),0⟩,⟨0,0,0,(1),442⟩,⟨2,882,883,(0),0⟩,⟨0,0,0,(1),443⟩,⟨2,884,885,(0),0⟩,⟨0,0,0,(1),444⟩,⟨2,886,887,(0),0⟩,⟨0,0,0,(1),445⟩,⟨2,888,889,(0),0⟩,⟨0,0,0,(1),446⟩,⟨2,890,891,(0),0⟩,⟨0,0,0,(1),447⟩,⟨2,892,893,(0),0⟩,⟨0,0,0,(1),448⟩]
def fragment55 : Fragment := ⟨true,nodes55.map ScopedC.CData.nodeInitializer⟩
def file55 : File := ⟨"fact2_row0_part_055.inc",include_str "../../../../source/fact2_row0_part_055.inc"⟩
def tree55 : Tree Fragment := .leaf file55 fragment55
theorem bound55 : tree55.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes56 : List ScopedNumerical.Input.Node := [⟨2,894,895,(0),0⟩,⟨0,0,0,(1),449⟩,⟨2,896,897,(0),0⟩,⟨0,0,0,(1),450⟩,⟨2,898,899,(0),0⟩,⟨0,0,0,(1),451⟩,⟨2,900,901,(0),0⟩,⟨0,0,0,(1),452⟩,⟨2,902,903,(0),0⟩,⟨0,0,0,(1),453⟩,⟨2,904,905,(0),0⟩,⟨0,0,0,(1),454⟩,⟨2,906,907,(0),0⟩,⟨0,0,0,(1),455⟩,⟨2,908,909,(0),0⟩,⟨0,0,0,(1),456⟩]
def fragment56 : Fragment := ⟨true,nodes56.map ScopedC.CData.nodeInitializer⟩
def file56 : File := ⟨"fact2_row0_part_056.inc",include_str "../../../../source/fact2_row0_part_056.inc"⟩
def tree56 : Tree Fragment := .leaf file56 fragment56
theorem bound56 : tree56.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile53 : File := ⟨"fact2_row0_join_00101.inc",include_str "../../../../source/fact2_row0_join_00101.inc"⟩
def joinTree53 : Tree Fragment := .pair joinFile53 tree55 tree56
theorem joinBound53 : joinTree53.Bound (fun f file => renderFragment f = some file.text) := .pair bound55 bound56 (by decide +kernel)
def nodes57 : List ScopedNumerical.Input.Node := [⟨2,910,911,(0),0⟩,⟨0,0,0,(1),457⟩,⟨2,912,913,(0),0⟩,⟨0,0,0,(1),458⟩,⟨2,914,915,(0),0⟩,⟨0,0,0,(1),459⟩,⟨2,916,917,(0),0⟩,⟨0,0,0,(1),460⟩,⟨2,918,919,(0),0⟩,⟨0,0,0,(1),461⟩,⟨2,920,921,(0),0⟩,⟨0,0,0,(1),462⟩,⟨2,922,923,(0),0⟩,⟨0,0,0,(1),463⟩,⟨2,924,925,(0),0⟩,⟨0,0,0,(1),464⟩]
def fragment57 : Fragment := ⟨true,nodes57.map ScopedC.CData.nodeInitializer⟩
def file57 : File := ⟨"fact2_row0_part_057.inc",include_str "../../../../source/fact2_row0_part_057.inc"⟩
def tree57 : Tree Fragment := .leaf file57 fragment57
theorem bound57 : tree57.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes58 : List ScopedNumerical.Input.Node := [⟨2,926,927,(0),0⟩,⟨0,0,0,(1),465⟩,⟨2,928,929,(0),0⟩,⟨0,0,0,(1),466⟩,⟨2,930,931,(0),0⟩,⟨0,0,0,(1),467⟩,⟨2,932,933,(0),0⟩,⟨0,0,0,(1),468⟩,⟨2,934,935,(0),0⟩,⟨0,0,0,(1),469⟩,⟨2,936,937,(0),0⟩,⟨0,0,0,(1),470⟩,⟨2,938,939,(0),0⟩,⟨0,0,0,(1),471⟩,⟨2,940,941,(0),0⟩,⟨0,0,0,(1),472⟩]
def fragment58 : Fragment := ⟨true,nodes58.map ScopedC.CData.nodeInitializer⟩
def file58 : File := ⟨"fact2_row0_part_058.inc",include_str "../../../../source/fact2_row0_part_058.inc"⟩
def tree58 : Tree Fragment := .leaf file58 fragment58
theorem bound58 : tree58.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes59 : List ScopedNumerical.Input.Node := [⟨2,942,943,(0),0⟩,⟨0,0,0,(1),473⟩,⟨2,944,945,(0),0⟩,⟨0,0,0,(1),474⟩,⟨2,946,947,(0),0⟩,⟨0,0,0,(1),475⟩,⟨2,948,949,(0),0⟩,⟨0,0,0,(1),476⟩,⟨2,950,951,(0),0⟩,⟨0,0,0,(1),477⟩,⟨2,952,953,(0),0⟩,⟨0,0,0,(1),478⟩,⟨2,954,955,(0),0⟩,⟨0,0,0,(1),479⟩,⟨2,956,957,(0),0⟩,⟨0,0,0,(1),480⟩]
def fragment59 : Fragment := ⟨true,nodes59.map ScopedC.CData.nodeInitializer⟩
def file59 : File := ⟨"fact2_row0_part_059.inc",include_str "../../../../source/fact2_row0_part_059.inc"⟩
def tree59 : Tree Fragment := .leaf file59 fragment59
theorem bound59 : tree59.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile54 : File := ⟨"fact2_row0_join_00102.inc",include_str "../../../../source/fact2_row0_join_00102.inc"⟩
def joinTree54 : Tree Fragment := .pair joinFile54 tree58 tree59
theorem joinBound54 : joinTree54.Bound (fun f file => renderFragment f = some file.text) := .pair bound58 bound59 (by decide +kernel)
def joinFile55 : File := ⟨"fact2_row0_join_00103.inc",include_str "../../../../source/fact2_row0_join_00103.inc"⟩
def joinTree55 : Tree Fragment := .pair joinFile55 tree57 joinTree54
theorem joinBound55 : joinTree55.Bound (fun f file => renderFragment f = some file.text) := .pair bound57 joinBound54 (by decide +kernel)
def joinFile56 : File := ⟨"fact2_row0_join_00104.inc",include_str "../../../../source/fact2_row0_join_00104.inc"⟩
def joinTree56 : Tree Fragment := .pair joinFile56 joinTree53 joinTree55
theorem joinBound56 : joinTree56.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound53 joinBound55 (by decide +kernel)
def nodes60 : List ScopedNumerical.Input.Node := [⟨2,958,959,(0),0⟩,⟨0,0,0,(1),481⟩,⟨2,960,961,(0),0⟩,⟨0,0,0,(1),482⟩,⟨2,962,963,(0),0⟩,⟨0,0,0,(1),483⟩,⟨2,964,965,(0),0⟩,⟨0,0,0,(1),484⟩,⟨2,966,967,(0),0⟩,⟨0,0,0,(1),485⟩,⟨2,968,969,(0),0⟩,⟨0,0,0,(1),486⟩,⟨2,970,971,(0),0⟩,⟨0,0,0,(1),487⟩,⟨2,972,973,(0),0⟩,⟨0,0,0,(1),488⟩]
def fragment60 : Fragment := ⟨true,nodes60.map ScopedC.CData.nodeInitializer⟩
def file60 : File := ⟨"fact2_row0_part_060.inc",include_str "../../../../source/fact2_row0_part_060.inc"⟩
def tree60 : Tree Fragment := .leaf file60 fragment60
theorem bound60 : tree60.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes61 : List ScopedNumerical.Input.Node := [⟨2,974,975,(0),0⟩,⟨0,0,0,(1),489⟩,⟨2,976,977,(0),0⟩,⟨0,0,0,(1),490⟩,⟨2,978,979,(0),0⟩,⟨0,0,0,(1),491⟩,⟨2,980,981,(0),0⟩,⟨0,0,0,(1),492⟩,⟨2,982,983,(0),0⟩,⟨0,0,0,(1),493⟩,⟨2,984,985,(0),0⟩,⟨0,0,0,(1),494⟩,⟨2,986,987,(0),0⟩,⟨0,0,0,(1),495⟩,⟨2,988,989,(0),0⟩,⟨0,0,0,(1),496⟩]
def fragment61 : Fragment := ⟨true,nodes61.map ScopedC.CData.nodeInitializer⟩
def file61 : File := ⟨"fact2_row0_part_061.inc",include_str "../../../../source/fact2_row0_part_061.inc"⟩
def tree61 : Tree Fragment := .leaf file61 fragment61
theorem bound61 : tree61.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes62 : List ScopedNumerical.Input.Node := [⟨2,990,991,(0),0⟩,⟨0,0,0,(1),497⟩,⟨2,992,993,(0),0⟩,⟨0,0,0,(1),498⟩,⟨2,994,995,(0),0⟩,⟨0,0,0,(1),499⟩,⟨2,996,997,(0),0⟩,⟨0,0,0,(1),500⟩,⟨2,998,999,(0),0⟩,⟨0,0,0,(1),501⟩,⟨2,1000,1001,(0),0⟩,⟨0,0,0,(1),502⟩,⟨2,1002,1003,(0),0⟩,⟨0,0,0,(1),503⟩,⟨2,1004,1005,(0),0⟩,⟨0,0,0,(1),504⟩]
def fragment62 : Fragment := ⟨true,nodes62.map ScopedC.CData.nodeInitializer⟩
def file62 : File := ⟨"fact2_row0_part_062.inc",include_str "../../../../source/fact2_row0_part_062.inc"⟩
def tree62 : Tree Fragment := .leaf file62 fragment62
theorem bound62 : tree62.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile57 : File := ⟨"fact2_row0_join_00105.inc",include_str "../../../../source/fact2_row0_join_00105.inc"⟩
def joinTree57 : Tree Fragment := .pair joinFile57 tree61 tree62
theorem joinBound57 : joinTree57.Bound (fun f file => renderFragment f = some file.text) := .pair bound61 bound62 (by decide +kernel)
def joinFile58 : File := ⟨"fact2_row0_join_00106.inc",include_str "../../../../source/fact2_row0_join_00106.inc"⟩
def joinTree58 : Tree Fragment := .pair joinFile58 tree60 joinTree57
theorem joinBound58 : joinTree58.Bound (fun f file => renderFragment f = some file.text) := .pair bound60 joinBound57 (by decide +kernel)
def nodes63 : List ScopedNumerical.Input.Node := [⟨2,1006,1007,(0),0⟩,⟨0,0,0,(1),505⟩,⟨2,1008,1009,(0),0⟩,⟨0,0,0,(1),506⟩,⟨2,1010,1011,(0),0⟩,⟨0,0,0,(1),507⟩,⟨2,1012,1013,(0),0⟩,⟨0,0,0,(1),508⟩,⟨2,1014,1015,(0),0⟩,⟨0,0,0,(1),509⟩,⟨2,1016,1017,(0),0⟩,⟨0,0,0,(1),510⟩,⟨2,1018,1019,(0),0⟩,⟨0,0,0,(1),511⟩,⟨2,1020,1021,(0),0⟩,⟨0,0,0,(1),512⟩]
def fragment63 : Fragment := ⟨true,nodes63.map ScopedC.CData.nodeInitializer⟩
def file63 : File := ⟨"fact2_row0_part_063.inc",include_str "../../../../source/fact2_row0_part_063.inc"⟩
def tree63 : Tree Fragment := .leaf file63 fragment63
theorem bound63 : tree63.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes64 : List ScopedNumerical.Input.Node := [⟨2,1022,1023,(0),0⟩,⟨0,0,0,(1),513⟩,⟨2,1024,1025,(0),0⟩,⟨0,0,0,(1),514⟩,⟨2,1026,1027,(0),0⟩,⟨0,0,0,(1),515⟩,⟨2,1028,1029,(0),0⟩,⟨0,0,0,(1),516⟩,⟨2,1030,1031,(0),0⟩,⟨0,0,0,(1),517⟩,⟨2,1032,1033,(0),0⟩,⟨0,0,0,(1),518⟩,⟨2,1034,1035,(0),0⟩,⟨0,0,0,(1),519⟩,⟨2,1036,1037,(0),0⟩,⟨0,0,0,(1),520⟩]
def fragment64 : Fragment := ⟨true,nodes64.map ScopedC.CData.nodeInitializer⟩
def file64 : File := ⟨"fact2_row0_part_064.inc",include_str "../../../../source/fact2_row0_part_064.inc"⟩
def tree64 : Tree Fragment := .leaf file64 fragment64
theorem bound64 : tree64.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes65 : List ScopedNumerical.Input.Node := [⟨2,1038,1039,(0),0⟩,⟨0,0,0,(1),521⟩,⟨2,1040,1041,(0),0⟩,⟨0,0,0,(1),522⟩,⟨2,1042,1043,(0),0⟩,⟨0,0,0,(1),523⟩,⟨2,1044,1045,(0),0⟩,⟨0,0,0,(1),524⟩,⟨2,1046,1047,(0),0⟩,⟨0,0,0,(1),525⟩,⟨2,1048,1049,(0),0⟩,⟨0,0,0,(1),526⟩,⟨2,1050,1051,(0),0⟩,⟨0,0,0,(1),527⟩,⟨2,1052,1053,(0),0⟩,⟨0,0,0,(1),528⟩]
def fragment65 : Fragment := ⟨true,nodes65.map ScopedC.CData.nodeInitializer⟩
def file65 : File := ⟨"fact2_row0_part_065.inc",include_str "../../../../source/fact2_row0_part_065.inc"⟩
def tree65 : Tree Fragment := .leaf file65 fragment65
theorem bound65 : tree65.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile59 : File := ⟨"fact2_row0_join_00107.inc",include_str "../../../../source/fact2_row0_join_00107.inc"⟩
def joinTree59 : Tree Fragment := .pair joinFile59 tree64 tree65
theorem joinBound59 : joinTree59.Bound (fun f file => renderFragment f = some file.text) := .pair bound64 bound65 (by decide +kernel)
def joinFile60 : File := ⟨"fact2_row0_join_00108.inc",include_str "../../../../source/fact2_row0_join_00108.inc"⟩
def joinTree60 : Tree Fragment := .pair joinFile60 tree63 joinTree59
theorem joinBound60 : joinTree60.Bound (fun f file => renderFragment f = some file.text) := .pair bound63 joinBound59 (by decide +kernel)
def joinFile61 : File := ⟨"fact2_row0_join_00109.inc",include_str "../../../../source/fact2_row0_join_00109.inc"⟩
def joinTree61 : Tree Fragment := .pair joinFile61 joinTree58 joinTree60
theorem joinBound61 : joinTree61.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound58 joinBound60 (by decide +kernel)
def joinFile62 : File := ⟨"fact2_row0_join_00110.inc",include_str "../../../../source/fact2_row0_join_00110.inc"⟩
def joinTree62 : Tree Fragment := .pair joinFile62 joinTree56 joinTree61
theorem joinBound62 : joinTree62.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound56 joinBound61 (by decide +kernel)
def joinFile63 : File := ⟨"fact2_row0_join_00111.inc",include_str "../../../../source/fact2_row0_join_00111.inc"⟩
def joinTree63 : Tree Fragment := .pair joinFile63 joinTree52 joinTree62
theorem joinBound63 : joinTree63.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound52 joinBound62 (by decide +kernel)
def nodes66 : List ScopedNumerical.Input.Node := [⟨2,1054,1055,(0),0⟩,⟨0,0,0,(1),529⟩,⟨2,1056,1057,(0),0⟩,⟨0,0,0,(1),530⟩,⟨2,1058,1059,(0),0⟩,⟨0,0,0,(1),531⟩,⟨2,1060,1061,(0),0⟩,⟨0,0,0,(1),532⟩,⟨2,1062,1063,(0),0⟩,⟨0,0,0,(1),533⟩,⟨2,1064,1065,(0),0⟩,⟨0,0,0,(1),534⟩,⟨2,1066,1067,(0),0⟩,⟨0,0,0,(1),535⟩,⟨2,1068,1069,(0),0⟩,⟨0,0,0,(1),536⟩]
def fragment66 : Fragment := ⟨true,nodes66.map ScopedC.CData.nodeInitializer⟩
def file66 : File := ⟨"fact2_row0_part_066.inc",include_str "../../../../source/fact2_row0_part_066.inc"⟩
def tree66 : Tree Fragment := .leaf file66 fragment66
theorem bound66 : tree66.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes67 : List ScopedNumerical.Input.Node := [⟨2,1070,1071,(0),0⟩,⟨0,0,0,(1),537⟩,⟨2,1072,1073,(0),0⟩,⟨0,0,0,(1),538⟩,⟨2,1074,1075,(0),0⟩,⟨0,0,0,(1),539⟩,⟨2,1076,1077,(0),0⟩,⟨0,0,0,(1),540⟩,⟨2,1078,1079,(0),0⟩,⟨0,0,0,(1),541⟩,⟨2,1080,1081,(0),0⟩,⟨0,0,0,(1),542⟩,⟨2,1082,1083,(0),0⟩,⟨0,0,0,(1),543⟩,⟨2,1084,1085,(0),0⟩,⟨0,0,0,(1),544⟩]
def fragment67 : Fragment := ⟨true,nodes67.map ScopedC.CData.nodeInitializer⟩
def file67 : File := ⟨"fact2_row0_part_067.inc",include_str "../../../../source/fact2_row0_part_067.inc"⟩
def tree67 : Tree Fragment := .leaf file67 fragment67
theorem bound67 : tree67.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile64 : File := ⟨"fact2_row0_join_00112.inc",include_str "../../../../source/fact2_row0_join_00112.inc"⟩
def joinTree64 : Tree Fragment := .pair joinFile64 tree66 tree67
theorem joinBound64 : joinTree64.Bound (fun f file => renderFragment f = some file.text) := .pair bound66 bound67 (by decide +kernel)
def nodes68 : List ScopedNumerical.Input.Node := [⟨2,1086,1087,(0),0⟩,⟨0,0,0,(1),545⟩,⟨2,1088,1089,(0),0⟩,⟨0,0,0,(1),546⟩,⟨2,1090,1091,(0),0⟩,⟨0,0,0,(1),547⟩,⟨2,1092,1093,(0),0⟩,⟨0,0,0,(1),548⟩,⟨2,1094,1095,(0),0⟩,⟨0,0,0,(1),549⟩,⟨2,1096,1097,(0),0⟩,⟨0,0,0,(1),550⟩,⟨2,1098,1099,(0),0⟩,⟨0,0,0,(1),551⟩,⟨2,1100,1101,(0),0⟩,⟨0,0,0,(1),552⟩]
def fragment68 : Fragment := ⟨true,nodes68.map ScopedC.CData.nodeInitializer⟩
def file68 : File := ⟨"fact2_row0_part_068.inc",include_str "../../../../source/fact2_row0_part_068.inc"⟩
def tree68 : Tree Fragment := .leaf file68 fragment68
theorem bound68 : tree68.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes69 : List ScopedNumerical.Input.Node := [⟨2,1102,1103,(0),0⟩,⟨0,0,0,(1),553⟩,⟨2,1104,1105,(0),0⟩,⟨0,0,0,(1),554⟩,⟨2,1106,1107,(0),0⟩,⟨0,0,0,(1),555⟩,⟨2,1108,1109,(0),0⟩,⟨0,0,0,(1),556⟩,⟨2,1110,1111,(0),0⟩,⟨0,0,0,(1),557⟩,⟨2,1112,1113,(0),0⟩,⟨0,0,0,(1),558⟩,⟨2,1114,1115,(0),0⟩,⟨0,0,0,(1),559⟩,⟨2,1116,1117,(0),0⟩,⟨0,0,0,(1),560⟩]
def fragment69 : Fragment := ⟨true,nodes69.map ScopedC.CData.nodeInitializer⟩
def file69 : File := ⟨"fact2_row0_part_069.inc",include_str "../../../../source/fact2_row0_part_069.inc"⟩
def tree69 : Tree Fragment := .leaf file69 fragment69
theorem bound69 : tree69.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes70 : List ScopedNumerical.Input.Node := [⟨2,1118,1119,(0),0⟩,⟨0,0,0,(1),561⟩,⟨2,1120,1121,(0),0⟩,⟨0,0,0,(1),562⟩,⟨2,1122,1123,(0),0⟩,⟨0,0,0,(1),563⟩,⟨2,1124,1125,(0),0⟩,⟨0,0,0,(1),564⟩,⟨2,1126,1127,(0),0⟩,⟨0,0,0,(1),565⟩,⟨2,1128,1129,(0),0⟩,⟨0,0,0,(1),566⟩,⟨2,1130,1131,(0),0⟩,⟨0,0,0,(1),567⟩,⟨2,1132,1133,(0),0⟩,⟨0,0,0,(1),568⟩]
def fragment70 : Fragment := ⟨true,nodes70.map ScopedC.CData.nodeInitializer⟩
def file70 : File := ⟨"fact2_row0_part_070.inc",include_str "../../../../source/fact2_row0_part_070.inc"⟩
def tree70 : Tree Fragment := .leaf file70 fragment70
theorem bound70 : tree70.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile65 : File := ⟨"fact2_row0_join_00113.inc",include_str "../../../../source/fact2_row0_join_00113.inc"⟩
def joinTree65 : Tree Fragment := .pair joinFile65 tree69 tree70
theorem joinBound65 : joinTree65.Bound (fun f file => renderFragment f = some file.text) := .pair bound69 bound70 (by decide +kernel)
def joinFile66 : File := ⟨"fact2_row0_join_00114.inc",include_str "../../../../source/fact2_row0_join_00114.inc"⟩
def joinTree66 : Tree Fragment := .pair joinFile66 tree68 joinTree65
theorem joinBound66 : joinTree66.Bound (fun f file => renderFragment f = some file.text) := .pair bound68 joinBound65 (by decide +kernel)
def joinFile67 : File := ⟨"fact2_row0_join_00115.inc",include_str "../../../../source/fact2_row0_join_00115.inc"⟩
def joinTree67 : Tree Fragment := .pair joinFile67 joinTree64 joinTree66
theorem joinBound67 : joinTree67.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound64 joinBound66 (by decide +kernel)
def nodes71 : List ScopedNumerical.Input.Node := [⟨2,1134,1135,(0),0⟩,⟨0,0,0,(1),569⟩,⟨2,1136,1137,(0),0⟩,⟨0,0,0,(1),570⟩,⟨2,1138,1139,(0),0⟩,⟨0,0,0,(1),571⟩,⟨2,1140,1141,(0),0⟩,⟨0,0,0,(1),572⟩,⟨2,1142,1143,(0),0⟩,⟨0,0,0,(1),573⟩,⟨2,1144,1145,(0),0⟩,⟨0,0,0,(1),574⟩,⟨2,1146,1147,(0),0⟩,⟨0,0,0,(1),575⟩,⟨2,1148,1149,(0),0⟩,⟨0,0,0,(1),576⟩]
def fragment71 : Fragment := ⟨true,nodes71.map ScopedC.CData.nodeInitializer⟩
def file71 : File := ⟨"fact2_row0_part_071.inc",include_str "../../../../source/fact2_row0_part_071.inc"⟩
def tree71 : Tree Fragment := .leaf file71 fragment71
theorem bound71 : tree71.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes72 : List ScopedNumerical.Input.Node := [⟨2,1150,1151,(0),0⟩,⟨0,0,0,(1),577⟩,⟨2,1152,1153,(0),0⟩,⟨0,0,0,(1),578⟩,⟨2,1154,1155,(0),0⟩,⟨0,0,0,(1),579⟩,⟨2,1156,1157,(0),0⟩,⟨0,0,0,(1),580⟩,⟨2,1158,1159,(0),0⟩,⟨0,0,0,(1),581⟩,⟨2,1160,1161,(0),0⟩,⟨0,0,0,(1),582⟩,⟨2,1162,1163,(0),0⟩,⟨0,0,0,(1),583⟩,⟨2,1164,1165,(0),0⟩,⟨0,0,0,(1),584⟩]
def fragment72 : Fragment := ⟨true,nodes72.map ScopedC.CData.nodeInitializer⟩
def file72 : File := ⟨"fact2_row0_part_072.inc",include_str "../../../../source/fact2_row0_part_072.inc"⟩
def tree72 : Tree Fragment := .leaf file72 fragment72
theorem bound72 : tree72.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes73 : List ScopedNumerical.Input.Node := [⟨2,1166,1167,(0),0⟩,⟨0,0,0,(1),585⟩,⟨2,1168,1169,(0),0⟩,⟨0,0,0,(1),586⟩,⟨2,1170,1171,(0),0⟩,⟨0,0,0,(1),587⟩,⟨2,1172,1173,(0),0⟩,⟨0,0,0,(1),588⟩,⟨2,1174,1175,(0),0⟩,⟨0,0,0,(1),589⟩,⟨2,1176,1177,(0),0⟩,⟨0,0,0,(1),590⟩,⟨2,1178,1179,(0),0⟩,⟨0,0,0,(1),591⟩,⟨2,1180,1181,(0),0⟩,⟨0,0,0,(1),592⟩]
def fragment73 : Fragment := ⟨true,nodes73.map ScopedC.CData.nodeInitializer⟩
def file73 : File := ⟨"fact2_row0_part_073.inc",include_str "../../../../source/fact2_row0_part_073.inc"⟩
def tree73 : Tree Fragment := .leaf file73 fragment73
theorem bound73 : tree73.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile68 : File := ⟨"fact2_row0_join_00116.inc",include_str "../../../../source/fact2_row0_join_00116.inc"⟩
def joinTree68 : Tree Fragment := .pair joinFile68 tree72 tree73
theorem joinBound68 : joinTree68.Bound (fun f file => renderFragment f = some file.text) := .pair bound72 bound73 (by decide +kernel)
def joinFile69 : File := ⟨"fact2_row0_join_00117.inc",include_str "../../../../source/fact2_row0_join_00117.inc"⟩
def joinTree69 : Tree Fragment := .pair joinFile69 tree71 joinTree68
theorem joinBound69 : joinTree69.Bound (fun f file => renderFragment f = some file.text) := .pair bound71 joinBound68 (by decide +kernel)
def nodes74 : List ScopedNumerical.Input.Node := [⟨2,1182,1183,(0),0⟩,⟨0,0,0,(1),593⟩,⟨2,1184,1185,(0),0⟩,⟨0,0,0,(1),594⟩,⟨2,1186,1187,(0),0⟩,⟨0,0,0,(1),595⟩,⟨2,1188,1189,(0),0⟩,⟨0,0,0,(1),596⟩,⟨2,1190,1191,(0),0⟩,⟨0,0,0,(1),597⟩,⟨2,1192,1193,(0),0⟩,⟨0,0,0,(1),598⟩,⟨2,1194,1195,(0),0⟩,⟨0,0,0,(1),599⟩,⟨2,1196,1197,(0),0⟩,⟨0,0,0,(1),600⟩]
def fragment74 : Fragment := ⟨true,nodes74.map ScopedC.CData.nodeInitializer⟩
def file74 : File := ⟨"fact2_row0_part_074.inc",include_str "../../../../source/fact2_row0_part_074.inc"⟩
def tree74 : Tree Fragment := .leaf file74 fragment74
theorem bound74 : tree74.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes75 : List ScopedNumerical.Input.Node := [⟨2,1198,1199,(0),0⟩,⟨0,0,0,(1),601⟩,⟨2,1200,1201,(0),0⟩,⟨0,0,0,(1),602⟩,⟨2,1202,1203,(0),0⟩,⟨0,0,0,(1),603⟩,⟨2,1204,1205,(0),0⟩,⟨0,0,0,(1),604⟩,⟨2,1206,1207,(0),0⟩,⟨0,0,0,(1),605⟩,⟨2,1208,1209,(0),0⟩,⟨0,0,0,(1),606⟩,⟨2,1210,1211,(0),0⟩,⟨0,0,0,(1),607⟩,⟨2,1212,1213,(0),0⟩,⟨0,0,0,(1),608⟩]
def fragment75 : Fragment := ⟨true,nodes75.map ScopedC.CData.nodeInitializer⟩
def file75 : File := ⟨"fact2_row0_part_075.inc",include_str "../../../../source/fact2_row0_part_075.inc"⟩
def tree75 : Tree Fragment := .leaf file75 fragment75
theorem bound75 : tree75.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes76 : List ScopedNumerical.Input.Node := [⟨2,1214,1215,(0),0⟩,⟨0,0,0,(1),609⟩,⟨2,1216,1217,(0),0⟩,⟨0,0,0,(1),610⟩,⟨2,1218,1219,(0),0⟩,⟨0,0,0,(1),611⟩,⟨2,1220,1221,(0),0⟩,⟨0,0,0,(1),612⟩,⟨2,1222,1223,(0),0⟩,⟨0,0,0,(1),613⟩,⟨2,1224,1225,(0),0⟩,⟨0,0,0,(1),614⟩,⟨2,1226,1227,(0),0⟩,⟨0,0,0,(1),615⟩,⟨2,1228,1229,(0),0⟩,⟨0,0,0,(1),616⟩]
def fragment76 : Fragment := ⟨true,nodes76.map ScopedC.CData.nodeInitializer⟩
def file76 : File := ⟨"fact2_row0_part_076.inc",include_str "../../../../source/fact2_row0_part_076.inc"⟩
def tree76 : Tree Fragment := .leaf file76 fragment76
theorem bound76 : tree76.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile70 : File := ⟨"fact2_row0_join_00118.inc",include_str "../../../../source/fact2_row0_join_00118.inc"⟩
def joinTree70 : Tree Fragment := .pair joinFile70 tree75 tree76
theorem joinBound70 : joinTree70.Bound (fun f file => renderFragment f = some file.text) := .pair bound75 bound76 (by decide +kernel)
def joinFile71 : File := ⟨"fact2_row0_join_00119.inc",include_str "../../../../source/fact2_row0_join_00119.inc"⟩
def joinTree71 : Tree Fragment := .pair joinFile71 tree74 joinTree70
theorem joinBound71 : joinTree71.Bound (fun f file => renderFragment f = some file.text) := .pair bound74 joinBound70 (by decide +kernel)
def joinFile72 : File := ⟨"fact2_row0_join_00120.inc",include_str "../../../../source/fact2_row0_join_00120.inc"⟩
def joinTree72 : Tree Fragment := .pair joinFile72 joinTree69 joinTree71
theorem joinBound72 : joinTree72.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound69 joinBound71 (by decide +kernel)
def joinFile73 : File := ⟨"fact2_row0_join_00121.inc",include_str "../../../../source/fact2_row0_join_00121.inc"⟩
def joinTree73 : Tree Fragment := .pair joinFile73 joinTree67 joinTree72
theorem joinBound73 : joinTree73.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound67 joinBound72 (by decide +kernel)
def nodes77 : List ScopedNumerical.Input.Node := [⟨2,1230,1231,(0),0⟩,⟨0,0,0,(1),617⟩,⟨2,1232,1233,(0),0⟩,⟨0,0,0,(1),618⟩,⟨2,1234,1235,(0),0⟩,⟨0,0,0,(1),619⟩,⟨2,1236,1237,(0),0⟩,⟨0,0,0,(1),620⟩,⟨2,1238,1239,(0),0⟩,⟨0,0,0,(1),621⟩,⟨2,1240,1241,(0),0⟩,⟨0,0,0,(1),622⟩,⟨2,1242,1243,(0),0⟩,⟨0,0,0,(1),623⟩,⟨2,1244,1245,(0),0⟩,⟨0,0,0,(1),624⟩]
def fragment77 : Fragment := ⟨true,nodes77.map ScopedC.CData.nodeInitializer⟩
def file77 : File := ⟨"fact2_row0_part_077.inc",include_str "../../../../source/fact2_row0_part_077.inc"⟩
def tree77 : Tree Fragment := .leaf file77 fragment77
theorem bound77 : tree77.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes78 : List ScopedNumerical.Input.Node := [⟨2,1246,1247,(0),0⟩,⟨0,0,0,(1),625⟩,⟨2,1248,1249,(0),0⟩,⟨0,0,0,(1),626⟩,⟨2,1250,1251,(0),0⟩,⟨0,0,0,(1),627⟩,⟨2,1252,1253,(0),0⟩,⟨0,0,0,(1),628⟩,⟨2,1254,1255,(0),0⟩,⟨0,0,0,(1),629⟩,⟨2,1256,1257,(0),0⟩,⟨0,0,0,(1),630⟩,⟨2,1258,1259,(0),0⟩,⟨0,0,0,(1),631⟩,⟨2,1260,1261,(0),0⟩,⟨0,0,0,(1),632⟩]
def fragment78 : Fragment := ⟨true,nodes78.map ScopedC.CData.nodeInitializer⟩
def file78 : File := ⟨"fact2_row0_part_078.inc",include_str "../../../../source/fact2_row0_part_078.inc"⟩
def tree78 : Tree Fragment := .leaf file78 fragment78
theorem bound78 : tree78.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile74 : File := ⟨"fact2_row0_join_00122.inc",include_str "../../../../source/fact2_row0_join_00122.inc"⟩
def joinTree74 : Tree Fragment := .pair joinFile74 tree77 tree78
theorem joinBound74 : joinTree74.Bound (fun f file => renderFragment f = some file.text) := .pair bound77 bound78 (by decide +kernel)
def nodes79 : List ScopedNumerical.Input.Node := [⟨2,1262,1263,(0),0⟩,⟨0,0,0,(1),633⟩,⟨2,1264,1265,(0),0⟩,⟨0,0,0,(1),634⟩,⟨2,1266,1267,(0),0⟩,⟨0,0,0,(1),635⟩,⟨2,1268,1269,(0),0⟩,⟨0,0,0,(1),636⟩,⟨2,1270,1271,(0),0⟩,⟨0,0,0,(1),637⟩,⟨2,1272,1273,(0),0⟩,⟨0,0,0,(1),638⟩,⟨2,1274,1275,(0),0⟩,⟨0,0,0,(1),639⟩,⟨2,1276,1277,(0),0⟩,⟨0,0,0,(1),640⟩]
def fragment79 : Fragment := ⟨true,nodes79.map ScopedC.CData.nodeInitializer⟩
def file79 : File := ⟨"fact2_row0_part_079.inc",include_str "../../../../source/fact2_row0_part_079.inc"⟩
def tree79 : Tree Fragment := .leaf file79 fragment79
theorem bound79 : tree79.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes80 : List ScopedNumerical.Input.Node := [⟨2,1278,1279,(0),0⟩,⟨0,0,0,(1),641⟩,⟨2,1280,1281,(0),0⟩,⟨0,0,0,(1),642⟩,⟨2,1282,1283,(0),0⟩,⟨0,0,0,(1),643⟩,⟨2,1284,1285,(0),0⟩,⟨0,0,0,(1),644⟩,⟨2,1286,1287,(0),0⟩,⟨0,0,0,(1),645⟩,⟨2,1288,1289,(0),0⟩,⟨0,0,0,(1),646⟩,⟨2,1290,1291,(0),0⟩,⟨0,0,0,(1),647⟩,⟨2,1292,1293,(0),0⟩,⟨0,0,0,(1),648⟩]
def fragment80 : Fragment := ⟨true,nodes80.map ScopedC.CData.nodeInitializer⟩
def file80 : File := ⟨"fact2_row0_part_080.inc",include_str "../../../../source/fact2_row0_part_080.inc"⟩
def tree80 : Tree Fragment := .leaf file80 fragment80
theorem bound80 : tree80.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes81 : List ScopedNumerical.Input.Node := [⟨2,1294,1295,(0),0⟩,⟨0,0,0,(1),649⟩,⟨2,1296,1297,(0),0⟩,⟨0,0,0,(1),650⟩,⟨2,1298,1299,(0),0⟩,⟨0,0,0,(1),651⟩,⟨2,1300,1301,(0),0⟩,⟨0,0,0,(1),652⟩,⟨2,1302,1303,(0),0⟩,⟨0,0,0,(1),653⟩,⟨2,1304,1305,(0),0⟩,⟨0,0,0,(1),654⟩,⟨2,1306,1307,(0),0⟩,⟨0,0,0,(1),655⟩,⟨2,1308,1309,(0),0⟩,⟨0,0,0,(1),656⟩]
def fragment81 : Fragment := ⟨true,nodes81.map ScopedC.CData.nodeInitializer⟩
def file81 : File := ⟨"fact2_row0_part_081.inc",include_str "../../../../source/fact2_row0_part_081.inc"⟩
def tree81 : Tree Fragment := .leaf file81 fragment81
theorem bound81 : tree81.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile75 : File := ⟨"fact2_row0_join_00123.inc",include_str "../../../../source/fact2_row0_join_00123.inc"⟩
def joinTree75 : Tree Fragment := .pair joinFile75 tree80 tree81
theorem joinBound75 : joinTree75.Bound (fun f file => renderFragment f = some file.text) := .pair bound80 bound81 (by decide +kernel)
def joinFile76 : File := ⟨"fact2_row0_join_00124.inc",include_str "../../../../source/fact2_row0_join_00124.inc"⟩
def joinTree76 : Tree Fragment := .pair joinFile76 tree79 joinTree75
theorem joinBound76 : joinTree76.Bound (fun f file => renderFragment f = some file.text) := .pair bound79 joinBound75 (by decide +kernel)
def joinFile77 : File := ⟨"fact2_row0_join_00125.inc",include_str "../../../../source/fact2_row0_join_00125.inc"⟩
def joinTree77 : Tree Fragment := .pair joinFile77 joinTree74 joinTree76
theorem joinBound77 : joinTree77.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound74 joinBound76 (by decide +kernel)
def nodes82 : List ScopedNumerical.Input.Node := [⟨2,1310,1311,(0),0⟩,⟨0,0,0,(1),657⟩,⟨2,1312,1313,(0),0⟩,⟨0,0,0,(1),658⟩,⟨2,1314,1315,(0),0⟩,⟨0,0,0,(1),659⟩,⟨2,1316,1317,(0),0⟩,⟨0,0,0,(1),660⟩,⟨2,1318,1319,(0),0⟩,⟨0,0,0,(1),661⟩,⟨2,1320,1321,(0),0⟩,⟨0,0,0,(1),662⟩,⟨2,1322,1323,(0),0⟩,⟨0,0,0,(1),663⟩,⟨2,1324,1325,(0),0⟩,⟨0,0,0,(1),664⟩]
def fragment82 : Fragment := ⟨true,nodes82.map ScopedC.CData.nodeInitializer⟩
def file82 : File := ⟨"fact2_row0_part_082.inc",include_str "../../../../source/fact2_row0_part_082.inc"⟩
def tree82 : Tree Fragment := .leaf file82 fragment82
theorem bound82 : tree82.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes83 : List ScopedNumerical.Input.Node := [⟨2,1326,1327,(0),0⟩,⟨0,0,0,(1),665⟩,⟨2,1328,1329,(0),0⟩,⟨0,0,0,(1),666⟩,⟨2,1330,1331,(0),0⟩,⟨0,0,0,(1),667⟩,⟨2,1332,1333,(0),0⟩,⟨0,0,0,(1),668⟩,⟨2,1334,1335,(0),0⟩,⟨0,0,0,(1),669⟩,⟨2,1336,1337,(0),0⟩,⟨0,0,0,(1),670⟩,⟨2,1338,1339,(0),0⟩,⟨0,0,0,(1),671⟩,⟨2,1340,1341,(0),0⟩,⟨0,0,0,(1),672⟩]
def fragment83 : Fragment := ⟨true,nodes83.map ScopedC.CData.nodeInitializer⟩
def file83 : File := ⟨"fact2_row0_part_083.inc",include_str "../../../../source/fact2_row0_part_083.inc"⟩
def tree83 : Tree Fragment := .leaf file83 fragment83
theorem bound83 : tree83.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes84 : List ScopedNumerical.Input.Node := [⟨2,1342,1343,(0),0⟩,⟨0,0,0,(1),673⟩,⟨2,1344,1345,(0),0⟩,⟨0,0,0,(1),674⟩,⟨2,1346,1347,(0),0⟩,⟨0,0,0,(1),675⟩,⟨2,1348,1349,(0),0⟩,⟨0,0,0,(1),676⟩,⟨2,1350,1351,(0),0⟩,⟨0,0,0,(1),677⟩,⟨2,1352,1353,(0),0⟩,⟨0,0,0,(1),678⟩,⟨2,1354,1355,(0),0⟩,⟨0,0,0,(1),679⟩,⟨2,1356,1357,(0),0⟩,⟨0,0,0,(1),680⟩]
def fragment84 : Fragment := ⟨true,nodes84.map ScopedC.CData.nodeInitializer⟩
def file84 : File := ⟨"fact2_row0_part_084.inc",include_str "../../../../source/fact2_row0_part_084.inc"⟩
def tree84 : Tree Fragment := .leaf file84 fragment84
theorem bound84 : tree84.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile78 : File := ⟨"fact2_row0_join_00126.inc",include_str "../../../../source/fact2_row0_join_00126.inc"⟩
def joinTree78 : Tree Fragment := .pair joinFile78 tree83 tree84
theorem joinBound78 : joinTree78.Bound (fun f file => renderFragment f = some file.text) := .pair bound83 bound84 (by decide +kernel)
def joinFile79 : File := ⟨"fact2_row0_join_00127.inc",include_str "../../../../source/fact2_row0_join_00127.inc"⟩
def joinTree79 : Tree Fragment := .pair joinFile79 tree82 joinTree78
theorem joinBound79 : joinTree79.Bound (fun f file => renderFragment f = some file.text) := .pair bound82 joinBound78 (by decide +kernel)
def nodes85 : List ScopedNumerical.Input.Node := [⟨2,1358,1359,(0),0⟩,⟨0,0,0,(1),681⟩,⟨2,1360,1361,(0),0⟩,⟨0,0,0,(1),682⟩,⟨2,1362,1363,(0),0⟩,⟨0,0,0,(1),683⟩,⟨2,1364,1365,(0),0⟩,⟨0,0,0,(1),684⟩,⟨2,1366,1367,(0),0⟩,⟨0,0,0,(1),685⟩,⟨2,1368,1369,(0),0⟩,⟨0,0,0,(1),686⟩,⟨2,1370,1371,(0),0⟩,⟨0,0,0,(1),687⟩,⟨2,1372,1373,(0),0⟩,⟨0,0,0,(1),688⟩]
def fragment85 : Fragment := ⟨true,nodes85.map ScopedC.CData.nodeInitializer⟩
def file85 : File := ⟨"fact2_row0_part_085.inc",include_str "../../../../source/fact2_row0_part_085.inc"⟩
def tree85 : Tree Fragment := .leaf file85 fragment85
theorem bound85 : tree85.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes86 : List ScopedNumerical.Input.Node := [⟨2,1374,1375,(0),0⟩,⟨0,0,0,(1),689⟩,⟨2,1376,1377,(0),0⟩,⟨0,0,0,(1),690⟩,⟨2,1378,1379,(0),0⟩,⟨0,0,0,(1),691⟩,⟨2,1380,1381,(0),0⟩,⟨0,0,0,(1),692⟩,⟨2,1382,1383,(0),0⟩,⟨0,0,0,(1),693⟩,⟨2,1384,1385,(0),0⟩,⟨0,0,0,(1),694⟩,⟨2,1386,1387,(0),0⟩,⟨0,0,0,(1),695⟩,⟨2,1388,1389,(0),0⟩,⟨0,0,0,(1),696⟩]
def fragment86 : Fragment := ⟨true,nodes86.map ScopedC.CData.nodeInitializer⟩
def file86 : File := ⟨"fact2_row0_part_086.inc",include_str "../../../../source/fact2_row0_part_086.inc"⟩
def tree86 : Tree Fragment := .leaf file86 fragment86
theorem bound86 : tree86.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def nodes87 : List ScopedNumerical.Input.Node := [⟨2,1390,1391,(0),0⟩,⟨0,0,0,(1),697⟩,⟨2,1392,1393,(0),0⟩,⟨0,0,0,(1),698⟩,⟨2,1394,1395,(0),0⟩,⟨0,0,0,(1),699⟩,⟨2,1396,1397,(0),0⟩,⟨0,0,0,(1),700⟩,⟨2,1398,1399,(0),0⟩,⟨0,0,0,(700),1⟩,⟨7,1401,0,(0),0⟩,⟨4,1402,0,(0),0⟩,⟨2,1400,1403,(0),0⟩]
def fragment87 : Fragment := ⟨true,nodes87.map ScopedC.CData.nodeInitializer⟩
def file87 : File := ⟨"fact2_row0_part_087.inc",include_str "../../../../source/fact2_row0_part_087.inc"⟩
def tree87 : Tree Fragment := .leaf file87 fragment87
theorem bound87 : tree87.Bound (fun f file => renderFragment f = some file.text) := .leaf (by decide +kernel)
def joinFile80 : File := ⟨"fact2_row0_join_00128.inc",include_str "../../../../source/fact2_row0_join_00128.inc"⟩
def joinTree80 : Tree Fragment := .pair joinFile80 tree86 tree87
theorem joinBound80 : joinTree80.Bound (fun f file => renderFragment f = some file.text) := .pair bound86 bound87 (by decide +kernel)
def joinFile81 : File := ⟨"fact2_row0_join_00129.inc",include_str "../../../../source/fact2_row0_join_00129.inc"⟩
def joinTree81 : Tree Fragment := .pair joinFile81 tree85 joinTree80
theorem joinBound81 : joinTree81.Bound (fun f file => renderFragment f = some file.text) := .pair bound85 joinBound80 (by decide +kernel)
def joinFile82 : File := ⟨"fact2_row0_join_00130.inc",include_str "../../../../source/fact2_row0_join_00130.inc"⟩
def joinTree82 : Tree Fragment := .pair joinFile82 joinTree79 joinTree81
theorem joinBound82 : joinTree82.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound79 joinBound81 (by decide +kernel)
def joinFile83 : File := ⟨"fact2_row0_join_00131.inc",include_str "../../../../source/fact2_row0_join_00131.inc"⟩
def joinTree83 : Tree Fragment := .pair joinFile83 joinTree77 joinTree82
theorem joinBound83 : joinTree83.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound77 joinBound82 (by decide +kernel)
def joinFile84 : File := ⟨"fact2_row0_join_00132.inc",include_str "../../../../source/fact2_row0_join_00132.inc"⟩
def joinTree84 : Tree Fragment := .pair joinFile84 joinTree73 joinTree83
theorem joinBound84 : joinTree84.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound73 joinBound83 (by decide +kernel)
def joinFile85 : File := ⟨"fact2_row0_join_00133.inc",include_str "../../../../source/fact2_row0_join_00133.inc"⟩
def joinTree85 : Tree Fragment := .pair joinFile85 joinTree63 joinTree84
theorem joinBound85 : joinTree85.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound63 joinBound84 (by decide +kernel)
def joinFile86 : File := ⟨"fact2_row0_join_00134.inc",include_str "../../../../source/fact2_row0_join_00134.inc"⟩
def joinTree86 : Tree Fragment := .pair joinFile86 joinTree42 joinTree85
theorem joinBound86 : joinTree86.Bound (fun f file => renderFragment f = some file.text) := .pair joinBound42 joinBound85 (by decide +kernel)
def chunks : List (List ScopedNumerical.Input.Node) := [nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12,nodes13,nodes14,nodes15,nodes16,nodes17,nodes18,nodes19,nodes20,nodes21,nodes22,nodes23,nodes24,nodes25,nodes26,nodes27,nodes28,nodes29,nodes30,nodes31,nodes32,nodes33,nodes34,nodes35,nodes36,nodes37,nodes38,nodes39,nodes40,nodes41,nodes42,nodes43,nodes44,nodes45,nodes46,nodes47,nodes48,nodes49,nodes50,nodes51,nodes52,nodes53,nodes54,nodes55,nodes56,nodes57,nodes58,nodes59,nodes60,nodes61,nodes62,nodes63,nodes64,nodes65,nodes66,nodes67,nodes68,nodes69,nodes70,nodes71,nodes72,nodes73,nodes74,nodes75,nodes76,nodes77,nodes78,nodes79,nodes80,nodes81,nodes82,nodes83,nodes84,nodes85,nodes86,nodes87]
theorem nodes_exact : chunks.flatten = ScopedNumerical.InputData.Fact2Row0.nodes := by rfl
def body : Tree Fragment := joinTree86
theorem body_bound : body.Bound (fun f file => renderFragment f = some file.text) := joinBound86
theorem values_exact : body.values = [fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12,fragment13,fragment14,fragment15,fragment16,fragment17,fragment18,fragment19,fragment20,fragment21,fragment22,fragment23,fragment24,fragment25,fragment26,fragment27,fragment28,fragment29,fragment30,fragment31,fragment32,fragment33,fragment34,fragment35,fragment36,fragment37,fragment38,fragment39,fragment40,fragment41,fragment42,fragment43,fragment44,fragment45,fragment46,fragment47,fragment48,fragment49,fragment50,fragment51,fragment52,fragment53,fragment54,fragment55,fragment56,fragment57,fragment58,fragment59,fragment60,fragment61,fragment62,fragment63,fragment64,fragment65,fragment66,fragment67,fragment68,fragment69,fragment70,fragment71,fragment72,fragment73,fragment74,fragment75,fragment76,fragment77,fragment78,fragment79,fragment80,fragment81,fragment82,fragment83,fragment84,fragment85,fragment86,fragment87] := by rfl
theorem elements_exact : body.values.flatMap Fragment.elements = ScopedNumerical.InputData.Fact2Row0.nodes.map ScopedC.CData.nodeInitializer := by
  have hx : body.values.map Fragment.elements = chunks.map (List.map ScopedC.CData.nodeInitializer) := by rfl
  rw [List.flatMap_def,hx,← List.map_flatten,nodes_exact]
theorem follows : FragmentsFollow body.values := by
  rw [values_exact]
  simp [FragmentsFollow,fragment0,fragment1,fragment2,fragment3,fragment4,fragment5,fragment6,fragment7,fragment8,fragment9,fragment10,fragment11,fragment12,fragment13,fragment14,fragment15,fragment16,fragment17,fragment18,fragment19,fragment20,fragment21,fragment22,fragment23,fragment24,fragment25,fragment26,fragment27,fragment28,fragment29,fragment30,fragment31,fragment32,fragment33,fragment34,fragment35,fragment36,fragment37,fragment38,fragment39,fragment40,fragment41,fragment42,fragment43,fragment44,fragment45,fragment46,fragment47,fragment48,fragment49,fragment50,fragment51,fragment52,fragment53,fragment54,fragment55,fragment56,fragment57,fragment58,fragment59,fragment60,fragment61,fragment62,fragment63,fragment64,fragment65,fragment66,fragment67,fragment68,fragment69,fragment70,fragment71,fragment72,fragment73,fragment74,fragment75,fragment76,fragment77,fragment78,fragment79,fragment80,fragment81,fragment82,fragment83,fragment84,fragment85,fragment86,fragment87,nodes0,nodes1,nodes2,nodes3,nodes4,nodes5,nodes6,nodes7,nodes8,nodes9,nodes10,nodes11,nodes12,nodes13,nodes14,nodes15,nodes16,nodes17,nodes18,nodes19,nodes20,nodes21,nodes22,nodes23,nodes24,nodes25,nodes26,nodes27,nodes28,nodes29,nodes30,nodes31,nodes32,nodes33,nodes34,nodes35,nodes36,nodes37,nodes38,nodes39,nodes40,nodes41,nodes42,nodes43,nodes44,nodes45,nodes46,nodes47,nodes48,nodes49,nodes50,nodes51,nodes52,nodes53,nodes54,nodes55,nodes56,nodes57,nodes58,nodes59,nodes60,nodes61,nodes62,nodes63,nodes64,nodes65,nodes66,nodes67,nodes68,nodes69,nodes70,nodes71,nodes72,nodes73,nodes74,nodes75,nodes76,nodes77,nodes78,nodes79,nodes80,nodes81,nodes82,nodes83,nodes84,nodes85,nodes86,nodes87]
def actual : File := ⟨"fact2_row0_array.inc",include_str "../../../../source/fact2_row0_array.inc"⟩
def declaration : Decl := ScopedC.CData.nodeArray "fact2_row0" ScopedNumerical.InputData.Fact2Row0.nodes
theorem array_bound : ArrayBound declaration actual := by
  refine ⟨body,body_bound,follows,?_,?_⟩
  · rw [elements_exact]
    simp only [declaration,ScopedC.CData.nodeArray,List.length_map]
  · rw [elements_exact,List.length_map,ScopedNumerical.InputData.Fact2Row0.node_count]
    decide +kernel
def piece : Piece := .array declaration
theorem bound : Piece.Bound piece actual := .array array_bound
#print axioms bound
end ScopedC.SourceBundle.Arrays.Fact2Row0

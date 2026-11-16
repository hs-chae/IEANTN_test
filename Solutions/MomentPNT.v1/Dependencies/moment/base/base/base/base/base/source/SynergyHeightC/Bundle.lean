import ScopedC.SourceBundle.FunctionTree
import SynergyC.Header
import SynergyHeightC.GlobalRenderers
import SynergyHeightC.FunctionTrees
import SynergyHeightC.Render_fail
import SynergyHeightC.Render_addU
import SynergyHeightC.Render_mulU
import SynergyHeightC.Render_ceilDiv
import SynergyHeightC.Render_rat
import SynergyHeightC.Render_unit
import SynergyHeightC.Render_zero
import SynergyHeightC.Render_add
import SynergyHeightC.Render_mul
import SynergyHeightC.Render_divI
import SynergyHeightC.Render_divN
import SynergyHeightC.Render_positiveSub
import SynergyHeightC.Render_expNeg
import SynergyHeightC.Render_atanh2
import SynergyHeightC.Render_logPos
import SynergyHeightC.Render_floorCube
import SynergyHeightC.Render_cubeRoot
import SynergyHeightC.Render_gaussianCell
import SynergyHeightC.Render_archived_basis_main
import SynergyHeightC.Render_expPositiveRaw
import SynergyHeightC.Render_expPositive
import SynergyHeightC.Render_logTight
import SynergyHeightC.Render_squareI
import SynergyHeightC.Render_inverseI
import SynergyHeightC.Render_sqrtInterval
import SynergyHeightC.Render_emitU
import SynergyHeightC.Render_emitI
import SynergyHeightC.Render_initializeConstants
import SynergyHeightC.Render_rightRawCap
import SynergyHeightC.Render_leftRawCap
import SynergyHeightC.Render_heightPair
import SynergyHeightC.Render_expNegAny
import SynergyHeightC.Render_paired
import SynergyHeightC.Render_subExact
import SynergyHeightC.Render_sqrtMatch
namespace SynergyHeightC.Bundle
open ScopedC.Syntax ScopedC.SourceBundle
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
inductive Piece where
 | prelude
 | typeDecl (d:SynergyC.Header.TypeDecl)
 | global (d:Decl)
 | function (f:Function)
inductive Piece.Bound : Piece→File→Prop where
 | prelude {file} (h:file.text=SynergyC.Header.externalPrelude):Bound .prelude file
 | typeDecl {d file} (h:file.text=SynergyC.Header.renderType d):Bound (.typeDecl d) file
 | global {d file} (h:(do pure ("static "++(←renderDecl d)++";\n"))=some file.text):Bound (.global d) file
 | function {f file} (h:renderFunction f=some file.text):Bound (.function f) file
 | functionTree {f file body} (h:FunctionTree.Bound f file body):Bound (.function f) file

def file0 : File := ⟨"prelude.inc",include_str "../../height-bundle-source-v3/prelude.inc"⟩
def piece0 : Piece := .prelude
theorem bound0 : Piece.Bound piece0 file0 := .prelude (by rfl)
def tree0 : ScopedC.SourceBundle.Tree Piece := .leaf file0 piece0
theorem tree_bound0 : tree0.Bound Piece.Bound := .leaf bound0
def file1 : File := ⟨"type_U.inc",include_str "../../height-bundle-source-v3/type_U.inc"⟩
def piece1 : Piece := .typeDecl (.unsignedAlias "U" 512)
theorem bound1 : Piece.Bound piece1 file1 := .typeDecl (by rfl)
def tree1 : ScopedC.SourceBundle.Tree Piece := .leaf file1 piece1
theorem tree_bound1 : tree1.Bound Piece.Bound := .leaf bound1
def file2 : File := ⟨"type_I.inc",include_str "../../height-bundle-source-v3/type_I.inc"⟩
def piece2 : Piece := .typeDecl (.record "I" [("U","lo"),("U","hi")])
theorem bound2 : Piece.Bound piece2 file2 := .typeDecl (by rfl)
def tree2 : ScopedC.SourceBundle.Tree Piece := .leaf file2 piece2
theorem tree_bound2 : tree2.Bound Piece.Bound := .leaf bound2
def file3 : File := ⟨"global_S.inc",include_str "../../height-bundle-source-v3/global_S.inc"⟩
def piece3 : Piece := .global Generated.g_S
theorem bound3 : Piece.Bound piece3 file3 := .global (by simpa only [file3] using Generated.render_global_S)
def tree3 : ScopedC.SourceBundle.Tree Piece := .leaf file3 piece3
theorem tree_bound3 : tree3.Bound Piece.Bound := .leaf bound3
def file4 : File := ⟨"global_MAXU.inc",include_str "../../height-bundle-source-v3/global_MAXU.inc"⟩
def piece4 : Piece := .global Generated.g_MAXU
theorem bound4 : Piece.Bound piece4 file4 := .global (by simpa only [file4] using Generated.render_global_MAXU)
def tree4 : ScopedC.SourceBundle.Tree Piece := .leaf file4 piece4
theorem tree_bound4 : tree4.Bound Piece.Bound := .leaf bound4
def file5 : File := ⟨"global_ln2.inc",include_str "../../height-bundle-source-v3/global_ln2.inc"⟩
def piece5 : Piece := .global Generated.g_ln2
theorem bound5 : Piece.Bound piece5 file5 := .global (by simpa only [file5] using Generated.render_global_ln2)
def tree5 : ScopedC.SourceBundle.Tree Piece := .leaf file5 piece5
theorem tree_bound5 : tree5.Bound Piece.Bound := .leaf bound5
def file6 : File := ⟨"function_fail.inc",include_str "../../height-bundle-source-v3/function_fail.inc"⟩
def piece6 : Piece := .function Generated.f_fail
theorem bound6 : Piece.Bound piece6 file6 := .function (by simpa only [file6] using Generated.render_fail)
def tree6 : ScopedC.SourceBundle.Tree Piece := .leaf file6 piece6
theorem tree_bound6 : tree6.Bound Piece.Bound := .leaf bound6
def file7 : File := ⟨"function_addU.inc",include_str "../../height-bundle-source-v3/function_addU.inc"⟩
def piece7 : Piece := .function Generated.f_addU
theorem bound7 : Piece.Bound piece7 file7 := .function (by simpa only [file7] using Generated.render_addU)
def tree7 : ScopedC.SourceBundle.Tree Piece := .leaf file7 piece7
theorem tree_bound7 : tree7.Bound Piece.Bound := .leaf bound7
def file8 : File := ⟨"function_mulU.inc",include_str "../../height-bundle-source-v3/function_mulU.inc"⟩
def piece8 : Piece := .function Generated.f_mulU
theorem bound8 : Piece.Bound piece8 file8 := .function (by simpa only [file8] using Generated.render_mulU)
def tree8 : ScopedC.SourceBundle.Tree Piece := .leaf file8 piece8
theorem tree_bound8 : tree8.Bound Piece.Bound := .leaf bound8
def file9 : File := ⟨"function_ceilDiv.inc",include_str "../../height-bundle-source-v3/function_ceilDiv.inc"⟩
def piece9 : Piece := .function Generated.f_ceilDiv
theorem bound9 : Piece.Bound piece9 file9 := .function (by simpa only [file9] using Generated.render_ceilDiv)
def tree9 : ScopedC.SourceBundle.Tree Piece := .leaf file9 piece9
theorem tree_bound9 : tree9.Bound Piece.Bound := .leaf bound9
def file10 : File := ⟨"function_rat.inc",include_str "../../height-bundle-source-v3/function_rat.inc"⟩
def piece10 : Piece := .function Generated.f_rat
theorem bound10 : Piece.Bound piece10 file10 := .function (by simpa only [file10] using Generated.render_rat)
def tree10 : ScopedC.SourceBundle.Tree Piece := .leaf file10 piece10
theorem tree_bound10 : tree10.Bound Piece.Bound := .leaf bound10
def file11 : File := ⟨"function_unit.inc",include_str "../../height-bundle-source-v3/function_unit.inc"⟩
def piece11 : Piece := .function Generated.f_unit
theorem bound11 : Piece.Bound piece11 file11 := .function (by simpa only [file11] using Generated.render_unit)
def tree11 : ScopedC.SourceBundle.Tree Piece := .leaf file11 piece11
theorem tree_bound11 : tree11.Bound Piece.Bound := .leaf bound11
def file12 : File := ⟨"function_zero.inc",include_str "../../height-bundle-source-v3/function_zero.inc"⟩
def piece12 : Piece := .function Generated.f_zero
theorem bound12 : Piece.Bound piece12 file12 := .function (by simpa only [file12] using Generated.render_zero)
def tree12 : ScopedC.SourceBundle.Tree Piece := .leaf file12 piece12
theorem tree_bound12 : tree12.Bound Piece.Bound := .leaf bound12
def file13 : File := ⟨"function_add.inc",include_str "../../height-bundle-source-v3/function_add.inc"⟩
def piece13 : Piece := .function Generated.f_add
theorem bound13 : Piece.Bound piece13 file13 := .function (by simpa only [file13] using Generated.render_add)
def tree13 : ScopedC.SourceBundle.Tree Piece := .leaf file13 piece13
theorem tree_bound13 : tree13.Bound Piece.Bound := .leaf bound13
def file14 : File := ⟨"function_mul.inc",include_str "../../height-bundle-source-v3/function_mul.inc"⟩
def piece14 : Piece := .function Generated.f_mul
theorem bound14 : Piece.Bound piece14 file14 := .function (by simpa only [file14] using Generated.render_mul)
def tree14 : ScopedC.SourceBundle.Tree Piece := .leaf file14 piece14
theorem tree_bound14 : tree14.Bound Piece.Bound := .leaf bound14
def file15 : File := ⟨"function_divI.inc",include_str "../../height-bundle-source-v3/function_divI.inc"⟩
def piece15 : Piece := .function Generated.f_divI
theorem bound15 : Piece.Bound piece15 file15 := .function (by simpa only [file15] using Generated.render_divI)
def tree15 : ScopedC.SourceBundle.Tree Piece := .leaf file15 piece15
theorem tree_bound15 : tree15.Bound Piece.Bound := .leaf bound15
def file16 : File := ⟨"function_divN.inc",include_str "../../height-bundle-source-v3/function_divN.inc"⟩
def piece16 : Piece := .function Generated.f_divN
theorem bound16 : Piece.Bound piece16 file16 := .function (by simpa only [file16] using Generated.render_divN)
def tree16 : ScopedC.SourceBundle.Tree Piece := .leaf file16 piece16
theorem tree_bound16 : tree16.Bound Piece.Bound := .leaf bound16
def file17 : File := ⟨"function_positiveSub.inc",include_str "../../height-bundle-source-v3/function_positiveSub.inc"⟩
def piece17 : Piece := .function Generated.f_positiveSub
theorem bound17 : Piece.Bound piece17 file17 := .function (by simpa only [file17] using Generated.render_positiveSub)
def tree17 : ScopedC.SourceBundle.Tree Piece := .leaf file17 piece17
theorem tree_bound17 : tree17.Bound Piece.Bound := .leaf bound17
def file18 : File := ⟨"function_expNeg.inc",include_str "../../height-bundle-source-v3/function_expNeg.inc"⟩
def piece18 : Piece := .function Generated.f_expNeg
theorem bound18 : Piece.Bound piece18 file18 := .function (by simpa only [file18] using Generated.render_expNeg)
def tree18 : ScopedC.SourceBundle.Tree Piece := .leaf file18 piece18
theorem tree_bound18 : tree18.Bound Piece.Bound := .leaf bound18
def file19 : File := ⟨"function_atanh2.inc",include_str "../../height-bundle-source-v3/function_atanh2.inc"⟩
def piece19 : Piece := .function Generated.f_atanh2
theorem bound19 : Piece.Bound piece19 file19 := .function (by simpa only [file19] using Generated.render_atanh2)
def tree19 : ScopedC.SourceBundle.Tree Piece := .leaf file19 piece19
theorem tree_bound19 : tree19.Bound Piece.Bound := .leaf bound19
def file20 : File := ⟨"function_logPos.inc",include_str "../../height-bundle-source-v3/function_logPos.inc"⟩
def piece20 : Piece := .function Generated.f_logPos
theorem bound20 : Piece.Bound piece20 file20 := .function (by simpa only [file20] using Generated.render_logPos)
def tree20 : ScopedC.SourceBundle.Tree Piece := .leaf file20 piece20
theorem tree_bound20 : tree20.Bound Piece.Bound := .leaf bound20
def file21 : File := ⟨"function_floorCube.inc",include_str "../../height-bundle-source-v3/function_floorCube.inc"⟩
def piece21 : Piece := .function Generated.f_floorCube
theorem bound21 : Piece.Bound piece21 file21 := .function (by simpa only [file21] using Generated.render_floorCube)
def tree21 : ScopedC.SourceBundle.Tree Piece := .leaf file21 piece21
theorem tree_bound21 : tree21.Bound Piece.Bound := .leaf bound21
def file22 : File := ⟨"function_cubeRoot.inc",include_str "../../height-bundle-source-v3/function_cubeRoot.inc"⟩
def piece22 : Piece := .function Generated.f_cubeRoot
theorem bound22 : Piece.Bound piece22 file22 := .function (by simpa only [file22] using Generated.render_cubeRoot)
def tree22 : ScopedC.SourceBundle.Tree Piece := .leaf file22 piece22
theorem tree_bound22 : tree22.Bound Piece.Bound := .leaf bound22
def file23 : File := ⟨"function_gaussianCell.inc",include_str "../../height-bundle-source-v3/function_gaussianCell.inc"⟩
def piece23 : Piece := .function Generated.f_gaussianCell
theorem bound23 : Piece.Bound piece23 file23 := .function (by simpa only [file23] using Generated.render_gaussianCell)
def tree23 : ScopedC.SourceBundle.Tree Piece := .leaf file23 piece23
theorem tree_bound23 : tree23.Bound Piece.Bound := .leaf bound23
def file24 : File := ⟨"function_archived_basis_main.inc",include_str "../../height-bundle-source-v3/function_archived_basis_main.inc"⟩
def piece24 : Piece := .function Generated.f_archived_basis_main
theorem bound24 : Piece.Bound piece24 file24 := .function (by simpa only [file24] using Generated.render_archived_basis_main)
def tree24 : ScopedC.SourceBundle.Tree Piece := .leaf file24 piece24
theorem tree_bound24 : tree24.Bound Piece.Bound := .leaf bound24
def file25 : File := ⟨"function_expPositiveRaw.inc",include_str "../../height-bundle-source-v3/function_expPositiveRaw.inc"⟩
def piece25 : Piece := .function Generated.f_expPositiveRaw
theorem bound25 : Piece.Bound piece25 file25 := .function (by simpa only [file25] using Generated.render_expPositiveRaw)
def tree25 : ScopedC.SourceBundle.Tree Piece := .leaf file25 piece25
theorem tree_bound25 : tree25.Bound Piece.Bound := .leaf bound25
def file26 : File := ⟨"function_expPositive.inc",include_str "../../height-bundle-source-v3/function_expPositive.inc"⟩
def piece26 : Piece := .function Generated.f_expPositive
theorem bound26 : Piece.Bound piece26 file26 := .function (by simpa only [file26] using Generated.render_expPositive)
def tree26 : ScopedC.SourceBundle.Tree Piece := .leaf file26 piece26
theorem tree_bound26 : tree26.Bound Piece.Bound := .leaf bound26
def file27 : File := ⟨"function_logTight.inc",include_str "../../height-bundle-source-v3/function_logTight.inc"⟩
def piece27 : Piece := .function Generated.f_logTight
theorem bound27 : Piece.Bound piece27 file27 := .function (by simpa only [file27] using Generated.render_logTight)
def tree27 : ScopedC.SourceBundle.Tree Piece := .leaf file27 piece27
theorem tree_bound27 : tree27.Bound Piece.Bound := .leaf bound27
def file28 : File := ⟨"function_squareI.inc",include_str "../../height-bundle-source-v3/function_squareI.inc"⟩
def piece28 : Piece := .function Generated.f_squareI
theorem bound28 : Piece.Bound piece28 file28 := .function (by simpa only [file28] using Generated.render_squareI)
def tree28 : ScopedC.SourceBundle.Tree Piece := .leaf file28 piece28
theorem tree_bound28 : tree28.Bound Piece.Bound := .leaf bound28
def file29 : File := ⟨"function_inverseI.inc",include_str "../../height-bundle-source-v3/function_inverseI.inc"⟩
def piece29 : Piece := .function Generated.f_inverseI
theorem bound29 : Piece.Bound piece29 file29 := .function (by simpa only [file29] using Generated.render_inverseI)
def tree29 : ScopedC.SourceBundle.Tree Piece := .leaf file29 piece29
theorem tree_bound29 : tree29.Bound Piece.Bound := .leaf bound29
def file30 : File := ⟨"function_sqrtInterval.inc",include_str "../../height-bundle-source-v3/function_sqrtInterval.inc"⟩
def piece30 : Piece := .function Generated.f_sqrtInterval
theorem bound30 : Piece.Bound piece30 file30 := .function (by simpa only [file30] using Generated.render_sqrtInterval)
def tree30 : ScopedC.SourceBundle.Tree Piece := .leaf file30 piece30
theorem tree_bound30 : tree30.Bound Piece.Bound := .leaf bound30
def file31 : File := ⟨"function_emitU.inc",include_str "../../height-bundle-source-v3/function_emitU.inc"⟩
def piece31 : Piece := .function Generated.f_emitU
theorem bound31 : Piece.Bound piece31 file31 := .function (by simpa only [file31] using Generated.render_emitU)
def tree31 : ScopedC.SourceBundle.Tree Piece := .leaf file31 piece31
theorem tree_bound31 : tree31.Bound Piece.Bound := .leaf bound31
def file32 : File := ⟨"function_emitI.inc",include_str "../../height-bundle-source-v3/function_emitI.inc"⟩
def piece32 : Piece := .function Generated.f_emitI
theorem bound32 : Piece.Bound piece32 file32 := .function (by simpa only [file32] using Generated.render_emitI)
def tree32 : ScopedC.SourceBundle.Tree Piece := .leaf file32 piece32
theorem tree_bound32 : tree32.Bound Piece.Bound := .leaf bound32
def file33 : File := ⟨"global_piBox.inc",include_str "../../height-bundle-source-v3/global_piBox.inc"⟩
def piece33 : Piece := .global Generated.g_piBox
theorem bound33 : Piece.Bound piece33 file33 := .global (by simpa only [file33] using Generated.render_global_piBox)
def tree33 : ScopedC.SourceBundle.Tree Piece := .leaf file33 piece33
theorem tree_bound33 : tree33.Bound Piece.Bound := .leaf bound33
def file34 : File := ⟨"global_m0Box.inc",include_str "../../height-bundle-source-v3/global_m0Box.inc"⟩
def piece34 : Piece := .global Generated.g_m0Box
theorem bound34 : Piece.Bound piece34 file34 := .global (by simpa only [file34] using Generated.render_global_m0Box)
def tree34 : ScopedC.SourceBundle.Tree Piece := .leaf file34 piece34
theorem tree_bound34 : tree34.Bound Piece.Bound := .leaf bound34
def file35 : File := ⟨"global_gaussianBox.inc",include_str "../../height-bundle-source-v3/global_gaussianBox.inc"⟩
def piece35 : Piece := .global Generated.g_gaussianBox
theorem bound35 : Piece.Bound piece35 file35 := .global (by simpa only [file35] using Generated.render_global_gaussianBox)
def tree35 : ScopedC.SourceBundle.Tree Piece := .leaf file35 piece35
theorem tree_bound35 : tree35.Bound Piece.Bound := .leaf bound35
def file36 : File := ⟨"global_peakBox.inc",include_str "../../height-bundle-source-v3/global_peakBox.inc"⟩
def piece36 : Piece := .global Generated.g_peakBox
theorem bound36 : Piece.Bound piece36 file36 := .global (by simpa only [file36] using Generated.render_global_peakBox)
def tree36 : ScopedC.SourceBundle.Tree Piece := .leaf file36 piece36
theorem tree_bound36 : tree36.Bound Piece.Bound := .leaf bound36
def file37 : File := ⟨"global_sqrtPi.inc",include_str "../../height-bundle-source-v3/global_sqrtPi.inc"⟩
def piece37 : Piece := .global Generated.g_sqrtPi
theorem bound37 : Piece.Bound piece37 file37 := .global (by simpa only [file37] using Generated.render_global_sqrtPi)
def tree37 : ScopedC.SourceBundle.Tree Piece := .leaf file37 piece37
theorem tree_bound37 : tree37.Bound Piece.Bound := .leaf bound37
def file38 : File := ⟨"global_sqrt2Alpha.inc",include_str "../../height-bundle-source-v3/global_sqrt2Alpha.inc"⟩
def piece38 : Piece := .global Generated.g_sqrt2Alpha
theorem bound38 : Piece.Bound piece38 file38 := .global (by simpa only [file38] using Generated.render_global_sqrt2Alpha)
def tree38 : ScopedC.SourceBundle.Tree Piece := .leaf file38 piece38
theorem tree_bound38 : tree38.Bound Piece.Bound := .leaf bound38
def file39 : File := ⟨"global_alphaBox.inc",include_str "../../height-bundle-source-v3/global_alphaBox.inc"⟩
def piece39 : Piece := .global Generated.g_alphaBox
theorem bound39 : Piece.Bound piece39 file39 := .global (by simpa only [file39] using Generated.render_global_alphaBox)
def tree39 : ScopedC.SourceBundle.Tree Piece := .leaf file39 piece39
theorem tree_bound39 : tree39.Bound Piece.Bound := .leaf bound39
def file40 : File := ⟨"global_dBox.inc",include_str "../../height-bundle-source-v3/global_dBox.inc"⟩
def piece40 : Piece := .global Generated.g_dBox
theorem bound40 : Piece.Bound piece40 file40 := .global (by simpa only [file40] using Generated.render_global_dBox)
def tree40 : ScopedC.SourceBundle.Tree Piece := .leaf file40 piece40
theorem tree_bound40 : tree40.Bound Piece.Bound := .leaf bound40
def file41 : File := ⟨"global_deltaBox.inc",include_str "../../height-bundle-source-v3/global_deltaBox.inc"⟩
def piece41 : Piece := .global Generated.g_deltaBox
theorem bound41 : Piece.Bound piece41 file41 := .global (by simpa only [file41] using Generated.render_global_deltaBox)
def tree41 : ScopedC.SourceBundle.Tree Piece := .leaf file41 piece41
theorem tree_bound41 : tree41.Bound Piece.Bound := .leaf bound41
def file42 : File := ⟨"global_smoothingBox.inc",include_str "../../height-bundle-source-v3/global_smoothingBox.inc"⟩
def piece42 : Piece := .global Generated.g_smoothingBox
theorem bound42 : Piece.Bound piece42 file42 := .global (by simpa only [file42] using Generated.render_global_smoothingBox)
def tree42 : ScopedC.SourceBundle.Tree Piece := .leaf file42 piece42
theorem tree_bound42 : tree42.Bound Piece.Bound := .leaf bound42
def file43 : File := ⟨"function_initializeConstants.inc",include_str "../../height-bundle-source-v3/function_initializeConstants.inc"⟩
def piece43 : Piece := .function Generated.f_initializeConstants
theorem bound43 : Piece.Bound piece43 file43 := .function (by simpa only [file43] using Generated.render_initializeConstants)
def tree43 : ScopedC.SourceBundle.Tree Piece := .leaf file43 piece43
theorem tree_bound43 : tree43.Bound Piece.Bound := .leaf bound43
def file44 : File := ⟨"function_rightRawCap.inc",include_str "../../height-bundle-source-v3/function_rightRawCap.inc"⟩
def piece44 : Piece := .function Generated.f_rightRawCap
theorem bound44 : Piece.Bound piece44 file44 := .function (by simpa only [file44] using Generated.render_rightRawCap)
def tree44 : ScopedC.SourceBundle.Tree Piece := .leaf file44 piece44
theorem tree_bound44 : tree44.Bound Piece.Bound := .leaf bound44
def file45 : File := ⟨"function_leftRawCap.inc",include_str "../../height-bundle-source-v3/function_leftRawCap.inc"⟩
def piece45 : Piece := .function Generated.f_leftRawCap
theorem bound45 : Piece.Bound piece45 file45 := .function (by simpa only [file45] using Generated.render_leftRawCap)
def tree45 : ScopedC.SourceBundle.Tree Piece := .leaf file45 piece45
theorem tree_bound45 : tree45.Bound Piece.Bound := .leaf bound45
def file46 : File := ⟨"function_heightPair.inc",include_str "../../height-bundle-source-v3/function_heightPair.inc"⟩
def piece46 : Piece := .function Generated.f_heightPair
theorem bound46 : Piece.Bound piece46 file46 := .function (by simpa only [file46] using Generated.render_heightPair)
def tree46 : ScopedC.SourceBundle.Tree Piece := .leaf file46 piece46
theorem tree_bound46 : tree46.Bound Piece.Bound := .leaf bound46
def file47 : File := ⟨"function_expNegAny.inc",include_str "../../height-bundle-source-v3/function_expNegAny.inc"⟩
def piece47 : Piece := .function Generated.f_expNegAny
theorem bound47 : Piece.Bound piece47 file47 := .function (by simpa only [file47] using Generated.render_expNegAny)
def tree47 : ScopedC.SourceBundle.Tree Piece := .leaf file47 piece47
theorem tree_bound47 : tree47.Bound Piece.Bound := .leaf bound47
def file48 : File := ⟨"function_paired.inc",include_str "../../height-bundle-source-v3/function_paired.inc"⟩
def piece48 : Piece := .function Generated.f_paired
theorem bound48 : Piece.Bound piece48 file48 := .function (by simpa only [file48] using Generated.render_paired)
def tree48 : ScopedC.SourceBundle.Tree Piece := .leaf file48 piece48
theorem tree_bound48 : tree48.Bound Piece.Bound := .leaf bound48
def file49 : File := ⟨"global_constantNodes.inc",include_str "../../height-bundle-source-v3/global_constantNodes.inc"⟩
def piece49 : Piece := .global Generated.g_constantNodes
theorem bound49 : Piece.Bound piece49 file49 := .global (by simpa only [file49] using Generated.render_global_constantNodes)
def tree49 : ScopedC.SourceBundle.Tree Piece := .leaf file49 piece49
theorem tree_bound49 : tree49.Bound Piece.Bound := .leaf bound49
def file50 : File := ⟨"function_subExact.inc",include_str "../../height-bundle-source-v3/function_subExact.inc"⟩
def piece50 : Piece := .function Generated.f_subExact
theorem bound50 : Piece.Bound piece50 file50 := .function (by simpa only [file50] using Generated.render_subExact)
def tree50 : ScopedC.SourceBundle.Tree Piece := .leaf file50 piece50
theorem tree_bound50 : tree50.Bound Piece.Bound := .leaf bound50
def file51 : File := ⟨"function_sqrtMatch.inc",include_str "../../height-bundle-source-v3/function_sqrtMatch.inc"⟩
def piece51 : Piece := .function Generated.f_sqrtMatch
theorem bound51 : Piece.Bound piece51 file51 := .function (by simpa only [file51] using Generated.render_sqrtMatch)
def tree51 : ScopedC.SourceBundle.Tree Piece := .leaf file51 piece51
theorem tree_bound51 : tree51.Bound Piece.Bound := .leaf bound51
def file52 : File := ⟨"function_initializePointConstants.inc",include_str "../../height-bundle-source-v3/function_initializePointConstants.inc"⟩
def piece52 : Piece := .function Generated.f_initializePointConstants
theorem bound52 : Piece.Bound piece52 file52 := .functionTree (by simpa only [file52,FunctionTrees.initWrapper] using FunctionTrees.initBound)
def tree52 : ScopedC.SourceBundle.Tree Piece := .leaf file52 piece52
theorem tree_bound52 : tree52.Bound Piece.Bound := .leaf bound52
def file53 : File := ⟨"function_pointHeight.inc",include_str "../../height-bundle-source-v3/function_pointHeight.inc"⟩
def piece53 : Piece := .function Generated.f_pointHeight
theorem bound53 : Piece.Bound piece53 file53 := .functionTree (by simpa only [file53,FunctionTrees.pointWrapper] using FunctionTrees.pointBound)
def tree53 : ScopedC.SourceBundle.Tree Piece := .leaf file53 piece53
theorem tree_bound53 : tree53.Bound Piece.Bound := .leaf bound53
def file54 : File := ⟨"function_pointEdge.inc",include_str "../../height-bundle-source-v3/function_pointEdge.inc"⟩
def piece54 : Piece := .function Generated.f_pointEdge
theorem bound54 : Piece.Bound piece54 file54 := .functionTree (by simpa only [file54,FunctionTrees.edgeWrapper] using FunctionTrees.edgeBound)
def tree54 : ScopedC.SourceBundle.Tree Piece := .leaf file54 piece54
theorem tree_bound54 : tree54.Bound Piece.Bound := .leaf bound54
def file55 : File := ⟨"function_main.inc",include_str "../../height-bundle-source-v3/function_main.inc"⟩
def piece55 : Piece := .function Generated.f_main
theorem bound55 : Piece.Bound piece55 file55 := .functionTree (by simpa only [file55,FunctionTrees.entryWrapper] using FunctionTrees.entryBound)
def tree55 : ScopedC.SourceBundle.Tree Piece := .leaf file55 piece55
theorem tree_bound55 : tree55.Bound Piece.Bound := .leaf bound55
def join_file0 : File := ⟨"join_000.inc",include_str "../../height-bundle-source-v3/join_000.inc"⟩
def join_tree0 : ScopedC.SourceBundle.Tree Piece := .pair join_file0 tree1 tree2
theorem join_bound0 : join_tree0.Bound Piece.Bound := .pair tree_bound1 tree_bound2 (by decide +kernel)
def join_file1 : File := ⟨"join_001.inc",include_str "../../height-bundle-source-v3/join_001.inc"⟩
def join_tree1 : ScopedC.SourceBundle.Tree Piece := .pair join_file1 tree0 join_tree0
theorem join_bound1 : join_tree1.Bound Piece.Bound := .pair tree_bound0 join_bound0 (by decide +kernel)
def join_file2 : File := ⟨"join_002.inc",include_str "../../height-bundle-source-v3/join_002.inc"⟩
def join_tree2 : ScopedC.SourceBundle.Tree Piece := .pair join_file2 tree3 tree4
theorem join_bound2 : join_tree2.Bound Piece.Bound := .pair tree_bound3 tree_bound4 (by decide +kernel)
def join_file3 : File := ⟨"join_003.inc",include_str "../../height-bundle-source-v3/join_003.inc"⟩
def join_tree3 : ScopedC.SourceBundle.Tree Piece := .pair join_file3 tree5 tree6
theorem join_bound3 : join_tree3.Bound Piece.Bound := .pair tree_bound5 tree_bound6 (by decide +kernel)
def join_file4 : File := ⟨"join_004.inc",include_str "../../height-bundle-source-v3/join_004.inc"⟩
def join_tree4 : ScopedC.SourceBundle.Tree Piece := .pair join_file4 join_tree2 join_tree3
theorem join_bound4 : join_tree4.Bound Piece.Bound := .pair join_bound2 join_bound3 (by decide +kernel)
def join_file5 : File := ⟨"join_005.inc",include_str "../../height-bundle-source-v3/join_005.inc"⟩
def join_tree5 : ScopedC.SourceBundle.Tree Piece := .pair join_file5 join_tree1 join_tree4
theorem join_bound5 : join_tree5.Bound Piece.Bound := .pair join_bound1 join_bound4 (by decide +kernel)
def join_file6 : File := ⟨"join_006.inc",include_str "../../height-bundle-source-v3/join_006.inc"⟩
def join_tree6 : ScopedC.SourceBundle.Tree Piece := .pair join_file6 tree8 tree9
theorem join_bound6 : join_tree6.Bound Piece.Bound := .pair tree_bound8 tree_bound9 (by decide +kernel)
def join_file7 : File := ⟨"join_007.inc",include_str "../../height-bundle-source-v3/join_007.inc"⟩
def join_tree7 : ScopedC.SourceBundle.Tree Piece := .pair join_file7 tree7 join_tree6
theorem join_bound7 : join_tree7.Bound Piece.Bound := .pair tree_bound7 join_bound6 (by decide +kernel)
def join_file8 : File := ⟨"join_008.inc",include_str "../../height-bundle-source-v3/join_008.inc"⟩
def join_tree8 : ScopedC.SourceBundle.Tree Piece := .pair join_file8 tree10 tree11
theorem join_bound8 : join_tree8.Bound Piece.Bound := .pair tree_bound10 tree_bound11 (by decide +kernel)
def join_file9 : File := ⟨"join_009.inc",include_str "../../height-bundle-source-v3/join_009.inc"⟩
def join_tree9 : ScopedC.SourceBundle.Tree Piece := .pair join_file9 tree12 tree13
theorem join_bound9 : join_tree9.Bound Piece.Bound := .pair tree_bound12 tree_bound13 (by decide +kernel)
def join_file10 : File := ⟨"join_010.inc",include_str "../../height-bundle-source-v3/join_010.inc"⟩
def join_tree10 : ScopedC.SourceBundle.Tree Piece := .pair join_file10 join_tree8 join_tree9
theorem join_bound10 : join_tree10.Bound Piece.Bound := .pair join_bound8 join_bound9 (by decide +kernel)
def join_file11 : File := ⟨"join_011.inc",include_str "../../height-bundle-source-v3/join_011.inc"⟩
def join_tree11 : ScopedC.SourceBundle.Tree Piece := .pair join_file11 join_tree7 join_tree10
theorem join_bound11 : join_tree11.Bound Piece.Bound := .pair join_bound7 join_bound10 (by decide +kernel)
def join_file12 : File := ⟨"join_012.inc",include_str "../../height-bundle-source-v3/join_012.inc"⟩
def join_tree12 : ScopedC.SourceBundle.Tree Piece := .pair join_file12 join_tree5 join_tree11
theorem join_bound12 : join_tree12.Bound Piece.Bound := .pair join_bound5 join_bound11 (by decide +kernel)
def join_file13 : File := ⟨"join_013.inc",include_str "../../height-bundle-source-v3/join_013.inc"⟩
def join_tree13 : ScopedC.SourceBundle.Tree Piece := .pair join_file13 tree15 tree16
theorem join_bound13 : join_tree13.Bound Piece.Bound := .pair tree_bound15 tree_bound16 (by decide +kernel)
def join_file14 : File := ⟨"join_014.inc",include_str "../../height-bundle-source-v3/join_014.inc"⟩
def join_tree14 : ScopedC.SourceBundle.Tree Piece := .pair join_file14 tree14 join_tree13
theorem join_bound14 : join_tree14.Bound Piece.Bound := .pair tree_bound14 join_bound13 (by decide +kernel)
def join_file15 : File := ⟨"join_015.inc",include_str "../../height-bundle-source-v3/join_015.inc"⟩
def join_tree15 : ScopedC.SourceBundle.Tree Piece := .pair join_file15 tree17 tree18
theorem join_bound15 : join_tree15.Bound Piece.Bound := .pair tree_bound17 tree_bound18 (by decide +kernel)
def join_file16 : File := ⟨"join_016.inc",include_str "../../height-bundle-source-v3/join_016.inc"⟩
def join_tree16 : ScopedC.SourceBundle.Tree Piece := .pair join_file16 tree19 tree20
theorem join_bound16 : join_tree16.Bound Piece.Bound := .pair tree_bound19 tree_bound20 (by decide +kernel)
def join_file17 : File := ⟨"join_017.inc",include_str "../../height-bundle-source-v3/join_017.inc"⟩
def join_tree17 : ScopedC.SourceBundle.Tree Piece := .pair join_file17 join_tree15 join_tree16
theorem join_bound17 : join_tree17.Bound Piece.Bound := .pair join_bound15 join_bound16 (by decide +kernel)
def join_file18 : File := ⟨"join_018.inc",include_str "../../height-bundle-source-v3/join_018.inc"⟩
def join_tree18 : ScopedC.SourceBundle.Tree Piece := .pair join_file18 join_tree14 join_tree17
theorem join_bound18 : join_tree18.Bound Piece.Bound := .pair join_bound14 join_bound17 (by decide +kernel)
def join_file19 : File := ⟨"join_019.inc",include_str "../../height-bundle-source-v3/join_019.inc"⟩
def join_tree19 : ScopedC.SourceBundle.Tree Piece := .pair join_file19 tree22 tree23
theorem join_bound19 : join_tree19.Bound Piece.Bound := .pair tree_bound22 tree_bound23 (by decide +kernel)
def join_file20 : File := ⟨"join_020.inc",include_str "../../height-bundle-source-v3/join_020.inc"⟩
def join_tree20 : ScopedC.SourceBundle.Tree Piece := .pair join_file20 tree21 join_tree19
theorem join_bound20 : join_tree20.Bound Piece.Bound := .pair tree_bound21 join_bound19 (by decide +kernel)
def join_file21 : File := ⟨"join_021.inc",include_str "../../height-bundle-source-v3/join_021.inc"⟩
def join_tree21 : ScopedC.SourceBundle.Tree Piece := .pair join_file21 tree24 tree25
theorem join_bound21 : join_tree21.Bound Piece.Bound := .pair tree_bound24 tree_bound25 (by decide +kernel)
def join_file22 : File := ⟨"join_022.inc",include_str "../../height-bundle-source-v3/join_022.inc"⟩
def join_tree22 : ScopedC.SourceBundle.Tree Piece := .pair join_file22 tree26 tree27
theorem join_bound22 : join_tree22.Bound Piece.Bound := .pair tree_bound26 tree_bound27 (by decide +kernel)
def join_file23 : File := ⟨"join_023.inc",include_str "../../height-bundle-source-v3/join_023.inc"⟩
def join_tree23 : ScopedC.SourceBundle.Tree Piece := .pair join_file23 join_tree21 join_tree22
theorem join_bound23 : join_tree23.Bound Piece.Bound := .pair join_bound21 join_bound22 (by decide +kernel)
def join_file24 : File := ⟨"join_024.inc",include_str "../../height-bundle-source-v3/join_024.inc"⟩
def join_tree24 : ScopedC.SourceBundle.Tree Piece := .pair join_file24 join_tree20 join_tree23
theorem join_bound24 : join_tree24.Bound Piece.Bound := .pair join_bound20 join_bound23 (by decide +kernel)
def join_file25 : File := ⟨"join_025.inc",include_str "../../height-bundle-source-v3/join_025.inc"⟩
def join_tree25 : ScopedC.SourceBundle.Tree Piece := .pair join_file25 join_tree18 join_tree24
theorem join_bound25 : join_tree25.Bound Piece.Bound := .pair join_bound18 join_bound24 (by decide +kernel)
def join_file26 : File := ⟨"join_026.inc",include_str "../../height-bundle-source-v3/join_026.inc"⟩
def join_tree26 : ScopedC.SourceBundle.Tree Piece := .pair join_file26 join_tree12 join_tree25
theorem join_bound26 : join_tree26.Bound Piece.Bound := .pair join_bound12 join_bound25 (by decide +kernel)
def join_file27 : File := ⟨"join_027.inc",include_str "../../height-bundle-source-v3/join_027.inc"⟩
def join_tree27 : ScopedC.SourceBundle.Tree Piece := .pair join_file27 tree29 tree30
theorem join_bound27 : join_tree27.Bound Piece.Bound := .pair tree_bound29 tree_bound30 (by decide +kernel)
def join_file28 : File := ⟨"join_028.inc",include_str "../../height-bundle-source-v3/join_028.inc"⟩
def join_tree28 : ScopedC.SourceBundle.Tree Piece := .pair join_file28 tree28 join_tree27
theorem join_bound28 : join_tree28.Bound Piece.Bound := .pair tree_bound28 join_bound27 (by decide +kernel)
def join_file29 : File := ⟨"join_029.inc",include_str "../../height-bundle-source-v3/join_029.inc"⟩
def join_tree29 : ScopedC.SourceBundle.Tree Piece := .pair join_file29 tree31 tree32
theorem join_bound29 : join_tree29.Bound Piece.Bound := .pair tree_bound31 tree_bound32 (by decide +kernel)
def join_file30 : File := ⟨"join_030.inc",include_str "../../height-bundle-source-v3/join_030.inc"⟩
def join_tree30 : ScopedC.SourceBundle.Tree Piece := .pair join_file30 tree33 tree34
theorem join_bound30 : join_tree30.Bound Piece.Bound := .pair tree_bound33 tree_bound34 (by decide +kernel)
def join_file31 : File := ⟨"join_031.inc",include_str "../../height-bundle-source-v3/join_031.inc"⟩
def join_tree31 : ScopedC.SourceBundle.Tree Piece := .pair join_file31 join_tree29 join_tree30
theorem join_bound31 : join_tree31.Bound Piece.Bound := .pair join_bound29 join_bound30 (by decide +kernel)
def join_file32 : File := ⟨"join_032.inc",include_str "../../height-bundle-source-v3/join_032.inc"⟩
def join_tree32 : ScopedC.SourceBundle.Tree Piece := .pair join_file32 join_tree28 join_tree31
theorem join_bound32 : join_tree32.Bound Piece.Bound := .pair join_bound28 join_bound31 (by decide +kernel)
def join_file33 : File := ⟨"join_033.inc",include_str "../../height-bundle-source-v3/join_033.inc"⟩
def join_tree33 : ScopedC.SourceBundle.Tree Piece := .pair join_file33 tree36 tree37
theorem join_bound33 : join_tree33.Bound Piece.Bound := .pair tree_bound36 tree_bound37 (by decide +kernel)
def join_file34 : File := ⟨"join_034.inc",include_str "../../height-bundle-source-v3/join_034.inc"⟩
def join_tree34 : ScopedC.SourceBundle.Tree Piece := .pair join_file34 tree35 join_tree33
theorem join_bound34 : join_tree34.Bound Piece.Bound := .pair tree_bound35 join_bound33 (by decide +kernel)
def join_file35 : File := ⟨"join_035.inc",include_str "../../height-bundle-source-v3/join_035.inc"⟩
def join_tree35 : ScopedC.SourceBundle.Tree Piece := .pair join_file35 tree38 tree39
theorem join_bound35 : join_tree35.Bound Piece.Bound := .pair tree_bound38 tree_bound39 (by decide +kernel)
def join_file36 : File := ⟨"join_036.inc",include_str "../../height-bundle-source-v3/join_036.inc"⟩
def join_tree36 : ScopedC.SourceBundle.Tree Piece := .pair join_file36 tree40 tree41
theorem join_bound36 : join_tree36.Bound Piece.Bound := .pair tree_bound40 tree_bound41 (by decide +kernel)
def join_file37 : File := ⟨"join_037.inc",include_str "../../height-bundle-source-v3/join_037.inc"⟩
def join_tree37 : ScopedC.SourceBundle.Tree Piece := .pair join_file37 join_tree35 join_tree36
theorem join_bound37 : join_tree37.Bound Piece.Bound := .pair join_bound35 join_bound36 (by decide +kernel)
def join_file38 : File := ⟨"join_038.inc",include_str "../../height-bundle-source-v3/join_038.inc"⟩
def join_tree38 : ScopedC.SourceBundle.Tree Piece := .pair join_file38 join_tree34 join_tree37
theorem join_bound38 : join_tree38.Bound Piece.Bound := .pair join_bound34 join_bound37 (by decide +kernel)
def join_file39 : File := ⟨"join_039.inc",include_str "../../height-bundle-source-v3/join_039.inc"⟩
def join_tree39 : ScopedC.SourceBundle.Tree Piece := .pair join_file39 join_tree32 join_tree38
theorem join_bound39 : join_tree39.Bound Piece.Bound := .pair join_bound32 join_bound38 (by decide +kernel)
def join_file40 : File := ⟨"join_040.inc",include_str "../../height-bundle-source-v3/join_040.inc"⟩
def join_tree40 : ScopedC.SourceBundle.Tree Piece := .pair join_file40 tree43 tree44
theorem join_bound40 : join_tree40.Bound Piece.Bound := .pair tree_bound43 tree_bound44 (by decide +kernel)
def join_file41 : File := ⟨"join_041.inc",include_str "../../height-bundle-source-v3/join_041.inc"⟩
def join_tree41 : ScopedC.SourceBundle.Tree Piece := .pair join_file41 tree42 join_tree40
theorem join_bound41 : join_tree41.Bound Piece.Bound := .pair tree_bound42 join_bound40 (by decide +kernel)
def join_file42 : File := ⟨"join_042.inc",include_str "../../height-bundle-source-v3/join_042.inc"⟩
def join_tree42 : ScopedC.SourceBundle.Tree Piece := .pair join_file42 tree45 tree46
theorem join_bound42 : join_tree42.Bound Piece.Bound := .pair tree_bound45 tree_bound46 (by decide +kernel)
def join_file43 : File := ⟨"join_043.inc",include_str "../../height-bundle-source-v3/join_043.inc"⟩
def join_tree43 : ScopedC.SourceBundle.Tree Piece := .pair join_file43 tree47 tree48
theorem join_bound43 : join_tree43.Bound Piece.Bound := .pair tree_bound47 tree_bound48 (by decide +kernel)
def join_file44 : File := ⟨"join_044.inc",include_str "../../height-bundle-source-v3/join_044.inc"⟩
def join_tree44 : ScopedC.SourceBundle.Tree Piece := .pair join_file44 join_tree42 join_tree43
theorem join_bound44 : join_tree44.Bound Piece.Bound := .pair join_bound42 join_bound43 (by decide +kernel)
def join_file45 : File := ⟨"join_045.inc",include_str "../../height-bundle-source-v3/join_045.inc"⟩
def join_tree45 : ScopedC.SourceBundle.Tree Piece := .pair join_file45 join_tree41 join_tree44
theorem join_bound45 : join_tree45.Bound Piece.Bound := .pair join_bound41 join_bound44 (by decide +kernel)
def join_file46 : File := ⟨"join_046.inc",include_str "../../height-bundle-source-v3/join_046.inc"⟩
def join_tree46 : ScopedC.SourceBundle.Tree Piece := .pair join_file46 tree50 tree51
theorem join_bound46 : join_tree46.Bound Piece.Bound := .pair tree_bound50 tree_bound51 (by decide +kernel)
def join_file47 : File := ⟨"join_047.inc",include_str "../../height-bundle-source-v3/join_047.inc"⟩
def join_tree47 : ScopedC.SourceBundle.Tree Piece := .pair join_file47 tree49 join_tree46
theorem join_bound47 : join_tree47.Bound Piece.Bound := .pair tree_bound49 join_bound46 (by decide +kernel)
def join_file48 : File := ⟨"join_048.inc",include_str "../../height-bundle-source-v3/join_048.inc"⟩
def join_tree48 : ScopedC.SourceBundle.Tree Piece := .pair join_file48 tree52 tree53
theorem join_bound48 : join_tree48.Bound Piece.Bound := .pair tree_bound52 tree_bound53 (by decide +kernel)
def join_file49 : File := ⟨"join_049.inc",include_str "../../height-bundle-source-v3/join_049.inc"⟩
def join_tree49 : ScopedC.SourceBundle.Tree Piece := .pair join_file49 tree54 tree55
theorem join_bound49 : join_tree49.Bound Piece.Bound := .pair tree_bound54 tree_bound55 (by decide +kernel)
def join_file50 : File := ⟨"join_050.inc",include_str "../../height-bundle-source-v3/join_050.inc"⟩
def join_tree50 : ScopedC.SourceBundle.Tree Piece := .pair join_file50 join_tree48 join_tree49
theorem join_bound50 : join_tree50.Bound Piece.Bound := .pair join_bound48 join_bound49 (by decide +kernel)
def join_file51 : File := ⟨"join_051.inc",include_str "../../height-bundle-source-v3/join_051.inc"⟩
def join_tree51 : ScopedC.SourceBundle.Tree Piece := .pair join_file51 join_tree47 join_tree50
theorem join_bound51 : join_tree51.Bound Piece.Bound := .pair join_bound47 join_bound50 (by decide +kernel)
def join_file52 : File := ⟨"join_052.inc",include_str "../../height-bundle-source-v3/join_052.inc"⟩
def join_tree52 : ScopedC.SourceBundle.Tree Piece := .pair join_file52 join_tree45 join_tree51
theorem join_bound52 : join_tree52.Bound Piece.Bound := .pair join_bound45 join_bound51 (by decide +kernel)
def join_file53 : File := ⟨"join_053.inc",include_str "../../height-bundle-source-v3/join_053.inc"⟩
def join_tree53 : ScopedC.SourceBundle.Tree Piece := .pair join_file53 join_tree39 join_tree52
theorem join_bound53 : join_tree53.Bound Piece.Bound := .pair join_bound39 join_bound52 (by decide +kernel)
def join_file54 : File := ⟨"join_054.inc",include_str "../../height-bundle-source-v3/join_054.inc"⟩
def join_tree54 : ScopedC.SourceBundle.Tree Piece := .pair join_file54 join_tree26 join_tree53
theorem join_bound54 : join_tree54.Bound Piece.Bound := .pair join_bound26 join_bound53 (by decide +kernel)
def tree : ScopedC.SourceBundle.Tree Piece := join_tree54
theorem bound : tree.Bound Piece.Bound := join_bound54
def code : List Function := tree.values.flatMap (fun p=>match p with | .function f=>[f] | _=>[])
def globals : List Decl := tree.values.flatMap (fun p=>match p with | .global d=>[d] | _=>[])
theorem code_exact : code=Generated.functions := by rfl
theorem globals_exact : globals=Generated.globals := by rfl
def entryFile : File := ⟨"height_bundle.cpp",include_str "../../height-bundle-source-v3/height_bundle.cpp"⟩
def actualFiles : List File := tree.files++(FunctionTrees.innerFiles++[entryFile])

theorem initWrapper_mem : FunctionTrees.initWrapper∈tree.files := by
  change file52∈tree.files
  exact (List.mem_cons_of_mem join_file54 (List.mem_append_right join_tree26.files (List.mem_cons_of_mem join_file53 (List.mem_append_right join_tree39.files (List.mem_cons_of_mem join_file52 (List.mem_append_right join_tree45.files (List.mem_cons_of_mem join_file51 (List.mem_append_right join_tree47.files (List.mem_cons_of_mem join_file50 (List.mem_append_left join_tree49.files (List.mem_cons_of_mem join_file48 (List.mem_append_left tree53.files (by change file52∈[file52];exact List.mem_cons_self)))))))))))))
theorem initAllFiles {source:File} (h:source∈FunctionTrees.initWrapper::FunctionTrees.initBody.files):source∈actualFiles := by
  rcases List.mem_cons.mp h with h|h
  · subst source
    exact List.mem_append_left _ initWrapper_mem
  · apply List.mem_append_right tree.files
    apply List.mem_append_left [entryFile]
    change source∈FunctionTrees.initBody.files++FunctionTrees.pointBody.files++FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files
    exact List.mem_append_left (FunctionTrees.pointBody.files++FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files) h
theorem init_expands {load:String→Option String} (same:∀file∈actualFiles,load file.name=some file.text):
    FunctionTree.Expands load FunctionTrees.initWrapper.name Generated.f_initializePointConstants :=
  FunctionTrees.initBound.expands_from_all_files load (fun file member=>same file (initAllFiles member))
#print axioms init_expands
theorem pointWrapper_mem : FunctionTrees.pointWrapper∈tree.files := by
  change file53∈tree.files
  exact (List.mem_cons_of_mem join_file54 (List.mem_append_right join_tree26.files (List.mem_cons_of_mem join_file53 (List.mem_append_right join_tree39.files (List.mem_cons_of_mem join_file52 (List.mem_append_right join_tree45.files (List.mem_cons_of_mem join_file51 (List.mem_append_right join_tree47.files (List.mem_cons_of_mem join_file50 (List.mem_append_left join_tree49.files (List.mem_cons_of_mem join_file48 (List.mem_append_right tree52.files (by change file53∈[file53];exact List.mem_cons_self)))))))))))))
theorem pointAllFiles {source:File} (h:source∈FunctionTrees.pointWrapper::FunctionTrees.pointBody.files):source∈actualFiles := by
  rcases List.mem_cons.mp h with h|h
  · subst source
    exact List.mem_append_left _ pointWrapper_mem
  · apply List.mem_append_right tree.files
    apply List.mem_append_left [entryFile]
    change source∈FunctionTrees.initBody.files++FunctionTrees.pointBody.files++FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files
    exact List.mem_append_right FunctionTrees.initBody.files (List.mem_append_left (FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files) h)
theorem point_expands {load:String→Option String} (same:∀file∈actualFiles,load file.name=some file.text):
    FunctionTree.Expands load FunctionTrees.pointWrapper.name Generated.f_pointHeight :=
  FunctionTrees.pointBound.expands_from_all_files load (fun file member=>same file (pointAllFiles member))
#print axioms point_expands
theorem edgeWrapper_mem : FunctionTrees.edgeWrapper∈tree.files := by
  change file54∈tree.files
  exact (List.mem_cons_of_mem join_file54 (List.mem_append_right join_tree26.files (List.mem_cons_of_mem join_file53 (List.mem_append_right join_tree39.files (List.mem_cons_of_mem join_file52 (List.mem_append_right join_tree45.files (List.mem_cons_of_mem join_file51 (List.mem_append_right join_tree47.files (List.mem_cons_of_mem join_file50 (List.mem_append_right join_tree48.files (List.mem_cons_of_mem join_file49 (List.mem_append_left tree55.files (by change file54∈[file54];exact List.mem_cons_self)))))))))))))
theorem edgeAllFiles {source:File} (h:source∈FunctionTrees.edgeWrapper::FunctionTrees.edgeBody.files):source∈actualFiles := by
  rcases List.mem_cons.mp h with h|h
  · subst source
    exact List.mem_append_left _ edgeWrapper_mem
  · apply List.mem_append_right tree.files
    apply List.mem_append_left [entryFile]
    change source∈FunctionTrees.initBody.files++FunctionTrees.pointBody.files++FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files
    exact List.mem_append_right FunctionTrees.initBody.files (List.mem_append_right FunctionTrees.pointBody.files (List.mem_append_left (FunctionTrees.entryBody.files) h))
theorem edge_expands {load:String→Option String} (same:∀file∈actualFiles,load file.name=some file.text):
    FunctionTree.Expands load FunctionTrees.edgeWrapper.name Generated.f_pointEdge :=
  FunctionTrees.edgeBound.expands_from_all_files load (fun file member=>same file (edgeAllFiles member))
#print axioms edge_expands
theorem entryWrapper_mem : FunctionTrees.entryWrapper∈tree.files := by
  change file55∈tree.files
  exact (List.mem_cons_of_mem join_file54 (List.mem_append_right join_tree26.files (List.mem_cons_of_mem join_file53 (List.mem_append_right join_tree39.files (List.mem_cons_of_mem join_file52 (List.mem_append_right join_tree45.files (List.mem_cons_of_mem join_file51 (List.mem_append_right join_tree47.files (List.mem_cons_of_mem join_file50 (List.mem_append_right join_tree48.files (List.mem_cons_of_mem join_file49 (List.mem_append_right tree54.files (by change file55∈[file55];exact List.mem_cons_self)))))))))))))
theorem entryAllFiles {source:File} (h:source∈FunctionTrees.entryWrapper::FunctionTrees.entryBody.files):source∈actualFiles := by
  rcases List.mem_cons.mp h with h|h
  · subst source
    exact List.mem_append_left _ entryWrapper_mem
  · apply List.mem_append_right tree.files
    apply List.mem_append_left [entryFile]
    change source∈FunctionTrees.initBody.files++FunctionTrees.pointBody.files++FunctionTrees.edgeBody.files++FunctionTrees.entryBody.files
    exact List.mem_append_right FunctionTrees.initBody.files (List.mem_append_right FunctionTrees.pointBody.files (List.mem_append_right FunctionTrees.edgeBody.files (h)))
theorem entry_expands {load:String→Option String} (same:∀file∈actualFiles,load file.name=some file.text):
    FunctionTree.Expands load FunctionTrees.entryWrapper.name Generated.f_main :=
  FunctionTrees.entryBound.expands_from_all_files load (fun file member=>same file (entryAllFiles member))
#print axioms entry_expands
#print axioms bound
#print axioms code_exact
#print axioms globals_exact
end SynergyHeightC.Bundle

import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_global_S : (do pure ("static "++(←renderDecl g_S)++";\n")) = some "static const U S=(((U)1)<<128);\n" := by decide +kernel
theorem render_global_MAXU : (do pure ("static "++(←renderDecl g_MAXU)++";\n")) = some "static const U MAXU=((U)(-1));\n" := by decide +kernel
theorem render_global_ln2 : (do pure ("static "++(←renderDecl g_ln2)++";\n")) = some "static I ln2;\n" := by decide +kernel
theorem render_global_piBox : (do pure ("static "++(←renderDecl g_piBox)++";\n")) = some "static I piBox;\n" := by decide +kernel
theorem render_global_m0Box : (do pure ("static "++(←renderDecl g_m0Box)++";\n")) = some "static I m0Box;\n" := by decide +kernel
theorem render_global_gaussianBox : (do pure ("static "++(←renderDecl g_gaussianBox)++";\n")) = some "static I gaussianBox;\n" := by decide +kernel
theorem render_global_peakBox : (do pure ("static "++(←renderDecl g_peakBox)++";\n")) = some "static I peakBox;\n" := by decide +kernel
theorem render_global_sqrtPi : (do pure ("static "++(←renderDecl g_sqrtPi)++";\n")) = some "static I sqrtPi;\n" := by decide +kernel
theorem render_global_sqrt2Alpha : (do pure ("static "++(←renderDecl g_sqrt2Alpha)++";\n")) = some "static I sqrt2Alpha;\n" := by decide +kernel
theorem render_global_alphaBox : (do pure ("static "++(←renderDecl g_alphaBox)++";\n")) = some "static I alphaBox;\n" := by decide +kernel
theorem render_global_dBox : (do pure ("static "++(←renderDecl g_dBox)++";\n")) = some "static I dBox;\n" := by decide +kernel
theorem render_global_deltaBox : (do pure ("static "++(←renderDecl g_deltaBox)++";\n")) = some "static I deltaBox;\n" := by decide +kernel
theorem render_global_smoothingBox : (do pure ("static "++(←renderDecl g_smoothingBox)++";\n")) = some "static I smoothingBox;\n" := by decide +kernel
theorem render_global_constantNodes : (do pure ("static "++(←renderDecl g_constantNodes)++";\n")) = some "static I constantNodes[58];\n" := by decide +kernel
#print axioms render_global_S
#print axioms render_global_constantNodes
end SynergyHeightC.Generated

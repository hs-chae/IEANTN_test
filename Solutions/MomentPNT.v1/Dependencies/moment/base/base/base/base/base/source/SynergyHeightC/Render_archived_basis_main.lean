import SynergyHeightC.Definitions
namespace SynergyHeightC.Generated
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem render_archived_basis_main : renderFunction f_archived_basis_main = some "int archived_basis_main(){(ln2=atanh2(rat(1,3)));\nI j0=zero();\nI j1=zero();\nI j2=zero();\nconst unsigned int prefix=4096;\nunsigned int i=0;\nwhile((i<prefix)){I left=rat(((5*prefix)+i),(6*prefix));\nI right=rat((((5*prefix)+i)+1),(6*prefix));\n(j0=add(j0,gaussianCell(left,right,rat(1,(6*prefix)))));\n(i=(i+1));}\nconst unsigned int cells=32768;\n(i=0);\nwhile((i<cells)){I left=rat((cells+(15*i)),cells);\nI right=rat((cells+(15*(i+1))),cells);\nI area=gaussianCell(left,right,rat(15,cells));\nI lr=logPos(right);\n(j0=add(j0,area));\n(j1=add(j1,mul(area,lr)));\n(j2=add(j2,mul(area,mul(lr,lr))));\n(i=(i+1));}\nI q=rat(601,2500);\nI M=expNeg(divN(add(unit(),logPos(mul(rat(6,1),q))),6));\nI bq=mul(rat(256,1),q);\nI tail=divI(mul(expNeg(bq),add(bq,unit())),mul(rat(2,1),mul(q,q)));\n(j0=add(add(j0,mul(rat(5,6),M)),tail));\n(j1=add(j1,tail));\n(j2=add(j2,tail));\nI result[3]={j0,j1,j2};\nuint64_t out[18];\n(i=0);\nwhile((i<3)){((out[(6*i)])=((uint64_t)((result[i]).lo)));\n((out[((6*i)+1)])=((uint64_t)(((result[i]).lo)>>64)));\n((out[((6*i)+2)])=((uint64_t)(((result[i]).lo)>>128)));\n((out[((6*i)+3)])=((uint64_t)((result[i]).hi)));\n((out[((6*i)+4)])=((uint64_t)(((result[i]).hi)>>64)));\n((out[((6*i)+5)])=((uint64_t)(((result[i]).hi)>>128)));\n(i=(i+1));}\nreturn ((fwrite(out,8,18,stdout)==18)?0:2);}\n" := by decide +kernel
#print axioms render_archived_basis_main
end SynergyHeightC.Generated

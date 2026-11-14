import ScopedC.Generated
namespace ScopedC.GeneratedAll
open ScopedC.Syntax
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def f_main : Function := {returnType:="int",name:="main",parameters:=[],body:=(.sequence [(.eval (.call (.var "lean_initialize_runtime_module") [])),(.forLoop (.declare [{type:="unsigned int",name:="j",value:=(some (.nat 0)),arrayExtent:=none}]) (some (.binary "<" (.var "j") (.nat 52))) (.binary "=" (.var "j") (.binary "+" (.var "j") (.nat 1))) (.sequence [(.eval (.call (.var "prepare") [(.index (.var "allDepths") (.var "j"))])),(.declare [{type:="unsigned int",name:="mark",value:=(some (.var "poolTop")),arrayExtent:=none}]),(.declare [{type:="I",name:="result",value:=(some (.call (.var "runRow") [(.index (.var "allRows") (.var "j")),(.var "mark"),(.nat 0)])),arrayExtent:=none}]),(.eval (.call (.var "printI") [(.var "result")])),(.eval (.call (.var "clearTo") [(.var "mark")])),(.eval (.call (.var "lean_dec") [(.field "." (.field "." (.var "result") "lo") "mag")])),(.eval (.call (.var "lean_dec") [(.field "." (.field "." (.var "result") "hi") "mag")])),(.eval (.call (.var "clearTo") [(.nat 0)]))])),(.eval (.call (.var "fprintf") [(.var "stderr"),(.stringLiteral "poolHigh=%u\n"),(.var "poolHigh")])),(.returnStmt (.nat 0))])}
theorem render_main : renderFunction f_main = some "int main(){lean_initialize_runtime_module();\nfor(unsigned int j=0;(j<52);(j=(j+1))){prepare((allDepths[j]));\nunsigned int mark=poolTop;\nI result=runRow((allRows[j]),mark,0);\nprintI(result);\nclearTo(mark);\nlean_dec(((result.lo).mag));\nlean_dec(((result.hi).mag));\nclearTo(0);}\nfprintf(stderr,\"poolHigh=%u\\n\",poolHigh);\nreturn 0;}\n" := by decide +kernel
def functions : List Function := ScopedC.Generated.functions.dropLast ++ [f_main]
#print axioms render_main
end ScopedC.GeneratedAll

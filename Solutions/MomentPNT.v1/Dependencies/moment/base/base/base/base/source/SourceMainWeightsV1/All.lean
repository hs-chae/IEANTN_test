import SourceMainWeightsV1.Block00
import SourceMainWeightsV1.Block01
import SourceMainWeightsV1.Block02
import SourceMainWeightsV1.Block03
import SourceMainWeightsV1.Block04
import SourceMainWeightsV1.Block05
import SourceMainWeightsV1.Block06
import SourceMainWeightsV1.Block07
import SourceMainWeightsV1.Block08
import SourceMainWeightsV1.Block09
import SourceMainWeightsV1.Block10
import SourceMainWeightsV1.Block11
import SourceMainWeightsV1.Block12
import SourceMainWeightsV1.Block13
import SourceMainWeightsV1.Block14
import SourceMainWeightsV1.Block15
import SourceMainWeightsV1.Block16
import SourceMainWeightsV1.Block17
import SourceMainWeightsV1.Block18
import SourceMainWeightsV1.Block19
import SourceMainWeightsV1.Block20
import SourceMainWeightsV1.Block21
import SourceMainWeightsV1.Block22
import SourceMainWeightsV1.Block23
import SynergyHeightC.MainWeightFold
namespace SourceMainWeightsV1.All
open ScopedNumerical SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def total : ProofBox := ⟨2869890699926766771202866067252394067,2869890699926766771254572444732902052⟩
private theorem chunked_step {n : Nat} {x y : ProofBox}
 (hx : chunked n=some x) (hy : block (32*n) 32=some y) :
 chunked (n+1)=some (ProofBox.add x y) := by
 exact congrArg₂ (fun a b : Option ProofBox => do
   let first ← a
   let second ← b
   pure (ProofBox.add first second)) hx hy
theorem exact_total : prefixSum 768=some total := by
 let s0 : ProofBox := ⟨0,0⟩
 have h0 : chunked 0=some s0 := rfl
 let s1 := ProofBox.add s0 SourceMainWeightsV1.Block00.result
 have h1 : chunked 1=some s1 := chunked_step (n:=0) (x:=s0) (y:=SourceMainWeightsV1.Block00.result) h0 SourceMainWeightsV1.Block00.exact_sum
 let s2 := ProofBox.add s1 SourceMainWeightsV1.Block01.result
 have h2 : chunked 2=some s2 := chunked_step (n:=1) (x:=s1) (y:=SourceMainWeightsV1.Block01.result) h1 SourceMainWeightsV1.Block01.exact_sum
 let s3 := ProofBox.add s2 SourceMainWeightsV1.Block02.result
 have h3 : chunked 3=some s3 := chunked_step (n:=2) (x:=s2) (y:=SourceMainWeightsV1.Block02.result) h2 SourceMainWeightsV1.Block02.exact_sum
 let s4 := ProofBox.add s3 SourceMainWeightsV1.Block03.result
 have h4 : chunked 4=some s4 := chunked_step (n:=3) (x:=s3) (y:=SourceMainWeightsV1.Block03.result) h3 SourceMainWeightsV1.Block03.exact_sum
 let s5 := ProofBox.add s4 SourceMainWeightsV1.Block04.result
 have h5 : chunked 5=some s5 := chunked_step (n:=4) (x:=s4) (y:=SourceMainWeightsV1.Block04.result) h4 SourceMainWeightsV1.Block04.exact_sum
 let s6 := ProofBox.add s5 SourceMainWeightsV1.Block05.result
 have h6 : chunked 6=some s6 := chunked_step (n:=5) (x:=s5) (y:=SourceMainWeightsV1.Block05.result) h5 SourceMainWeightsV1.Block05.exact_sum
 let s7 := ProofBox.add s6 SourceMainWeightsV1.Block06.result
 have h7 : chunked 7=some s7 := chunked_step (n:=6) (x:=s6) (y:=SourceMainWeightsV1.Block06.result) h6 SourceMainWeightsV1.Block06.exact_sum
 let s8 := ProofBox.add s7 SourceMainWeightsV1.Block07.result
 have h8 : chunked 8=some s8 := chunked_step (n:=7) (x:=s7) (y:=SourceMainWeightsV1.Block07.result) h7 SourceMainWeightsV1.Block07.exact_sum
 let s9 := ProofBox.add s8 SourceMainWeightsV1.Block08.result
 have h9 : chunked 9=some s9 := chunked_step (n:=8) (x:=s8) (y:=SourceMainWeightsV1.Block08.result) h8 SourceMainWeightsV1.Block08.exact_sum
 let s10 := ProofBox.add s9 SourceMainWeightsV1.Block09.result
 have h10 : chunked 10=some s10 := chunked_step (n:=9) (x:=s9) (y:=SourceMainWeightsV1.Block09.result) h9 SourceMainWeightsV1.Block09.exact_sum
 let s11 := ProofBox.add s10 SourceMainWeightsV1.Block10.result
 have h11 : chunked 11=some s11 := chunked_step (n:=10) (x:=s10) (y:=SourceMainWeightsV1.Block10.result) h10 SourceMainWeightsV1.Block10.exact_sum
 let s12 := ProofBox.add s11 SourceMainWeightsV1.Block11.result
 have h12 : chunked 12=some s12 := chunked_step (n:=11) (x:=s11) (y:=SourceMainWeightsV1.Block11.result) h11 SourceMainWeightsV1.Block11.exact_sum
 let s13 := ProofBox.add s12 SourceMainWeightsV1.Block12.result
 have h13 : chunked 13=some s13 := chunked_step (n:=12) (x:=s12) (y:=SourceMainWeightsV1.Block12.result) h12 SourceMainWeightsV1.Block12.exact_sum
 let s14 := ProofBox.add s13 SourceMainWeightsV1.Block13.result
 have h14 : chunked 14=some s14 := chunked_step (n:=13) (x:=s13) (y:=SourceMainWeightsV1.Block13.result) h13 SourceMainWeightsV1.Block13.exact_sum
 let s15 := ProofBox.add s14 SourceMainWeightsV1.Block14.result
 have h15 : chunked 15=some s15 := chunked_step (n:=14) (x:=s14) (y:=SourceMainWeightsV1.Block14.result) h14 SourceMainWeightsV1.Block14.exact_sum
 let s16 := ProofBox.add s15 SourceMainWeightsV1.Block15.result
 have h16 : chunked 16=some s16 := chunked_step (n:=15) (x:=s15) (y:=SourceMainWeightsV1.Block15.result) h15 SourceMainWeightsV1.Block15.exact_sum
 let s17 := ProofBox.add s16 SourceMainWeightsV1.Block16.result
 have h17 : chunked 17=some s17 := chunked_step (n:=16) (x:=s16) (y:=SourceMainWeightsV1.Block16.result) h16 SourceMainWeightsV1.Block16.exact_sum
 let s18 := ProofBox.add s17 SourceMainWeightsV1.Block17.result
 have h18 : chunked 18=some s18 := chunked_step (n:=17) (x:=s17) (y:=SourceMainWeightsV1.Block17.result) h17 SourceMainWeightsV1.Block17.exact_sum
 let s19 := ProofBox.add s18 SourceMainWeightsV1.Block18.result
 have h19 : chunked 19=some s19 := chunked_step (n:=18) (x:=s18) (y:=SourceMainWeightsV1.Block18.result) h18 SourceMainWeightsV1.Block18.exact_sum
 let s20 := ProofBox.add s19 SourceMainWeightsV1.Block19.result
 have h20 : chunked 20=some s20 := chunked_step (n:=19) (x:=s19) (y:=SourceMainWeightsV1.Block19.result) h19 SourceMainWeightsV1.Block19.exact_sum
 let s21 := ProofBox.add s20 SourceMainWeightsV1.Block20.result
 have h21 : chunked 21=some s21 := chunked_step (n:=20) (x:=s20) (y:=SourceMainWeightsV1.Block20.result) h20 SourceMainWeightsV1.Block20.exact_sum
 let s22 := ProofBox.add s21 SourceMainWeightsV1.Block21.result
 have h22 : chunked 22=some s22 := chunked_step (n:=21) (x:=s21) (y:=SourceMainWeightsV1.Block21.result) h21 SourceMainWeightsV1.Block21.exact_sum
 let s23 := ProofBox.add s22 SourceMainWeightsV1.Block22.result
 have h23 : chunked 23=some s23 := chunked_step (n:=22) (x:=s22) (y:=SourceMainWeightsV1.Block22.result) h22 SourceMainWeightsV1.Block22.exact_sum
 let s24 := ProofBox.add s23 SourceMainWeightsV1.Block23.result
 have h24 : chunked 24=some s24 := chunked_step (n:=23) (x:=s23) (y:=SourceMainWeightsV1.Block23.result) h23 SourceMainWeightsV1.Block23.exact_sum

 have fixed : s24=total := by decide +kernel
 have final : chunked 24=some total := h24.trans (congrArg some fixed)
 exact (block_eq_chunked 24).trans final
theorem upper_word_bound : total.hi*1000000000000 ≤
    8433850764*ProofBox.scale 128 := by decide +kernel
theorem all_domains (i : Nat) (hi : i < 768) : cellDomain i=true := by
 let j := i/32
 have hj : j < 24 := by dsimp [j]; omega
 have lower : 32*j ≤ i := by dsimp [j]; omega
 have upper : i < 32*j+32 := by dsimp [j]; omega
 interval_cases j
 · exact domain_of_block (lo:=0) (i:=i) SourceMainWeightsV1.Block00.domains (by omega) (by omega)
 · exact domain_of_block (lo:=32) (i:=i) SourceMainWeightsV1.Block01.domains (by omega) (by omega)
 · exact domain_of_block (lo:=64) (i:=i) SourceMainWeightsV1.Block02.domains (by omega) (by omega)
 · exact domain_of_block (lo:=96) (i:=i) SourceMainWeightsV1.Block03.domains (by omega) (by omega)
 · exact domain_of_block (lo:=128) (i:=i) SourceMainWeightsV1.Block04.domains (by omega) (by omega)
 · exact domain_of_block (lo:=160) (i:=i) SourceMainWeightsV1.Block05.domains (by omega) (by omega)
 · exact domain_of_block (lo:=192) (i:=i) SourceMainWeightsV1.Block06.domains (by omega) (by omega)
 · exact domain_of_block (lo:=224) (i:=i) SourceMainWeightsV1.Block07.domains (by omega) (by omega)
 · exact domain_of_block (lo:=256) (i:=i) SourceMainWeightsV1.Block08.domains (by omega) (by omega)
 · exact domain_of_block (lo:=288) (i:=i) SourceMainWeightsV1.Block09.domains (by omega) (by omega)
 · exact domain_of_block (lo:=320) (i:=i) SourceMainWeightsV1.Block10.domains (by omega) (by omega)
 · exact domain_of_block (lo:=352) (i:=i) SourceMainWeightsV1.Block11.domains (by omega) (by omega)
 · exact domain_of_block (lo:=384) (i:=i) SourceMainWeightsV1.Block12.domains (by omega) (by omega)
 · exact domain_of_block (lo:=416) (i:=i) SourceMainWeightsV1.Block13.domains (by omega) (by omega)
 · exact domain_of_block (lo:=448) (i:=i) SourceMainWeightsV1.Block14.domains (by omega) (by omega)
 · exact domain_of_block (lo:=480) (i:=i) SourceMainWeightsV1.Block15.domains (by omega) (by omega)
 · exact domain_of_block (lo:=512) (i:=i) SourceMainWeightsV1.Block16.domains (by omega) (by omega)
 · exact domain_of_block (lo:=544) (i:=i) SourceMainWeightsV1.Block17.domains (by omega) (by omega)
 · exact domain_of_block (lo:=576) (i:=i) SourceMainWeightsV1.Block18.domains (by omega) (by omega)
 · exact domain_of_block (lo:=608) (i:=i) SourceMainWeightsV1.Block19.domains (by omega) (by omega)
 · exact domain_of_block (lo:=640) (i:=i) SourceMainWeightsV1.Block20.domains (by omega) (by omega)
 · exact domain_of_block (lo:=672) (i:=i) SourceMainWeightsV1.Block21.domains (by omega) (by omega)
 · exact domain_of_block (lo:=704) (i:=i) SourceMainWeightsV1.Block22.domains (by omega) (by omega)
 · exact domain_of_block (lo:=736) (i:=i) SourceMainWeightsV1.Block23.domains (by omega) (by omega)
end SourceMainWeightsV1.All
open Lean Elab
run_elab do
 for n in ([`SourceMainWeightsV1.All.exact_total,`SourceMainWeightsV1.All.upper_word_bound,
   `SourceMainWeightsV1.All.all_domains] : List Name) do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing aggregate root"
  let ax ← Lean.collectAxioms n
  logInfo m!"MAIN_SUM_AUDIT {(Json.mkObj [("name",toJson n.toString),("type_repr",toJson (reprStr ci.type)),("axioms",toJson (ax.toList.map Name.toString))]).compress}"

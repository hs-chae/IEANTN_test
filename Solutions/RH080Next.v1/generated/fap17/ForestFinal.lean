import ForestTablesCheck
import ForestCheck01
import ForestCheck02
import ForestCheck03
import ForestCheck04
import ForestCheck05
import ForestCheck06
import ForestCheck07
import ForestCheck08
import ForestCheck09
import ForestCheck10
import ForestCheck11
import ForestCheck12
import ForestCheck13
import ForestCheck14
import ForestCheck15
import ForestCheck16
import ForestCheck17
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT.IntegerModel
theorem complete_forest : ForestTrace stages (input 131072) 17 1 0 out17 := by
  have h0 : ForestTrace stages (input 131072) 0 131072 0 leaves := leaf_forest stages (input 131072) 131072 131072
  have h1 : ForestTrace stages (input 131072) 1 65536 0 out01 := layer_step h0 (by decide +kernel) layer01_trace
  have h2 : ForestTrace stages (input 131072) 2 32768 0 out02 := layer_step h1 (by decide +kernel) layer02_trace
  have h3 : ForestTrace stages (input 131072) 3 16384 0 out03 := layer_step h2 (by decide +kernel) layer03_trace
  have h4 : ForestTrace stages (input 131072) 4 8192 0 out04 := layer_step h3 (by decide +kernel) layer04_trace
  have h5 : ForestTrace stages (input 131072) 5 4096 0 out05 := layer_step h4 (by decide +kernel) layer05_trace
  have h6 : ForestTrace stages (input 131072) 6 2048 0 out06 := layer_step h5 (by decide +kernel) layer06_trace
  have h7 : ForestTrace stages (input 131072) 7 1024 0 out07 := layer_step h6 (by decide +kernel) layer07_trace
  have h8 : ForestTrace stages (input 131072) 8 512 0 out08 := layer_step h7 (by decide +kernel) layer08_trace
  have h9 : ForestTrace stages (input 131072) 9 256 0 out09 := layer_step h8 (by decide +kernel) layer09_trace
  have h10 : ForestTrace stages (input 131072) 10 128 0 out10 := layer_step h9 (by decide +kernel) layer10_trace
  have h11 : ForestTrace stages (input 131072) 11 64 0 out11 := layer_step h10 (by decide +kernel) layer11_trace
  have h12 : ForestTrace stages (input 131072) 12 32 0 out12 := layer_step h11 (by decide +kernel) layer12_trace
  have h13 : ForestTrace stages (input 131072) 13 16 0 out13 := layer_step h12 (by decide +kernel) layer13_trace
  have h14 : ForestTrace stages (input 131072) 14 8 0 out14 := layer_step h13 (by decide +kernel) layer14_trace
  have h15 : ForestTrace stages (input 131072) 15 4 0 out15 := layer_step h14 (by decide +kernel) layer15_trace
  have h16 : ForestTrace stages (input 131072) 16 2 0 out16 := layer_step h15 (by decide +kernel) layer16_trace
  have h17 : ForestTrace stages (input 131072) 17 1 0 out17 := layer_step h16 (by decide +kernel) layer17_trace
  exact h17
def output : List CInt := out17.head!
theorem complete_execution : ExecutionTrace stages (input 131072) 17 0 1 output := singleton_execution complete_forest
def totalAbs : Nat := output.foldl (fun a z => a+z.1.natAbs) 0
theorem total_checked : totalAbs=102468342420806369668447945569060309170116 := by decide +kernel
def quad : Nat := (List.range 400).foldl (fun a j => a+20*j*j*(coefficient j).natAbs) 0
theorem quad_checked : quad=12681061983660556400000 := by decide +kernel
def sourceNumerator : Nat := ceilDiv (ceilDiv totalAbs 1000000000000000000) 131072 + ceilDiv (ceilDiv (ceilDiv (100*quad) 3) 131072) 131072 + 20
theorem numerator_checked : sourceNumerator=781796015790084776 := by
  unfold sourceNumerator
  rw [total_checked,quad_checked]
  decide +kernel
#print axioms complete_execution
#print axioms numerator_checked
end FapForest17

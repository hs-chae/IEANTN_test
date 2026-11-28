import W4D13E01G0
import W4D13E02G0
import W4D13E03G0
import W4D13E04G0
import W4D13E05G0
import W4D13E06G0
import W4D13E07G0
import W4D13E08G0
import W4D13E09G0
import W4D13E10G0
import W4D13E11G0
import W4D13E12G0
import W4D13N13G0
import W4D13Tables
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace W4DAG13
open RH080Next.FFT.IntegerModel
def output : List CInt := W4D13N13G0.o13_0
theorem complete_execution : ExecutionTrace stages actualInput 13 0 1 output := W4D13N13G0.exec13_0
def topTail : List CInt := (((W4D13W13G0.w0.tail ++ W4D13W13G0.w1) ++ (W4D13W13G0.w2 ++ W4D13W13G0.w3)) ++ ((W4D13W13G0.w4 ++ W4D13W13G0.w5) ++ (W4D13W13G0.w6 ++ W4D13W13G0.w7)))
theorem top_shape : w13=(unit,0)::topTail := by
  have hh : W4D13W13G0.w0=(unit,0)::W4D13W13G0.w0.tail := by rfl
  unfold w13 topTail
  rw [hh]
  simp only [List.cons_append,List.tail_cons]
theorem global_twiddle_trace : TwiddleTrace seed (unit,0) w13.tail := by
  rw [top_shape]
  exact TwiddleSegment.forget_final (TwiddleSegment.append (TwiddleSegment.append (TwiddleSegment.append W4D13W13G0.segment0 W4D13W13G0.segment1) (TwiddleSegment.append W4D13W13G0.segment2 W4D13W13G0.segment3)) (TwiddleSegment.append (TwiddleSegment.append W4D13W13G0.segment4 W4D13W13G0.segment5) (TwiddleSegment.append W4D13W13G0.segment6 W4D13W13G0.segment7)))
theorem decimation01 : EvenTrace w02 w01 := EvenBlock.trace W4D13E01G0.block0
theorem decimation02 : EvenTrace w03 w02 := EvenBlock.trace W4D13E02G0.block0
theorem decimation03 : EvenTrace w04 w03 := EvenBlock.trace W4D13E03G0.block0
theorem decimation04 : EvenTrace w05 w04 := EvenBlock.trace W4D13E04G0.block0
theorem decimation05 : EvenTrace w06 w05 := EvenBlock.trace W4D13E05G0.block0
theorem decimation06 : EvenTrace w07 w06 := EvenBlock.trace W4D13E06G0.block0
theorem decimation07 : EvenTrace w08 w07 := EvenBlock.trace W4D13E07G0.block0
theorem decimation08 : EvenTrace w09 w08 := EvenBlock.trace W4D13E08G0.block0
theorem decimation09 : EvenTrace w10 w09 := EvenBlock.trace W4D13E09G0.block0
theorem decimation10 : EvenTrace w11 w10 := EvenBlock.trace W4D13E10G0.block0
theorem decimation11 : EvenTrace w12 w11 := EvenBlock.trace (EvenBlock.append W4D13E11G0.block0 W4D13E11G0.block1)
theorem decimation12 : EvenTrace w13 w12 := EvenBlock.trace (EvenBlock.append (EvenBlock.append W4D13E12G0.block0 W4D13E12G0.block1) (EvenBlock.append W4D13E12G0.block2 W4D13E12G0.block3))
theorem total_checked : absSum output=6398463156004875908672494257953393460578 := by
  unfold output W4D13N13G0.o13_0
  simp only [absSum_append,W4D13B13I0G0.p13_0_0_sum,W4D13B13I0G0.q13_0_0_sum,W4D13B13I0G0.p13_0_1_sum,W4D13B13I0G0.q13_0_1_sum,W4D13B13I0G0.p13_0_2_sum,W4D13B13I0G0.q13_0_2_sum,W4D13B13I0G0.p13_0_3_sum,W4D13B13I0G0.q13_0_3_sum,W4D13B13I0G1.p13_0_4_sum,W4D13B13I0G1.q13_0_4_sum,W4D13B13I0G1.p13_0_5_sum,W4D13B13I0G1.q13_0_5_sum,W4D13B13I0G1.p13_0_6_sum,W4D13B13I0G1.q13_0_6_sum,W4D13B13I0G1.p13_0_7_sum,W4D13B13I0G1.q13_0_7_sum]
  all_goals decide +kernel
theorem quad_checked : RH080Next.FFT.IntegerModel.W4.quad=1157537949152935144487960 := by decide +kernel
theorem numerator_checked : RH080Next.FFT.IntegerModel.W4.normFromOutput 8192 output=13560177159173855 := by
  unfold RH080Next.FFT.IntegerModel.W4.normFromOutput
  rw [fold_absSum,Nat.zero_add,total_checked,quad_checked]
  all_goals decide +kernel
#print axioms complete_execution
#print axioms global_twiddle_trace
#print axioms numerator_checked
#print axioms decimation01
#print axioms decimation02
#print axioms decimation03
#print axioms decimation04
#print axioms decimation05
#print axioms decimation06
#print axioms decimation07
#print axioms decimation08
#print axioms decimation09
#print axioms decimation10
#print axioms decimation11
#print axioms decimation12

end W4DAG13

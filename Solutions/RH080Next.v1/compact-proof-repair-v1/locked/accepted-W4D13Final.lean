import TopShapeSymbolic
import NormSymbolic
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
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.output"
    handle.flush
def output : List CInt := W4D13N13G0.o13_0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.output"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.complete_execution"
    handle.flush
theorem complete_execution : ExecutionTrace stages actualInput 13 0 1 output := W4D13N13G0.exec13_0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.complete_execution"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.topTail"
    handle.flush
def topTail : List CInt := (((W4D13W13G0.w0.tail ++ W4D13W13G0.w1) ++ (W4D13W13G0.w2 ++ W4D13W13G0.w3)) ++ ((W4D13W13G0.w4 ++ W4D13W13G0.w5) ++ (W4D13W13G0.w6 ++ W4D13W13G0.w7)))
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.topTail"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.top_shape"
    handle.flush
theorem top_shape : w13=(unit,0)::topTail := by
  let rs : List (List CInt) := [W4D13W13G0.w1,
    (W4D13W13G0.w2 ++ W4D13W13G0.w3),
    ((W4D13W13G0.w4 ++ W4D13W13G0.w5) ++ (W4D13W13G0.w6 ++ W4D13W13G0.w7))]
  let C : List CInt → List CInt := fun l => rs.foldl (fun left right => left ++ right) l
  have hh : W4D13W13G0.w0 = (unit,0) :: W4D13W13G0.w0.tail := by rfl
  calc
    w13 = C W4D13W13G0.w0 := by rfl
    _ = C ((unit,0) :: W4D13W13G0.w0.tail) := congrArg C hh
    _ = (unit,0) :: C W4D13W13G0.w0.tail :=
      RH080Next.PrivateTopShape.appendFold_cons (unit,0) W4D13W13G0.w0.tail rs
    _ = (unit,0) :: topTail := by rfl
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.top_shape"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.global_twiddle_trace"
    handle.flush
theorem global_twiddle_trace : TwiddleTrace seed (unit,0) w13.tail := by
  rw [top_shape]
  exact TwiddleSegment.forget_final (TwiddleSegment.append (TwiddleSegment.append (TwiddleSegment.append W4D13W13G0.segment0 W4D13W13G0.segment1) (TwiddleSegment.append W4D13W13G0.segment2 W4D13W13G0.segment3)) (TwiddleSegment.append (TwiddleSegment.append W4D13W13G0.segment4 W4D13W13G0.segment5) (TwiddleSegment.append W4D13W13G0.segment6 W4D13W13G0.segment7)))
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.global_twiddle_trace"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation01"
    handle.flush
theorem decimation01 : EvenTrace w02 w01 := EvenBlock.trace W4D13E01G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation01"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation02"
    handle.flush
theorem decimation02 : EvenTrace w03 w02 := EvenBlock.trace W4D13E02G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation02"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation03"
    handle.flush
theorem decimation03 : EvenTrace w04 w03 := EvenBlock.trace W4D13E03G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation03"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation04"
    handle.flush
theorem decimation04 : EvenTrace w05 w04 := EvenBlock.trace W4D13E04G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation04"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation05"
    handle.flush
theorem decimation05 : EvenTrace w06 w05 := EvenBlock.trace W4D13E05G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation05"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation06"
    handle.flush
theorem decimation06 : EvenTrace w07 w06 := EvenBlock.trace W4D13E06G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation06"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation07"
    handle.flush
theorem decimation07 : EvenTrace w08 w07 := EvenBlock.trace W4D13E07G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation07"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation08"
    handle.flush
theorem decimation08 : EvenTrace w09 w08 := EvenBlock.trace W4D13E08G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation08"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation09"
    handle.flush
theorem decimation09 : EvenTrace w10 w09 := EvenBlock.trace W4D13E09G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation09"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation10"
    handle.flush
theorem decimation10 : EvenTrace w11 w10 := EvenBlock.trace W4D13E10G0.block0
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation10"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation11"
    handle.flush
theorem decimation11 : EvenTrace w12 w11 := EvenBlock.trace (EvenBlock.append W4D13E11G0.block0 W4D13E11G0.block1)
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation11"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.decimation12"
    handle.flush
theorem decimation12 : EvenTrace w13 w12 := EvenBlock.trace (EvenBlock.append (EvenBlock.append W4D13E12G0.block0 W4D13E12G0.block1) (EvenBlock.append W4D13E12G0.block2 W4D13E12G0.block3))
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.decimation12"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.total_checked"
    handle.flush
theorem total_checked : absSum output=6398463156004875908672494257953393460578 := by
  unfold output W4D13N13G0.o13_0
  simp only [absSum_append,W4D13B13I0G0.p13_0_0_sum,W4D13B13I0G0.q13_0_0_sum,W4D13B13I0G0.p13_0_1_sum,W4D13B13I0G0.q13_0_1_sum,W4D13B13I0G0.p13_0_2_sum,W4D13B13I0G0.q13_0_2_sum,W4D13B13I0G0.p13_0_3_sum,W4D13B13I0G0.q13_0_3_sum,W4D13B13I0G1.p13_0_4_sum,W4D13B13I0G1.q13_0_4_sum,W4D13B13I0G1.p13_0_5_sum,W4D13B13I0G1.q13_0_5_sum,W4D13B13I0G1.p13_0_6_sum,W4D13B13I0G1.q13_0_6_sum,W4D13B13I0G1.p13_0_7_sum,W4D13B13I0G1.q13_0_7_sum]
  all_goals decide +kernel
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.total_checked"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.quad_checked"
    handle.flush
theorem quad_checked : RH080Next.FFT.IntegerModel.W4.quad=1157537949152935144487960 := by decide +kernel
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.quad_checked"
    handle.flush
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_BEGIN W4DAG13.numerator_checked"
    handle.flush
theorem numerator_checked : RH080Next.FFT.IntegerModel.W4.normFromOutput 8192 output=13560177159173855 := by
  exact (RH080Next.PrivateNormProof.normFromOutput_of_totals 8192 output
    6398463156004875908672494257953393460578 1157537949152935144487960
    total_checked quad_checked).trans (by decide +kernel)
run_cmd do
  match ← IO.getEnv "IEANTN_STAGED_PROOF_PROGRESS" with
  | none => pure ()
  | some path =>
    let handle ← IO.FS.Handle.mk path .append
    handle.putStrLn "COMPACT_END W4DAG13.numerator_checked"
    handle.flush
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

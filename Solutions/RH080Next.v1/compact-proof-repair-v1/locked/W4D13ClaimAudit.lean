import W4D13Final
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace W4ClaimAudit13
theorem execution : RH080Next.FFT.IntegerModel.ExecutionTrace W4DAG13.stages (RH080Next.FFT.IntegerModel.W4.input 8192) 13 0 1 W4DAG13.output := W4DAG13.complete_execution
theorem seed_exact : W4DAG13.seed=RH080Next.FFT.IntegerModel.root 8192 := by decide +kernel
theorem twiddle : RH080Next.FFT.IntegerModel.TwiddleTrace (RH080Next.FFT.IntegerModel.root 8192) (RH080Next.FFT.IntegerModel.unit,0) (W4DAG13.stages 13).tail := by
  rw [←seed_exact]
  exact W4DAG13.global_twiddle_trace
theorem lengths : ∀ t<13, (W4DAG13.stages (t+1)).length=2^t := W4DAG13.stage_lengths
theorem top_shape : ∃ tail, W4DAG13.stages 13=(RH080Next.FFT.IntegerModel.unit,0)::tail := ⟨W4DAG13.topTail, W4DAG13.top_shape⟩
theorem numerator : RH080Next.FFT.IntegerModel.W4.normFromOutput 8192 W4DAG13.output=13560177159173855 := W4DAG13.numerator_checked
theorem step01 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 2) (W4DAG13.stages 1) := W4DAG13.decimation01
theorem step02 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 3) (W4DAG13.stages 2) := W4DAG13.decimation02
theorem step03 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 4) (W4DAG13.stages 3) := W4DAG13.decimation03
theorem step04 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 5) (W4DAG13.stages 4) := W4DAG13.decimation04
theorem step05 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 6) (W4DAG13.stages 5) := W4DAG13.decimation05
theorem step06 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 7) (W4DAG13.stages 6) := W4DAG13.decimation06
theorem step07 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 8) (W4DAG13.stages 7) := W4DAG13.decimation07
theorem step08 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 9) (W4DAG13.stages 8) := W4DAG13.decimation08
theorem step09 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 10) (W4DAG13.stages 9) := W4DAG13.decimation09
theorem step10 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 11) (W4DAG13.stages 10) := W4DAG13.decimation10
theorem step11 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 12) (W4DAG13.stages 11) := W4DAG13.decimation11
theorem step12 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG13.stages 13) (W4DAG13.stages 12) := W4DAG13.decimation12
#print axioms execution
#print axioms seed_exact
#print axioms twiddle
#print axioms lengths
#print axioms top_shape
#print axioms numerator
#print axioms step01
#print axioms step02
#print axioms step03
#print axioms step04
#print axioms step05
#print axioms step06
#print axioms step07
#print axioms step08
#print axioms step09
#print axioms step10
#print axioms step11
#print axioms step12
end W4ClaimAudit13

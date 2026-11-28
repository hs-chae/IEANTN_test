import W4D24Final
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section
namespace W4ClaimAudit24
theorem execution : RH080Next.FFT.IntegerModel.ExecutionTrace W4DAG24.stages (RH080Next.FFT.IntegerModel.W4.input 16777216) 24 0 1 W4DAG24.output := W4DAG24.complete_execution
theorem seed_exact : W4DAG24.seed=RH080Next.FFT.IntegerModel.root 16777216 := by decide +kernel
theorem twiddle : RH080Next.FFT.IntegerModel.TwiddleTrace (RH080Next.FFT.IntegerModel.root 16777216) (RH080Next.FFT.IntegerModel.unit,0) (W4DAG24.stages 24).tail := by
  rw [←seed_exact]
  exact W4DAG24.global_twiddle_trace
theorem lengths : ∀ t<24, (W4DAG24.stages (t+1)).length=2^t := W4DAG24.stage_lengths
theorem top_shape : ∃ tail, W4DAG24.stages 24=(RH080Next.FFT.IntegerModel.unit,0)::tail := ⟨W4DAG24.topTail, W4DAG24.top_shape⟩
theorem numerator : RH080Next.FFT.IntegerModel.W4.normFromOutput 16777216 W4DAG24.output=7813568381279800 := W4DAG24.numerator_checked
theorem step01 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 2) (W4DAG24.stages 1) := W4DAG24.decimation01
theorem step02 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 3) (W4DAG24.stages 2) := W4DAG24.decimation02
theorem step03 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 4) (W4DAG24.stages 3) := W4DAG24.decimation03
theorem step04 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 5) (W4DAG24.stages 4) := W4DAG24.decimation04
theorem step05 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 6) (W4DAG24.stages 5) := W4DAG24.decimation05
theorem step06 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 7) (W4DAG24.stages 6) := W4DAG24.decimation06
theorem step07 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 8) (W4DAG24.stages 7) := W4DAG24.decimation07
theorem step08 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 9) (W4DAG24.stages 8) := W4DAG24.decimation08
theorem step09 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 10) (W4DAG24.stages 9) := W4DAG24.decimation09
theorem step10 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 11) (W4DAG24.stages 10) := W4DAG24.decimation10
theorem step11 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 12) (W4DAG24.stages 11) := W4DAG24.decimation11
theorem step12 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 13) (W4DAG24.stages 12) := W4DAG24.decimation12
theorem step13 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 14) (W4DAG24.stages 13) := W4DAG24.decimation13
theorem step14 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 15) (W4DAG24.stages 14) := W4DAG24.decimation14
theorem step15 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 16) (W4DAG24.stages 15) := W4DAG24.decimation15
theorem step16 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 17) (W4DAG24.stages 16) := W4DAG24.decimation16
theorem step17 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 18) (W4DAG24.stages 17) := W4DAG24.decimation17
theorem step18 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 19) (W4DAG24.stages 18) := W4DAG24.decimation18
theorem step19 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 20) (W4DAG24.stages 19) := W4DAG24.decimation19
theorem step20 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 21) (W4DAG24.stages 20) := W4DAG24.decimation20
theorem step21 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 22) (W4DAG24.stages 21) := W4DAG24.decimation21
theorem step22 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 23) (W4DAG24.stages 22) := W4DAG24.decimation22
theorem step23 : RH080Next.FFT.IntegerModel.EvenTrace (W4DAG24.stages 24) (W4DAG24.stages 23) := W4DAG24.decimation23
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
#print axioms step13
#print axioms step14
#print axioms step15
#print axioms step16
#print axioms step17
#print axioms step18
#print axioms step19
#print axioms step20
#print axioms step21
#print axioms step22
#print axioms step23
end W4ClaimAudit24

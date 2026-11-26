import FFTInterpreter
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RH080Next.FFTPV.Certified
/-- Closed computation of the actual source root initializer through the reused
proof-producing C interpreter; expected literals are untrusted candidate outputs. -/
theorem actual_root_result : rootResult=some [0, 239728737, 242879801, 999929872, 999999999, 0, 0, 169179084, 384123903, 507028292, 374, 0, 1] := by
  decide +kernel
#print axioms actual_root_result
end RH080Next.FFTPV.Certified

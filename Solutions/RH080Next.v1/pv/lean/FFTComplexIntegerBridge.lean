/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexCorrect
import FFTPairedIntModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource

/-- The exact source-derived complex arithmetic is the same paired-integer
operation consumed by the independently checked FFT operational traces. Each
real product is Euclidean-rounded before the two signed additions. -/
theorem resultPair_eq_integer_mul (input : Input) :
    resultPair input=FFT.IntegerModel.mul
      (pair (input.old (input.layout.object .a)) (input.layout.start .a))
      (pair (input.old (input.layout.object .b)) (input.layout.start .b)):=by
  norm_num [resultPair,sumValue,productValue,aOffset,bOffset,pair,FFT.IntegerModel.mul,FFT.IntegerModel.unit,unit]

#print axioms resultPair_eq_integer_mul
end RH080Next.FFTPV.ComplexSource

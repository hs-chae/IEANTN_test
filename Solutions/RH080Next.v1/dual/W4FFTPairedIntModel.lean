/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCertificateComposition
import WindowData

set_option autoImplicit false
namespace RH080Next.FFT.IntegerModel.W4

def coefficient (j : Nat) : Int := (RH080Next.WindowPV.Data.encodedNode j:Int)-10000000000000000

def input (n j : Nat) : CInt := sparseInput 2520 coefficient n j

def quad : Nat := (List.range 2520).foldl (fun a j => a+20*j*j*(coefficient j).natAbs) 0

/-- The independently ported w4 source's exact final upward divisions, with its
100-ulp FFT allowance. This alone is not an execution theorem or source PV. -/
def normFromOutput (n : Nat) (out : List CInt) : Nat :=
  let total := out.foldl (fun a z => a+z.1.natAbs) 0
  let first := ceilDiv (ceilDiv (ceilDiv total 1000000000000000000) 100) n
  let second := ceilDiv (ceilDiv (ceilDiv quad 3) n) n
  first+second+100

end RH080Next.FFT.IntegerModel.W4

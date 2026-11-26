/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapData

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FFT.IntegerModel

abbrev CInt := Int × Int
def unit : Int := 1000000000000000000000000000000000000
def piInteger : Int := 3141592653589793238462643383279502884
def mul (a b : CInt) : CInt :=
  ((a.1*b.1)/unit-(a.2*b.2)/unit,(a.1*b.2)/unit+(a.2*b.1)/unit)
def add (a b : CInt) : CInt := (a.1+b.1,a.2+b.2)
def sub (a b : CInt) : CInt := (a.1-b.1,a.2-b.2)

/-- Pure integer counterpart of the actual source's root initializer.
Source refinement and arithmetic guards are separate proof obligations. -/
def root (n : Nat) : CInt := Id.run do
  let x := (2*piInteger)/(n:Int)
  let x2 := (x*x)/unit
  let mut ct := unit
  let mut st := x
  let mut cr := unit
  let mut sr := x
  for j in List.range 10 do
    let i := j+1
    ct := ((ct*x2)/unit)/((2*i*(2*i-1):Nat):Int)
    st := ((st*x2)/unit)/((2*i*(2*i+1):Nat):Int)
    if i%2=1 then
      cr := cr-ct
      sr := sr-st
    else
      cr := cr+ct
      sr := sr+st
  return (cr,-sr)

def twiddles (n : Nat) (r : CInt) : Array CInt := Id.run do
  let mut out : Array CInt := #[(unit,0)]
  let mut previous : CInt := (unit,0)
  for _ in List.range (n/2-1) do
    previous := mul previous r
    out := out.push previous
  return out

def encoded : Array Nat := RH080Next.FapPV.Data.encoded.toArray
def coefficient (j : Nat) : Int := (encoded[j]?.getD 10000000000000000:Int)-10000000000000000
def input (n j : Nat) : CInt :=
  let k := if j<400 then j else n-j
  if k<400 then (coefficient k*100000000000000000000,0) else (0,0)

/-- Array-based version for the first performance benchmark. Array persistence
in kernel reduction must be measured; native evaluation alone is not evidence
of kernel verification or source-first PV. -/
def fft (n : Nat) (tw : Array CInt) : Nat → Nat → Nat → Array CInt
  | 0,index,_ => #[input n index]
  | s+1,index,step => Id.run do
    let half := 2^s
    let a := fft n tw s index (step*2)
    let b := fft n tw s (index+step) (step*2)
    let mut out := a++b
    let stride := n/(2*half)
    for j in List.range half do
      let av := out[j]?.getD (0,0)
      let bv := out[j+half]?.getD (0,0)
      let w := tw[j*stride]?.getD (0,0)
      let p := mul bv w
      out := out.set! j (add av p)
      out := out.set! (j+half) (sub av p)
    return out

def ceilDiv (a b : Nat) : Nat := a/b+(if a%b=0 then 0 else 1)

/-- Exact source normalization, including its successive upward divisions.
This definition omits the error sentinel: source proofs must establish all
word/limb bounds and zero status before relating a successful C return to it. -/
def normWithRoot (s : Nat) (r : CInt) : Nat := Id.run do
  let n := 2^s
  let tw := twiddles n r
  let out := fft n tw s 0 1
  let total := out.foldl (fun a z => a+z.1.natAbs) 0
  let first := ceilDiv (ceilDiv total 1000000000000000000) n
  let quad := (List.range 400).foldl (fun a j => a+20*j*j*(coefficient j).natAbs) 0
  let second := ceilDiv (ceilDiv (ceilDiv (100*quad) 3) n) n
  return first+second+20

def normNumerator (s : Nat) : Nat := normWithRoot s (root (2^s))

end RH080Next.FFT.IntegerModel

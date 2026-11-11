/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.PointProgram
import FKSComputationLed.Input
open LeanCert.Core LeanCert.Engine
namespace FKSComputationLed.CellProgram
open PointProgram Input

def eps : ℚ := 1/10^7
def errorInterval : IntervalDyadic := IntervalDyadic.ofIntervalRat
  ⟨-eps,eps,by norm_num [eps]⟩ cfg.precision

def base : IntervalDyadic × Bool := primitivePoint 2
structure PointInfo where
  logI : IntervalDyadic
  liI : IntervalDyadic
  weightI : IntervalDyadic
  valid : Bool

def pointInfo (n : Nat) : PointInfo :=
  let logv := logPoint n
  let prim := run primitiveExpr logv.1
  let sq := run (.exp (.mul (.const (1/2)) (.var 0))) logv.1
  let wt := LeanCert.Internal.Dyadic.evalPreparedCached
    (.mul (.var 0) (.inv (.var 1))) (fun i=>if i=0 then logv.1 else sq.1) ctx
  { logI := logv.1
    liI := IntervalDyadic.add (IntervalDyadic.sub prim.1 base.1) errorInterval
    weightI := wt.1
    valid := decide (2≤n) && logv.2 && prim.2 && base.2 && sq.2 && wt.2 &&
      logv.1.lowerBoundedBy 2 && logv.1.upperBoundedBy 24 }

def cellCheck (left right : PointInfo) (z : Cell) : Bool :=
  let upperGap := IntervalDyadic.sub right.liI (integerInterval z.ca)
  let lowerGap := IntervalDyadic.sub (integerInterval z.cb) left.liI
  left.valid && right.valid &&
    (IntervalDyadic.mul upperGap left.weightI).upperBoundedBy (19/10) &&
    (IntervalDyadic.mul lowerGap left.weightI).upperBoundedBy (19/10)

def cellsAux : List Cell → PointInfo → Bool
  | [],_ => true
  | z::zs,left =>
    let right := pointInfo z.b
    cellCheck left right z && cellsAux zs right

def numericGate (xs : Array Cell) : Bool :=
  if h : 0<xs.size then cellsAux xs.toList (pointInfo (xs[0]'h).a) else false

set_option maxRecDepth 100000
end FKSComputationLed.CellProgram

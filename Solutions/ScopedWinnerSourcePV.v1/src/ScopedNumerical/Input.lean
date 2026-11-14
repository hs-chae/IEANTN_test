/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LeanCert.Core.Expr

namespace ScopedNumerical.Input
open LeanCert.Core

/-- Parsed input instruction. Source `num`/`den` strings denote these integers. -/
structure Node where
  op : Nat
  a : Nat
  b : Nat
  num : Int
  den : Nat
  deriving Repr, DecidableEq

def step (values : Array Expr) (n : Node) : Expr :=
  if n.op = 0 then .const (mkRat n.num n.den)
  else if n.op = 1 then .var 0
  else if n.op = 2 then .add (values[n.a]?.getD (.const 0)) (values[n.b]?.getD (.const 0))
  else if n.op = 3 then .mul (values[n.a]?.getD (.const 0)) (values[n.b]?.getD (.const 0))
  else if n.op = 4 then .neg (values[n.a]?.getD (.const 0))
  else if n.op = 5 then .inv (values[n.a]?.getD (.const 0))
  else if n.op = 6 then .exp (values[n.a]?.getD (.const 0))
  else if n.op = 7 then .log (values[n.a]?.getD (.const 0))
  else if n.a = 0 then .namedConst .pi
  else .namedConst .eulerMascheroni

def decode (nodes : List Node) : Expr :=
  let values := nodes.foldl (fun values node => values.push (step values node)) #[]
  values.back?.getD (.const 0)

/-- Every read occurs after the referred instruction; literal denominators are positive. -/
def wellFormed (nodes : List Node) : Bool :=
  nodes.zipIdx.all fun (n,k) =>
    n.op ≤ 8 &&
    (if n.op = 0 then decide (0 < n.den)
     else if n.op = 1 then n.a == 0
     else if n.op = 8 then n.a ≤ 1
     else (n.a < k && (if n.op = 2 ∨ n.op = 3 then n.b < k else true)))

end ScopedNumerical.Input

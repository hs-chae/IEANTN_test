/- Separate environments: admitted challenge values never enter the Solution environment. -/
import Lean
open Lean
partial def canonicalType : Expr → Expr
  | .app f a => .app (canonicalType f) (canonicalType a)
  | .lam _ t b i => .lam .anonymous (canonicalType t) (canonicalType b) i
  | .forallE _ t b i => .forallE .anonymous (canonicalType t) (canonicalType b) i
  | .letE _ t v b n => .letE .anonymous (canonicalType t) (canonicalType v) (canonicalType b) n
  | .mdata _ e => canonicalType e
  | .proj n i e => .proj n i (canonicalType e)
  | e => e

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let actual ← importModules #[{module:=`Solution}] {}
  if actual.header.moduleNames.contains `IEANTN.Nodes.MomentPNT.v1.Challenge then
    throw <| IO.userError "admitted Challenge imported into actual Solution environment"
  let expected ← importModules #[{module:=`IEANTN.Nodes.MomentPNT.v1.Challenge}] {}
  for name in ([`MomentPNT.v1.challenge_moment_pi, `MomentPNT.v1.challenge_moment_psi,
      `MomentPNT.v1.challenge_kernel_control_pi, `MomentPNT.v1.challenge_kernel_control_psi,
      `MomentPNT.v1.challenge_moment_future_pi, `MomentPNT.v1.challenge_moment_prime_rich] : List Name) do
    let some a := actual.find? name | throw <| IO.userError s!"missing actual {name}"
    let some e := expected.find? name | throw <| IO.userError s!"missing expected {name}"
    if canonicalType a.type != canonicalType e.type then
      throw <| IO.userError s!"different exact type {name}"
    IO.println s!"EXACT_TYPE {name}"
  return 0

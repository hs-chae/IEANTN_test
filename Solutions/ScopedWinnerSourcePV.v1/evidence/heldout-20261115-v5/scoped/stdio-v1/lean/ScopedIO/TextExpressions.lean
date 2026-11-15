/- Executable expression subset for actual top-level text-I/O calls.
All nested argument evaluation uses the existing typed pureCall C semantics;
no unsupported nested effectful expression is silently accepted. -/
import ScopedIO.WorldSourceWith

namespace ScopedIO.TextExpressions
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def arguments (cfg : Layout) (pureCall : Machine.Call) (fuel : Nat) :
    List Expr → World → Option (List Value × World)
  | [],w => some ([],w)
  | e::es,w => do
      let (v,t) ← evalExpr cfg pureCall fuel w.app e
      let (vs,last) ← arguments cfg pureCall fuel es ⟨t,w.stream⟩
      return (v::vs,last)

theorem arguments_sound {cfg : Layout} {pureCall : Machine.Call} {fuel : Nat}
    (world : WorldIO.Call) (p : WorldIO.Platform) {es : List Expr}
    {s t : World} {vs : List Value} (h : arguments cfg pureCall fuel es s = some (vs,t)) :
    WorldSource.Arguments cfg pureCall world p es s t vs := by
  induction es generalizing s t vs with
  | nil =>
    simp only [arguments,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    exact WorldSource.Arguments.nil s
  | cons e es ih =>
    cases he : evalExpr cfg pureCall fuel s.app e with
    | none => simp [arguments,he] at h
    | some pair =>
      rcases pair with ⟨v,middle⟩
      cases hr : arguments cfg pureCall fuel es ⟨middle,s.stream⟩ with
      | none => simp [arguments,he,hr] at h
      | some pair =>
        rcases pair with ⟨rest,last⟩
        simp only [arguments,he,hr,Bind.bind,Option.bind,Pure.pure,
          Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact WorldSource.Arguments.cons (WorldSource.Eval.pure he) (ih hr)

def expression (cfg : Layout) (pureCall : Machine.Call) (world : WorldIO.Call)
    (fuel : Nat) (e : Expr) (w : World) : Option (Value × World) :=
  match e with
  | .call (.var name) es => do
      let (vs,middle) ← arguments cfg pureCall fuel es w
      world name vs middle
  | _ => do
      let (v,t) ← evalExpr cfg pureCall fuel w.app e
      return (v,⟨t,w.stream⟩)

theorem expression_sound {cfg : Layout} {pureCall : Machine.Call} {world : WorldIO.Call}
    {fuel : Nat} (p : WorldIO.Platform) {e : Expr} {s t : World} {v : Value}
    (h : expression cfg pureCall world fuel e s = some (v,t)) :
    WorldSource.Eval cfg pureCall world p e s t v := by
  unfold expression at h
  split at h
  next name es =>
    cases ha : arguments cfg pureCall fuel es s with
    | none => simp [ha] at h
    | some pair =>
      rcases pair with ⟨vs,middle⟩
      simp only [ha,Bind.bind,Option.bind] at h
      exact WorldSource.Eval.call (arguments_sound world p ha) h
  next other =>
    cases hp : evalExpr cfg pureCall fuel s.app e with
    | none => simp [hp] at h
    | some pair =>
      rcases pair with ⟨value,after⟩
      simp only [hp,Bind.bind,Option.bind,Pure.pure,
        Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      exact WorldSource.Eval.pure hp

end ScopedIO.TextExpressions

/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import DensityCachedSum
namespace WinnerMemoSum
open LeanCert.Core LeanCert.Engine LeanCert.Internal.Dyadic
set_option maxHeartbeats 0
set_option maxRecDepth 100000
abbrev Result := IntervalDyadic × Bool
abbrev Cache := List (Expr × Result)
def lookup : Cache→Expr→Option Result
  | [], _ => none
  | (key,r)::rest, e => if key=e then some r else lookup rest e

def Coherent (cache : Cache) (ρ : IntervalDyadicEnv) (ctx : PreparedContext) : Prop :=
  ∀ e r, (e,r) ∈ cache → r=evalPreparedCached e ρ ctx

theorem lookup_correct {cache : Cache} {ρ : IntervalDyadicEnv} {ctx : PreparedContext}
    (hc : Coherent cache ρ ctx) {e : Expr} {r : Result} (he : lookup cache e=some r) :
    r=evalPreparedCached e ρ ctx := by
  induction cache with
  |nil=>simp [lookup] at he
  |cons p rest ih=>
    rcases p with ⟨key,q⟩
    simp only [lookup] at he
    split_ifs at he with h
    · subst key
      simp only [Option.some.injEq] at he
      subst q
      exact hc e r (by simp)
    · exact ih (fun e r hr=>hc e r (by simp [hr])) he

def memoEval (e : Expr) (ρ : IntervalDyadicEnv)
    (ctx : PreparedContext) (cache : Cache) : Result :=
  match lookup cache e with
  | some r => r
  | none => match e with
    | .const q =>
        (IntervalDyadic.ofIntervalRat (IntervalRat.singleton q) ctx.cfg.precision, true)
    | .var idx => (ρ idx, true)
    | .add e₁ e₂ =>
        let r₁ := memoEval e₁ ρ ctx cache
        let r₂ := memoEval e₂ ρ ctx cache
        ((IntervalDyadic.add r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
    | .mul e₁ e₂ =>
        let r₁ := memoEval e₁ ρ ctx cache
        let r₂ := memoEval e₂ ρ ctx cache
        ((IntervalDyadic.mul r₁.1 r₂.1).roundOut ctx.cfg.precision, r₁.2 && r₂.2)
    | .neg e =>
        let r := memoEval e ρ ctx cache
        (IntervalDyadic.neg r.1, r.2)
    | .inv e =>
        let r := memoEval e ρ ctx cache
        let I := r.1.toIntervalRat
        (invIntervalDyadic r.1 ctx.cfg, r.2 && (decide (I.lo > 0) || decide (I.hi < 0)))
    | .exp e =>
        let r := memoEval e ρ ctx cache
        (expIntervalPrepared r.1 ctx, r.2)
    | .sin e =>
        let r := memoEval e ρ ctx cache
        (sinIntervalPrepared r.1 ctx, r.2)
    | .cos e =>
        let r := memoEval e ρ ctx cache
        (cosIntervalPrepared r.1 ctx, r.2)
    | .log e =>
        let r := memoEval e ρ ctx cache
        (logIntervalPrepared r.1 ctx, r.2 && decide (r.1.toIntervalRat.lo > 0))
    | .atan e =>
        let r := memoEval e ρ ctx cache
        (atanIntervalDyadic r.1 ctx.cfg, r.2)
    | .arsinh e =>
        let r := memoEval e ρ ctx cache
        (arsinhIntervalDyadic r.1 ctx.cfg, r.2)
    | .atanh e =>
        let r := memoEval e ρ ctx cache
        let I := r.1.toIntervalRat
        (atanhIntervalPrepared r.1 ctx,
          r.2 && decide (I.lo > -1) && decide (I.hi < 1))
    | .sinc e =>
        let r := memoEval e ρ ctx cache
        (sincIntervalDyadic r.1 ctx.cfg, r.2)
    | .erf e =>
        let r := memoEval e ρ ctx cache
        (erfIntervalDyadic r.1 ctx.cfg, r.2)
    | .sinh e =>
        let r := memoEval e ρ ctx cache
        (sinhIntervalDyadic r.1 ctx.cfg, r.2)
    | .cosh e =>
        let r := memoEval e ρ ctx cache
        (coshIntervalDyadic r.1 ctx.cfg, r.2)
    | .tanh e =>
        let r := memoEval e ρ ctx cache
        (tanhIntervalDyadic r.1 ctx.cfg, r.2)
    | .sqrt e =>
        let r := memoEval e ρ ctx cache
        (sqrtIntervalDyadic r.1 ctx.cfg, r.2)
    | .namedConst c =>
        (IntervalDyadic.ofIntervalRat c.interval ctx.cfg.precision, true)

theorem memoEval_eq {e : Expr} {ρ : IntervalDyadicEnv} {ctx : PreparedContext} {cache : Cache}
    (hc : Coherent cache ρ ctx) : memoEval e ρ ctx cache=evalPreparedCached e ρ ctx := by
  induction e
  all_goals
    rw [memoEval]
    split
    · rename_i r he
      exact lookup_correct hc he
    · simp_all only [evalPreparedCached]

def preload : List Expr→IntervalDyadicEnv→PreparedContext→Cache→Cache
  | [], _, _, cache => cache
  | e::rest, ρ, ctx, cache => preload rest ρ ctx ((e,memoEval e ρ ctx cache)::cache)

theorem preload_coherent (keys : List Expr) {ρ : IntervalDyadicEnv} {ctx : PreparedContext}
    {cache : Cache} (hc : Coherent cache ρ ctx) : Coherent (preload keys ρ ctx cache) ρ ctx := by
  induction keys generalizing cache with
  |nil=>exact hc
  |cons e rest ih=>
    apply ih
    intro f r hr
    rcases List.mem_cons.mp hr with he|he
    · have he':f=e ∧ r=memoEval e ρ ctx cache := Prod.mk.inj he
      rcases he' with ⟨rfl,rfl⟩
      exact memoEval_eq hc
    · exact hc f r he

theorem memo_preload_eq (e : Expr) (keys : List Expr) (ρ : IntervalDyadicEnv) (ctx : PreparedContext) :
    memoEval e ρ ctx (preload keys ρ ctx [])=evalPreparedCached e ρ ctx := by
  apply memoEval_eq
  exact preload_coherent keys (by simp [Coherent])

def memoSumAux (body : Expr) (keys : List Expr) (current limit : ℕ) (acc : IntervalDyadic)
    (ctx : PreparedContext) : Result :=
  if current>limit then (acc,true)
  else
    let env:=sumBodyEnvSimple current ctx.cfg.precision
    let term:=memoEval body env ctx (preload keys env ctx [])
    let next:=(IntervalDyadic.add acc term.1).roundOut ctx.cfg.precision
    let rest:=memoSumAux body keys (current+1) limit next ctx
    (rest.1,term.2 && rest.2)
  termination_by limit+1-current

theorem memoSumAux_eq (body : Expr) (keys : List Expr) (current limit : ℕ) (acc : IntervalDyadic)
    (ctx : PreparedContext) : memoSumAux body keys current limit acc ctx=
      CH2QRH.DensityComputation.checkedSumAux body current limit acc ctx := by
  generalize hm : limit+1-current=m
  induction m using Nat.strongRecOn generalizing current acc with
  |ind m ih=>
    rw [memoSumAux,CH2QRH.DensityComputation.checkedSumAux]
    split_ifs with h
    · rfl
    · simp only [memo_preload_eq]
      rw [ih (limit+1-(current+1)) (by omega) (current+1) _ rfl]

def memoCheck (body : Expr) (keys : List Expr) (a b : ℕ) (target : ℚ) (cfg : DyadicConfig) : Bool :=
  let result:=memoSumAux body keys a b finSumZero (prepareContext cfg)
  result.2 && result.1.upperBoundedBy target

theorem memoCheck_eq (body : Expr) (keys : List Expr) (a b : ℕ) (target : ℚ) (cfg : DyadicConfig) :
    memoCheck body keys a b target cfg=CH2QRH.DensityComputation.checkUpperBound body a b target cfg := by
  simp only [memoCheck,CH2QRH.DensityComputation.checkUpperBound,memoSumAux_eq]

#print axioms memoCheck_eq
#print axioms memo_preload_eq
end WinnerMemoSum

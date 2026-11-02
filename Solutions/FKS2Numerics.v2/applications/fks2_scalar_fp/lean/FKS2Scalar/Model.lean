import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Log
import Std.Tactic

/-! Selected normal-binary64 subset. Exact rational arithmetic is proof infrastructure only.
Every operation rounds by integer quotient/remainder, never host Float arithmetic. Nonzero
subnormal inputs/results and nonfinite results are rejected, rather than silently approximated.
Successful execution therefore constructs the required domain/safety checks. -/
namespace FKS2Scalar

def pow2 (e : Int) : Rat :=
  if e < 0 then 1 / (2 ^ (-e).toNat : Nat) else (2 ^ e.toNat : Nat)

def round64 (x : Rat) : Option Rat := Id.run do
  if x == 0 then return some 0
  let a := x.num.natAbs
  let b := x.den
  let guess := (a.log2 : Int) - (b.log2 : Int)
  let mag := if x < 0 then -x else x
  let e := if mag < pow2 guess then guess - 1 else guess
  if e < -1022 || e > 1023 then return none
  let unit := pow2 (e - 52)
  let scaled := mag / unit
  let whole := scaled.num.natAbs / scaled.den
  let remainder := scaled.num.natAbs % scaled.den
  let up := 2 * remainder > scaled.den ||
    (2 * remainder == scaled.den && whole % 2 == 1)
  let mantissa := whole + if up then 1 else 0
  if e == 1023 && mantissa == 2 ^ 53 then return none
  let result := (mantissa : Rat) * unit
  return some (if x < 0 then -result else result)

def decimal (s : String) : Option Rat := do
  let [a, b] := s.splitOn "." | none
  let n ← a.toNat?
  let m ← b.toNat?
  pure ((n : Rat) + (m : Rat) / (10 ^ b.length : Nat))

inductive Bin where
  | add | sub | mul | div
  deriving Repr, DecidableEq

inductive Expr where
  | lit (text : String)
  | var (name : String)
  | neg (a : Expr)
  | bin (op : Bin) (a b : Expr)
  | call (name : String) (arg : Expr)
  deriving Repr, DecidableEq

inductive Stmt where
  | localVar (name : String) (value : Expr)
  | assign (name : String) (value : Expr)
  | loop (name : String) (start bound : Expr) (inclusive : Bool) (body : List Stmt)
  | branch (left right : Expr) (body : List Stmt)
  | ret (value : Expr)
  deriving Repr

structure Function where
  name : String
  param : Option String
  body : List Stmt
  deriving Repr

abbrev Env := List (String × Rat)

def put (env : Env) (name : String) (value : Rat) : Env :=
  (name, value) :: env.filter (fun p => p.1 != name)

def get (env : Env) (name : String) : Option Rat :=
  (env.find? (fun p => p.1 == name)).map Prod.snd

structure Frame where
  env : Env
  result : Option Rat := none
  deriving Repr, DecidableEq

structure HelperEvent where
  name : String
  arg : Rat
  out : Rat
  deriving Repr, DecidableEq

abbrev Machine := StateT (List HelperEvent) Option

def liftOption (x : Option α) : Machine α := fun events =>
  x.map (fun value => (value, events))

mutual
def evalExpr (arithmetic : Rat → Option Rat) (program : List Function) : Nat → Env → Expr → Machine Rat
  | 0, _, _ => liftOption none
  | n + 1, env, expr => do
    match expr with
    | .lit text => liftOption (round64 (← decimal text))
    | .var name => liftOption (get env name)
    | .neg a => pure (-(← evalExpr arithmetic program n env a))
    | .bin op a b =>
      let x ← evalExpr arithmetic program n env a
      let y ← evalExpr arithmetic program n env b
      match op with
      | .add => liftOption (arithmetic (x + y))
      | .sub => liftOption (arithmetic (x - y))
      | .mul => liftOption (arithmetic (x * y))
      | .div => if y == 0 then liftOption none else liftOption (arithmetic (x / y))
    | .call name arg =>
      let x ← evalExpr arithmetic program n env arg
      let f ← liftOption (program.find? (fun f => f.name == name))
      let param ← liftOption f.param
      let final ← evalBlock arithmetic program n ⟨[(param, x)], none⟩ f.body
      let value ← liftOption final.result
      modify (fun events => ⟨name, x, value⟩ :: events)
      pure value

def evalBlock (arithmetic : Rat → Option Rat) (program : List Function) : Nat → Frame → List Stmt → Machine Frame
  | 0, _, _ => liftOption none
  | n + 1, state, body => do
    if state.result.isSome then return state
    match body with
    | [] => pure state
    | stmt :: rest =>
      let next ← evalStmt arithmetic program n state stmt
      evalBlock arithmetic program n next rest

def evalStmt (arithmetic : Rat → Option Rat) (program : List Function) : Nat → Frame → Stmt → Machine Frame
  | 0, _, _ => liftOption none
  | n + 1, state, stmt => do
    match stmt with
    | .localVar name value | .assign name value =>
      let x ← evalExpr arithmetic program n state.env value
      pure { state with env := put state.env name x }
    | .ret value =>
      let x ← evalExpr arithmetic program n state.env value
      pure { state with result := some x }
    | .branch a b body =>
      let x ← evalExpr arithmetic program n state.env a
      let y ← evalExpr arithmetic program n state.env b
      if x < y then evalBlock arithmetic program n state body else pure state
    | .loop name start bound inclusive body =>
      let x ← evalExpr arithmetic program n state.env start
      let y ← evalExpr arithmetic program n state.env bound
      evalLoop arithmetic program n { state with env := put state.env name x } name y inclusive body

def evalLoop (arithmetic : Rat → Option Rat) (program : List Function) : Nat → Frame → String → Rat → Bool →
    List Stmt → Machine Frame
  | 0, _, _, _, _, _ => liftOption none
  | n + 1, state, name, bound, inclusive, body => do
    if state.result.isSome then return state
    let x ← liftOption (get state.env name)
    if (if inclusive then x ≤ bound else x < bound) then
      let next ← evalBlock arithmetic program n state body
      if next.result.isSome then return next
      let old ← liftOption (get next.env name)
      let value ← liftOption (arithmetic (old + 1))
      evalLoop arithmetic program n { next with env := put next.env name value } name bound inclusive body
    else pure state
end

def executeObserved (arithmetic : Rat → Option Rat) (program : List Function) :
    Option (Rat × List HelperEvent) := do
  let f ← program.find? (fun f => f.name == "fks2_value")
  if f.param.isSome then none else do
    let (final, events) ← (evalBlock arithmetic program 1024 ⟨[], none⟩ f.body).run []
    let out ← final.result
    pure (out, events.reverse)

def executeWith (arithmetic : Rat → Option Rat) (program : List Function) : Option Rat :=
  (executeObserved arithmetic program).map Prod.fst

def execute (program : List Function) : Option Rat := executeWith round64 program

/-- Exact rational decoding, including subnormals, used to specify the returned bit pattern. -/
def decodeBits (bits : Nat) : Rat :=
  let sign : Rat := if bits / 2 ^ 63 % 2 == 0 then 1 else -1
  let exponent : Nat := bits / 2 ^ 52 % 2048
  let fraction : Nat := bits % 2 ^ 52
  if exponent == 0 then sign * (fraction : Rat) * pow2 (-1074)
  else sign * ((2 ^ 52 + fraction : Nat) : Rat) * pow2 ((exponent : Int) - 1075)

def finiteBits (bits : Nat) : Bool := bits < 2 ^ 64 && bits / 2 ^ 52 % 2048 < 2047

/-- Selected bounded source execution; failure includes a zero divisor, non-normal nonzero
operation result, overflow, missing variable/function, or exhausted structural fuel. -/
def ExecC (program : List Function) (out : Rat) : Prop := execute program = some out

end FKS2Scalar

import FKS2Scalar.Budget

namespace FKS2Scalar

def exprSupported (locals functions : List String) : Expr → Bool
  | .lit s => ((decimal s).bind round64).isSome
  | .var s => locals.contains s
  | .neg e => exprSupported locals functions e
  | .bin _ a b => exprSupported locals functions a && exprSupported locals functions b
  | .call f x => functions.contains f && exprSupported locals functions x

/-- Lexical support check for the exact selected subset. Block locals never escape;
no addresses/aliasing, shadowing, forward calls, recursion, or uninitialized reads. -/
def blockSupported (functions : List String) (locals : List String) : List Stmt → Bool
  | [] => true
  | .localVar name value :: rest => !locals.contains name &&
      exprSupported locals functions value && blockSupported functions (name :: locals) rest
  | .assign name value :: rest => locals.contains name &&
      exprSupported locals functions value && blockSupported functions locals rest
  | .ret value :: rest => rest.isEmpty && exprSupported locals functions value
  | .branch a b body :: rest => exprSupported locals functions a &&
      exprSupported locals functions b && blockSupported functions locals body &&
      blockSupported functions locals rest
  | .loop name start bound _ body :: rest => !locals.contains name &&
      exprSupported locals functions start && exprSupported (name :: locals) functions bound &&
      blockSupported functions (name :: locals) body && blockSupported functions locals rest

def programSupported : List String → List Function → Bool
  | _, [] => true
  | previous, f :: rest => !previous.contains f.name &&
      blockSupported previous f.param.toList f.body && programSupported (f.name :: previous) rest

def encodePositiveNormal (x : Rat) : Option Nat := do
  if x ≤ 0 then none else do
    let guess := (x.num.natAbs.log2 : Int) - (x.den.log2 : Int)
    let e := if x < pow2 guess then guess - 1 else guess
    let m := x / pow2 (e - 52)
    if e < -1022 || e > 1023 || m.den != 1 || m.num < 2 ^ 52 || m.num ≥ 2 ^ 53 then none
    else some ((e + 1023).toNat * 2 ^ 52 + m.num.toNat - 2 ^ 52)

def executeBits : Option Nat := (execute selectedAST).bind encodePositiveNormal

theorem lexical_support_checked : programSupported [] selectedAST = true := by
  native_decide

theorem fixed_bits : executeBits = some outputBits := by
  native_decide

theorem q_exact : q = 5986159799604107 / 9444732965739290427392 := by
  native_decide

/-- Actual source arithmetic and approximation use one AST. No independent numerical clone
or assumed source-output agreement occurs in this forward-error bridge. -/
theorem source_refines_fp {out : Rat} (h : ExecC selectedAST out) :
    executeWith round64 selectedAST = some out := h

theorem consumed_result :
    sourceChecked = true ∧ programSupported [] selectedAST = true ∧
    executeBits = some outputBits ∧ ExecC selectedAST q ∧ finiteBits outputBits = true ∧
    executeWith some selectedAST = some idealQ ∧
    |constantTarget - exactTarget| ≤ (E_constants : ℝ) ∧
    |(idealQ : ℝ) - constantTarget| ≤ (E_approximation : ℝ) ∧
    |q - idealQ| ≤ E_roundoff ∧
    |(q : ℝ) - FKS2Numerics.v1.nuAsympE30| ≤ (E : ℝ) ∧
    (0 : Rat) ≤ E ∧ E ≤ 1 / 10 ^ 12 ∧ q + E ≤ Bpoc := by
  have hexec : ExecC selectedAST q := source_refines_fp fixed_execution
  exact ⟨source_checked, lexical_support_checked, fixed_bits, hexec, output_finite,
    ideal_execution, constants_error, approximation_error, roundoff_certificate,
    budget_forward_error, rational_certificate.2.2.1,
    rational_certificate.2.2.2.1, rational_certificate.2.2.2.2.1⟩

end FKS2Scalar

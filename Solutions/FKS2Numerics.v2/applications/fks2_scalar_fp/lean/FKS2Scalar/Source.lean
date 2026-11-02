import FKS2Scalar.Model
import Lean.Elab.Tactic.Decide

namespace FKS2Scalar

private def l := Expr.lit
private def v := Expr.var
private def call := Expr.call
local infixl:65 " +ₑ " => Expr.bin Bin.add
local infixl:65 " -ₑ " => Expr.bin Bin.sub
local infixl:70 " *ₑ " => Expr.bin Bin.mul
local infixl:70 " /ₑ " => Expr.bin Bin.div

/-- Hand transcription of the directly authored source, checked below at token granularity. -/
def expFunction : Function := ⟨"exp_small", some "x", [
  .localVar "y" (v "x" /ₑ l "32.0"),
  .localVar "term" (l "1.0"),
  .localVar "sum" (l "1.0"),
  .loop "n" (l "1.0") (l "18.0") true [
    .assign "term" ((v "term" *ₑ v "y") /ₑ v "n"),
    .assign "sum" (v "sum" +ₑ v "term")],
  .loop "n" (l "0.0") (l "5.0") false [
    .assign "sum" (v "sum" *ₑ v "sum")],
  .ret (v "sum")]⟩

def sqrtFunction : Function := ⟨"sqrt_fixed", some "x", [
  .localVar "y" (l "3.0"),
  .loop "n" (l "0.0") (l "5.0") false [
    .assign "y" (l "0.5" *ₑ (v "y" +ₑ (v "x" /ₑ v "y")))],
  .ret (v "y")]⟩

def mainFunction : Function := ⟨"fks2_value", none, [
  .localVar "r" (l "5.5666305"),
  .localVar "a1" (l "1.0" +ₑ l "0.0000000193378"),
  .localVar "log2" (l "0.6931471805599453"),
  .localVar "s1" (l "0.0"),
  .localVar "s2" (l "0.0"),
  .loop "k" (l "3.0") (l "43.0") true [
    .localVar "t" (l "30.0" *ₑ ((l "1.0" /ₑ v "k") -ₑ (l "1.0" /ₑ l "3.0"))),
    .assign "s1" (v "s1" +ₑ call "exp_small" (v "t"))],
  .loop "k" (l "3.0") (l "44.0") true [
    .localVar "t" ((l "44.0" *ₑ v "log2") *ₑ
      ((l "1.0" /ₑ v "k") -ₑ (l "1.0" /ₑ l "3.0"))),
    .assign "s2" (v "s2" +ₑ call "exp_small" (v "t"))],
  .localVar "a2" (v "s1"),
  .branch (v "s1") (v "s2") [.assign "a2" (v "s2")],
  .assign "a2" (v "a1" *ₑ v "a2"),
  .localVar "u" (v "r" /ₑ l "30.0"),
  .localVar "z" (call "sqrt_fixed" (l "30.0" /ₑ v "r")),
  .localVar "p" (((l "1.0" /ₑ l "121.096") *ₑ v "u") /ₑ v "z"),
  .assign "p" (v "p" *ₑ call "exp_small" (l "2.0" *ₑ v "z")),
  .localVar "b1" ((v "a1" *ₑ l "30.0") *ₑ call "exp_small" (.neg (l "15.0"))),
  .localVar "b2" ((v "a2" *ₑ l "30.0") *ₑ call "exp_small" (.neg (l "20.0"))),
  .ret (v "p" *ₑ (v "b1" +ₑ v "b2"))]⟩

def selectedAST : List Function := [expFunction, sqrtFunction, mainFunction]

/-- Serialization of only the selected constructors, used to compare tokens with hand-written
source. It does not generate the C workload and is not a proved ISO C frontend. -/
def exprTokens : Expr → String
  | .lit t | .var t => t
  | .neg a => "(-" ++ exprTokens a ++ ")"
  | .bin op a b => "(" ++ exprTokens a ++
      (match op with | .add => " + " | .sub => " - " | .mul => " * " | .div => " / ") ++
      exprTokens b ++ ")"
  | .call name arg => name ++ "(" ++ exprTokens arg ++ ")"

def stmtTokens : Stmt → String
  | .localVar name value => "double " ++ name ++ " = " ++ exprTokens value ++ ";"
  | .assign name value => name ++ " = " ++ exprTokens value ++ ";"
  | .ret value => "return " ++ exprTokens value ++ ";"
  | .branch a b body => "if (" ++ exprTokens a ++ " < " ++ exprTokens b ++ ") {" ++
      String.join (body.map stmtTokens) ++ "}"
  | .loop name start bound inclusive body =>
      "for (double " ++ name ++ " = " ++ exprTokens start ++ "; " ++ name ++
      (if inclusive then " <= " else " < ") ++ exprTokens bound ++ "; " ++ name ++
      " = (" ++ name ++ " + 1.0)) {" ++ String.join (body.map stmtTokens) ++ "}"

def functionTokens (f : Function) : String :=
  (if f.param.isSome then "static " else "") ++ "double " ++ f.name ++ "(" ++
  (match f.param with | none => "void" | some p => "double " ++ p) ++ ") {" ++
  String.join (f.body.map stmtTokens) ++ "}"

/-- No comments, directives, strings, character literals, or unsupported symbols are accepted.
Words and decimal tokens retain their boundaries; <= is recognized as one token. -/
def scanTokens : Nat → List Char → Option (List String)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: cs => do
    if c.isWhitespace then scanTokens n cs
    else if c.isAlphanum || c == '_' || c == '.' then
      let word := (c :: cs).takeWhile (fun x => x.isAlphanum || x == '_' || x == '.')
      let tail ← scanTokens n ((c :: cs).drop word.length)
      pure (String.ofList word :: tail)
    else if c == '<' && cs.head? == some '=' then
      pure ("<=" :: (← scanTokens n (cs.drop 1)))
    else if ['(', ')', '{', '}', ';', '=', '+', '-', '*', '/', '<', ','].contains c then
      pure (String.singleton c :: (← scanTokens n cs))
    else none

def tokens (s : String) := scanTokens (s.length + 1) s.toList

/-- The file is embedded at elaboration; the build receipt separately hashes this same file. -/
def selectedSource : String := include_str ".."/".."/"fks2.c"

def sourceChecked : Bool :=
  let actual := tokens selectedSource
  actual.isSome && actual == tokens (String.join (selectedAST.map functionTokens))

def outputBits : Nat := 0x3ea54461706c938b
def q : Rat := decodeBits outputBits

-- Native checks concern finite tokens and exact integer/rational source execution only.
theorem source_checked : sourceChecked = true := by
  native_decide

theorem fixed_execution : ExecC selectedAST q := by
  unfold ExecC
  native_decide

theorem output_finite : finiteBits outputBits = true := by
  native_decide

end FKS2Scalar

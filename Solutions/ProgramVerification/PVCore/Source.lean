/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import SumStability.Source

/-!
# The selected restricted-C shape "sum, scale, then signed constants"

Three IEANTN numerical providers execute the same kind of C program: the frozen `sum` loop over a
static array, one multiplication by a scale literal, then a few additions or subtractions of
literals. Table 4 adds three constants after scaling; the Ramanujan budget subtracts two; the
calibration program A of the A→B pilot adds none. Until now each application restated this shape
(`FKS2Table4.TransportProgram`, `ForwardRamanujan.Program`, `CalibrationPilot.NamedProgram`) with
its own renderer and token check.

`Program` records the shape once: a function name, the array literals, the scale literal and the
list of signed literals. `render` prints the C text of the frozen `sum` function followed by this
wrapper, and `sourceMatches` compares the token stream of an actual file with it. Token equality
means the file is exactly this program up to whitespace; comments and preprocessor lines are
rejected by the scanner.

Small example: `⟨"f", ["0.5", "0.25"], "4.0", [(.minus, "1.0")]⟩` renders the wrapper
`static const double inputs[2] = {0.5,0.25}; double f(void) { double s = sum(inputs,2);
double r = (s * 4.0); r = (r - 1.0); return r; }`.
-/

namespace PVCore

/-- The sign of one constant applied after scaling. -/
inductive Sign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- The C operator printed for a sign. -/
def Sign.text : Sign → String
  | .plus => "+"
  | .minus => "-"

/-- The exact rational operation a sign denotes. -/
def Sign.apply : Sign → ℚ → ℚ → ℚ
  | .plus, r, c => r + c
  | .minus, r, c => r - c

/-- A selected program of the shape `s = sum(inputs, n); r = s * scale; r = r ± c₁; …; return r`.
There is no field for an expected output or an accuracy: those are theorems. -/
structure Program where
  fnName : String
  inputs : List String
  scale : String
  ops : List (Sign × String)
  deriving DecidableEq, Repr

/-- The C text of the frozen `sum` function followed by the wrapper for `p`. -/
def render (p : Program) : String :=
  (SumStability.render SumStability.selectedSumProgram).getD "" ++
  "static const double inputs[" ++ toString p.inputs.length ++ "] = {" ++
  String.intercalate "," p.inputs ++ "};" ++
  "double " ++ p.fnName ++ "(void) { double s = sum(inputs," ++ toString p.inputs.length ++
  "); double r = (s * " ++ p.scale ++ ");" ++
  String.join (p.ops.map fun o => "r = (r " ++ o.1.text ++ " " ++ o.2 ++ ");") ++
  "return r; }"

/-- The scanner of `SumStability.scan`, with the one extra symbol `-` that a subtraction needs.
Words, `++`, `+=` and the listed punctuation are tokens; anything else (comments, `#`, quotes)
makes the scan fail, so such a file never matches. -/
def scan : Nat → List Char → Option (List String)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: cs => do
    if c.isWhitespace then scan n cs
    else if c.isAlphanum || c == '_' || c == '.' then
      let word := (c :: cs).takeWhile (fun x => x.isAlphanum || x == '_' || x == '.')
      return String.ofList word :: (← scan n ((c :: cs).drop word.length))
    else if c == '+' && cs.head? == some '+' then
      return "++" :: (← scan n (cs.drop 1))
    else if c == '+' && cs.head? == some '=' then
      return "+=" :: (← scan n (cs.drop 1))
    else if ['(', ')', '{', '}', '[', ']', ';', '=', '+', '-', '*', '<', ','].contains c then
      return String.singleton c :: (← scan n cs)
    else none

/-- Token stream of a text, or `none` if the text contains anything the scanner rejects. -/
def tokens (s : String) : Option (List String) := scan (s.length + 1) s.toList

/-- The actual file `src` is the program `p`, token for token. -/
def sourceMatches (src : String) (p : Program) : Bool :=
  let ts := tokens src
  ts.isSome && ts == tokens (render p)

end PVCore

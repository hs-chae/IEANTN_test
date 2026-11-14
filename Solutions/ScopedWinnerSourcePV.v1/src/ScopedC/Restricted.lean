/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

namespace ScopedC.RestrictedC

/-- Reused restricted-C lexical correspondence, extended from the existing
LegacySumStability.Source scanner. This is not an unrestricted C frontend. -/
def skipBlock : Nat → List Char → Option (List Char)
  | 0, _ => none
  | _+1, [] => none
  | _+1, '*'::'/'::cs => some cs
  | k+1, _::cs => skipBlock k cs

def quoted (quote : Char) : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _+1, _, [] => none
  | k+1, acc, '\\'::c::cs => quoted quote k (c::'\\'::acc) cs
  | k+1, acc, c::cs =>
      if c=quote then some (String.ofList ((c::acc).reverse),cs)
      else quoted quote k (c::acc) cs

def wordChar (c : Char) : Bool := c.isAlphanum || c=='_'

def scan : Nat → List Char → Option (List String)
  | 0, _ => none
  | _+1, [] => some []
  | k+1, '/'::'/'::cs => scan k (cs.dropWhile (fun c=>c != '\n'))
  | k+1, '/'::'*'::cs => do
      let rest ← skipBlock (cs.length+1) cs
      scan k rest
  | k+1, c::cs => do
      if c.isWhitespace then scan k cs
      else if wordChar c then
        let word := (c::cs).takeWhile wordChar
        return String.ofList word :: (←scan k ((c::cs).drop word.length))
      else if c=='"' || c=='\'' then
        let (literal,rest) ← quoted c (cs.length+1) [c] cs
        return literal :: (←scan k rest)
      else if (c=='<' && cs.head?==some '<') || (c=='>' && cs.head?==some '>') then
        if cs[1]?==some '=' then
          return (String.ofList [c,c,'=']) :: (←scan k (cs.drop 2))
        else return (String.ofList [c,c]) :: (←scan k (cs.drop 1))
      else if ((c=='+' || c=='-' || c=='&' || c=='|') && cs.head?==some c) ||
          (['+','-','*','/','%','&','|','^','=','!','<','>'].contains c && cs.head?==some '=') ||
          (c=='-' && cs.head?==some '>') then
        match cs with
        | d::rest => return String.ofList [c,d] :: (←scan k rest)
        | [] => none
      else if ['(',')','{','}','[',']',';', '=', '+','-','*','/','<','>','!',
          '&','|','^','~','%',',',':','?','#','.'].contains c then
        return String.singleton c :: (←scan k cs)
      else none

def tokens (text : String) : Option (List String) := scan (text.length+1) text.toList

/-- A source binding must use a structured, application-owned typed AST and
renderer; ASTs carrying an opaque whole-source string do not supply semantics.
Kernel proofs check this predicate against `include_str` of the actual C file. -/
def SourceCorresponds {Program : Type} (render : Program → Option String)
    (text : String) (program : Program) : Prop :=
  ∃ printed, render program=some printed ∧ tokens text=tokens printed ∧
    (tokens text).isSome

theorem source_corresponds_of_exact {Program : Type} (render : Program → Option String)
    (text : String) (program : Program) (h : render program=some text)
    (valid : (tokens text).isSome) : SourceCorresponds render text program :=
  ⟨text,h,rfl,valid⟩

namespace Unsigned

def modulus (width : Nat) : Nat := 2^width
def repr (width value : Nat) : Nat := value % modulus width
def add (width a b : Nat) : Nat := repr width (a+b)
def mul (width a b : Nat) : Nat := repr width (a*b)
def sub (width a b : Nat) : Nat := repr width (a+modulus width-b)
def div (a b : Nat) : Option Nat := if b=0 then none else some (a/b)
def rem (a b : Nat) : Option Nat := if b=0 then none else some (a%b)

theorem repr_exact {width value : Nat} (h : value < modulus width) :
    repr width value=value := Nat.mod_eq_of_lt h
theorem add_exact {width a b : Nat} (h : a+b < modulus width) :
    add width a b=a+b := repr_exact h
theorem mul_exact {width a b : Nat} (h : a*b < modulus width) :
    mul width a b=a*b := repr_exact h
theorem sub_exact {width a b : Nat} (hab : b≤a) (ha : a < modulus width) :
    sub width a b=a-b := by
  unfold sub repr
  rw [show a+modulus width-b=(a-b)+modulus width by omega]
  simpa using Nat.mod_eq_of_lt (show a-b < modulus width by omega)
theorem div_exact {a b : Nat} (hb : b≠0) : div a b=some (a/b) := by
  simp [div,hb]
theorem rem_exact {a b : Nat} (hb : b≠0) : rem a b=some (a%b) := by
  simp [rem,hb]

end Unsigned

set_option maxRecDepth 10000 in
theorem scanner_smoke : tokens "/*x*/ unsigned _BitInt(256) x; // y\n x += 1;" =
    some ["unsigned","_BitInt","(","256",")","x",";","x","+=","1",";"] := by
  decide +kernel

#print axioms source_corresponds_of_exact
#print axioms Unsigned.sub_exact
#print axioms scanner_smoke
end ScopedC.RestrictedC

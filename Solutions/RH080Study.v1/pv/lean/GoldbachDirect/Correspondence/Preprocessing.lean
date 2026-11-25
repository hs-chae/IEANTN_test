import Mathlib.Data.List.Basic
import Mathlib.Tactic.Basic

/-! A deliberately restricted preprocessing syntax for the actual source files. The grammar
uses physical characters, not tokenizer output. Header spellings are exact, including every
character inside angle brackets or quotation marks. This does not interpret header contents,
expand macros, or assert equivalence to the whole C++ preprocessing language.
This physical/hash-directive profile composes with the identifier grammar: that grammar
excludes contextual module/import and preprocessing-operator names. An ordinary hash-free
line alone is not a complete C++ preprocessing judgment. -/
namespace GoldbachDirect.Correspondence

inductive AsciiPadding : Char → Prop
  | space : AsciiPadding ' '
  | tab : AsciiPadding '\t'
  | carriageReturn : AsciiPadding '\r'
  | verticalTab : AsciiPadding '\x0b'
  | formFeed : AsciiPadding '\x0c'

/-- Only boundary whitespace is discarded; whitespace inside a header name is retained. -/
inductive Padded (core : List Char) : List Char → Prop
  | bare : Padded core core
  | left {c chars} : AsciiPadding c → Padded core chars → Padded core (c :: chars)
  | right {c chars} : AsciiPadding c → Padded core chars → Padded core (chars ++ [c])

inductive SystemHeader : List Char → Prop
  | cudaRuntime : SystemHeader "cuda_runtime.h".toList
  | stdint : SystemHeader "stdint.h".toList
  | stddef : SystemHeader "stddef.h".toList
  | stdbool : SystemHeader "stdbool.h".toList
  | stdlib : SystemHeader "stdlib.h".toList
  | stdio : SystemHeader "stdio.h".toList

inductive LocalHeader : List Char → Prop
  | primes : LocalHeader "primes.h".toList
  | kernels : LocalHeader "kernels.cuh".toList

inductive DirectiveHeader : List Char → Prop
  | pragmaOnce : DirectiveHeader "#pragma once".toList
  | system {name} : SystemHeader name →
      DirectiveHeader ("#include <".toList ++ name ++ ['>'])
  | local {name} : LocalHeader name →
      DirectiveHeader ("#include \"".toList ++ name ++ ['"'])

/-- Raw hash characters occur only on complete canonical directive lines. In particular,
ordinary lines cannot hide extra directives behind the token-level comment/whitespace rules. -/
inductive PreprocessingLine : List Char → Prop
  | ordinary {chars} : '#' ∉ chars → PreprocessingLine chars
  | directive {core chars} : DirectiveHeader core → Padded core chars →
      PreprocessingLine chars

/-- Physical LF separation, preserving empty lines and the final line. -/
inductive PhysicalLines : List Char → List (List Char) → Prop
  | endOfInput : PhysicalLines [] [[]]
  | newline {chars lines} : PhysicalLines chars lines → PhysicalLines ('\n' :: chars) ([] :: lines)
  | character {c chars line lines} : c ≠ '\n' → PhysicalLines chars (line :: lines) →
      PhysicalLines (c :: chars) ((c :: line) :: lines)

/-- Excludes line splicing, all trigraph introducers and all C++ digraph punctuators.
Rejecting these pairs even in comments or quoted strings is intentional conservatism. -/
def SafeAdjacent (a b : Char) : Prop :=
  (a ≠ '\\' ∨ b ≠ '\n') ∧ (a ≠ '\\' ∨ b ≠ '\r') ∧
  (a ≠ '?' ∨ b ≠ '?') ∧ (a ≠ '<' ∨ b ≠ ':') ∧ (a ≠ ':' ∨ b ≠ '>') ∧
  (a ≠ '<' ∨ b ≠ '%') ∧ (a ≠ '%' ∨ b ≠ '>') ∧ (a ≠ '%' ∨ b ≠ ':')

/-- Printable ASCII, TAB, or LF only. Other raw controls (including CR, VT, FF, NUL,
and DEL) are outside this source-encoding profile; printable escape spellings remain allowed. -/
def SourceBasicChar (c : Char) : Prop :=
  (32 ≤ c.toNat ∧ c.toNat ≤ 126) ∨ c = '\t' ∨ c = '\n'

/-- The fragment uses basic ASCII with LF line endings. It has no alternative preprocessing
punctuators, backslash/newline splice, or final backslash. Raw-control rejection avoids
phase-1 normalization and constrained line-comment control-character interpretations. -/
inductive SourceFragment : List Char → Prop
  | empty : SourceFragment []
  | final {c} : SourceBasicChar c → c ≠ '\\' → SourceFragment [c]
  | next {a b chars} : SourceBasicChar a → SafeAdjacent a b → SourceFragment (b :: chars) →
      SourceFragment (a :: b :: chars)

inductive SourcePreprocessingSyntax : String → Prop
  | intro {source lines} : SourceFragment source.toList → PhysicalLines source.toList lines →
      (∀ line ∈ lines, PreprocessingLine line) → SourcePreprocessingSyntax source

def asciiPaddingAccepted (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\r' || c = '\x0b' || c = '\x0c'

def trimDirective (chars : List Char) : List Char :=
  ((chars.dropWhile asciiPaddingAccepted).reverse.dropWhile asciiPaddingAccepted).reverse

def directiveAccepted (chars : List Char) : Bool :=
  chars == "#pragma once".toList ||
  chars == "#include <cuda_runtime.h>".toList ||
  chars == "#include <stdint.h>".toList ||
  chars == "#include <stddef.h>".toList ||
  chars == "#include <stdbool.h>".toList ||
  chars == "#include <stdlib.h>".toList ||
  chars == "#include <stdio.h>".toList ||
  chars == "#include \"primes.h\"".toList ||
  chars == "#include \"kernels.cuh\"".toList

def preprocessingLineAccepted (chars : List Char) : Bool :=
  !chars.contains '#' || directiveAccepted (trimDirective chars)

def physicalLines : List Char → List (List Char)
  | [] => [[]]
  | c :: chars =>
      if c = '\n' then [] :: physicalLines chars
      else match physicalLines chars with
      | [] => [[c]]
      | line :: lines => (c :: line) :: lines

def adjacentAccepted (a b : Char) : Bool :=
  !(a = '\\' && b = '\n') && !(a = '\\' && b = '\r') &&
  !(a = '?' && b = '?') && !(a = '<' && b = ':') && !(a = ':' && b = '>') &&
  !(a = '<' && b = '%') && !(a = '%' && b = '>') && !(a = '%' && b = ':')

def sourceBasicCharAccepted (c : Char) : Bool :=
  (32 ≤ c.toNat && c.toNat ≤ 126) || c = '\t' || c = '\n'

def sourceFragmentAccepted : List Char → Bool
  | [] => true
  | [c] => sourceBasicCharAccepted c && c != '\\'
  | a :: b :: chars => sourceBasicCharAccepted a && adjacentAccepted a b &&
      sourceFragmentAccepted (b :: chars)

/-- A source-character guard. Exact directive spelling is checked before tokenization can
lose header-name whitespace; basic-ASCII/LF physical lines and forbidden pairs are checked. -/
def preprocessingAccepted (source : String) : Bool :=
  sourceFragmentAccepted source.toList &&
    (physicalLines source.toList).all preprocessingLineAccepted

private theorem asciiPaddingAccepted_sound {c : Char}
    (checked : asciiPaddingAccepted c = true) : AsciiPadding c := by
  simp only [asciiPaddingAccepted, Bool.or_eq_true, decide_eq_true_eq, or_assoc] at checked
  rcases checked with h | h | h | h | h <;> subst c
  · exact .space
  · exact .tab
  · exact .carriageReturn
  · exact .verticalTab
  · exact .formFeed

private theorem padded_trans {core middle chars : List Char}
    (inner : Padded core middle) (outer : Padded middle chars) : Padded core chars := by
  induction outer with
  | bare => exact inner
  | left h _ ih => exact .left h ih
  | right h _ ih => exact .right h ih

private theorem padded_reverse {core chars : List Char}
    (padding : Padded core chars) : Padded core.reverse chars.reverse := by
  induction padding with
  | bare => exact .bare
  | left h _ ih => simpa using (Padded.right h ih)
  | right h _ ih => simpa using (Padded.left h ih)

private theorem dropWhile_padded (chars : List Char) :
    Padded (chars.dropWhile asciiPaddingAccepted) chars := by
  induction chars with
  | nil => exact .bare
  | cons c cs ih =>
      cases h : asciiPaddingAccepted c with
      | false => simpa [h] using (Padded.bare : Padded (c :: cs) (c :: cs))
      | true => simpa [h] using (Padded.left (asciiPaddingAccepted_sound h) ih)

private theorem trimDirective_padded (chars : List Char) :
    Padded (trimDirective chars) chars := by
  have right := padded_reverse (dropWhile_padded (chars.dropWhile asciiPaddingAccepted).reverse)
  have both : Padded (trimDirective chars) (chars.dropWhile asciiPaddingAccepted) := by
    simpa only [trimDirective, List.reverse_reverse] using right
  exact padded_trans both (dropWhile_padded chars)

private theorem directiveAccepted_sound {chars : List Char}
    (checked : directiveAccepted chars = true) : DirectiveHeader chars := by
  simp only [directiveAccepted, Bool.or_eq_true, beq_iff_eq, or_assoc] at checked
  rcases checked with h | h | h | h | h | h | h | h | h <;> subst chars
  · exact .pragmaOnce
  · exact .system .cudaRuntime
  · exact .system .stdint
  · exact .system .stddef
  · exact .system .stdbool
  · exact .system .stdlib
  · exact .system .stdio
  · exact .local .primes
  · exact .local .kernels

private theorem preprocessingLineAccepted_sound {chars : List Char}
    (checked : preprocessingLineAccepted chars = true) : PreprocessingLine chars := by
  simp only [preprocessingLineAccepted, Bool.or_eq_true] at checked
  rcases checked with ordinary | directive
  · exact .ordinary (by simpa using ordinary)
  · exact .directive (directiveAccepted_sound directive) (trimDirective_padded chars)

private theorem physicalLines_nonempty (chars : List Char) : physicalLines chars ≠ [] := by
  induction chars with
  | nil => simp [physicalLines]
  | cons c cs ih =>
      simp only [physicalLines]
      split
      · simp
      · cases h : physicalLines cs with
        | nil => simp
        | cons line lines => simp

private theorem physicalLines_sound (chars : List Char) :
    PhysicalLines chars (physicalLines chars) := by
  induction chars with
  | nil => exact .endOfInput
  | cons c cs ih =>
      by_cases newline : c = '\n'
      · subst c
        simpa only [physicalLines, ite_true] using PhysicalLines.newline ih
      · cases h : physicalLines cs with
        | nil => exact False.elim (physicalLines_nonempty cs h)
        | cons line lines =>
            simp only [physicalLines, newline, ite_false, h]
            exact .character newline (by simpa only [h] using ih)

private theorem adjacentAccepted_sound {a b : Char}
    (checked : adjacentAccepted a b = true) : SafeAdjacent a b := by
  simpa [adjacentAccepted, SafeAdjacent, and_assoc] using checked

private theorem sourceBasicCharAccepted_sound {c : Char}
    (checked : sourceBasicCharAccepted c = true) : SourceBasicChar c := by
  simpa [sourceBasicCharAccepted, SourceBasicChar, or_assoc] using checked

private theorem sourceFragmentAccepted_sound {chars : List Char}
    (checked : sourceFragmentAccepted chars = true) : SourceFragment chars := by
  induction chars with
  | nil => exact .empty
  | cons a cs ih =>
      cases cs with
      | nil =>
          simp only [sourceFragmentAccepted, Bool.and_eq_true, bne_iff_ne] at checked
          exact .final (sourceBasicCharAccepted_sound checked.1) checked.2
      | cons b cs =>
          simp only [sourceFragmentAccepted, Bool.and_eq_true] at checked
          exact .next (sourceBasicCharAccepted_sound checked.1.1)
            (adjacentAccepted_sound checked.1.2) (ih checked.2)

/-- For every accepted string, raw characters have a physical-line derivation with exact
header names, printable-ASCII/TAB/LF encoding, no extra hash directives, no splices, and no
digraph/trigraph preprocessing. -/
theorem preprocessingAccepted_sound {source : String}
    (checked : preprocessingAccepted source = true) : SourcePreprocessingSyntax source := by
  simp only [preprocessingAccepted, Bool.and_eq_true] at checked
  obtain ⟨fragment, lines⟩ := checked
  apply SourcePreprocessingSyntax.intro (sourceFragmentAccepted_sound fragment)
    (physicalLines_sound source.toList)
  intro line member
  exact preprocessingLineAccepted_sound ((List.all_eq_true.mp lines) line member)

end GoldbachDirect.Correspondence

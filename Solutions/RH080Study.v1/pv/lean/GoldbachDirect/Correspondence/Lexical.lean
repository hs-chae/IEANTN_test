import Mathlib.Data.List.Basic

namespace GoldbachDirect.Lexical

/-- The checker's supported word characters. Decimal digits and letters may occur together;
this is a lexical word, whose identifier/numeral admissibility belongs to the grammar. -/
def wordChar (c : Char) : Bool := c.isAlphanum || c = '_'

/-- A maximal prefix satisfying a character predicate, specified without an executable scanner. -/
inductive Run (p : Char → Bool) : List Char → List Char → List Char → Prop
  | endOfInput : Run p [] [] []
  | stop {c cs} : p c = false → Run p (c :: cs) [] (c :: cs)
  | next {c cs word tail} : p c = true → Run p cs word tail →
      Run p (c :: cs) (c :: word) tail

/-- Characters up to and including the first unescaped matching quotation mark.
A backslash consumes the following character; a bare newline is forbidden. -/
inductive QuotedBody (quote : Char) : List Char → List Char → List Char → Prop
  | close {tail} : QuotedBody quote (quote :: tail) [quote] tail
  | escape {d cs body tail} : '\\' ≠ quote → QuotedBody quote cs body tail →
      QuotedBody quote ('\\' :: d :: cs) ('\\' :: d :: body) tail
  | ordinary {c cs body tail} : c ≠ quote → c ≠ '\\' → c ≠ '\n' →
      QuotedBody quote cs body tail → QuotedBody quote (c :: cs) (c :: body) tail

/-- A block comment ends at its first closing star/slash pair. -/
inductive BlockBody : List Char → List Char → Prop
  | close {tail} : BlockBody ('*' :: '/' :: tail) tail
  | next {c cs tail} : (∀ suffix, c :: cs ≠ '*' :: '/' :: suffix) →
      BlockBody cs tail → BlockBody (c :: cs) tail

def punctuation3 : List String := ["<<<", ">>>", "<<=", ">>="]

def punctuation2 : List String :=
  ["==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "->", "+=", "-=", "*=", "/=",
   "%=", "&=", "|=", "^=", "++", "--"]

def punctuation1 : List Char :=
  ['#', '(', ')', '[', ']', '{', '}', ';', ':', ',', '.', '?', '+', '-', '*', '/', '%',
   '<', '>', '=', '!', '~', '&', '|', '^']

/-- The longest supported punctuation at the current position. Negative prefix conditions
make the three-, two-, and one-character alternatives disjoint. -/
inductive Punctuation : List Char → String → List Char → Prop
  | three {chars} : String.ofList (chars.take 3) ∈ punctuation3 →
      Punctuation chars (String.ofList (chars.take 3)) (chars.drop 3)
  | two {chars} : String.ofList (chars.take 3) ∉ punctuation3 →
      String.ofList (chars.take 2) ∈ punctuation2 →
      Punctuation chars (String.ofList (chars.take 2)) (chars.drop 2)
  | one {c cs} : String.ofList ((c :: cs).take 3) ∉ punctuation3 →
      String.ofList ((c :: cs).take 2) ∉ punctuation2 → c ∈ punctuation1 →
      Punctuation (c :: cs) (String.singleton c) cs

/-- Independent character-level lexical derivations for the supported C++/CUDA subset.
The judgment contains no tokenizer, fuel, accumulator, AST printer or source equality test. -/
inductive Lexes : List Char → List String → Prop
  | done : Lexes [] []
  | whitespace {c cs ts} : c.isWhitespace = true → Lexes cs ts → Lexes (c :: cs) ts
  | lineComment {rest body tail ts} : Run (· != '\n') rest body tail →
      Lexes tail ts → Lexes ('/' :: '/' :: rest) ts
  | blockComment {rest tail ts} : BlockBody rest tail →
      Lexes tail ts → Lexes ('/' :: '*' :: rest) ts
  | quoted {quote rest body tail ts} : (quote = '"' ∨ quote = '\'') →
      QuotedBody quote rest body tail → Lexes tail ts →
      Lexes (quote :: rest) (String.ofList (quote :: body) :: ts)
  | word {c rest body tail ts} : wordChar c = true → Run wordChar rest body tail →
      Lexes tail ts → Lexes (c :: rest) (String.ofList (c :: body) :: ts)
  | punctuation {chars token tail ts} :
      (∀ rest, chars ≠ '/' :: '/' :: rest ∧ chars ≠ '/' :: '*' :: rest) →
      Punctuation chars token tail → Lexes tail ts → Lexes chars (token :: ts)

/-- A complete character-level lexical derivation for a source string. -/
def declarativeLex (source : String) (tokens : List String) : Prop :=
  Lexes source.toList tokens

end GoldbachDirect.Lexical

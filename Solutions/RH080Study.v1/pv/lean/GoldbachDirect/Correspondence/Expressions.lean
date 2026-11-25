import GoldbachDirect.SourceCheck

/-! An independently specified, precedence-indexed grammar for the expression
fragment. The grammar's constructors do not mention `Expr.tokens`. In particular,
postfix operations require a postfix expression, rather than an arbitrary prefix
expression. The executable guard below is stronger than the historical `atomic`
test. This file proves syntax correspondence only; typing, macro interpretation,
and evaluation are separate obligations. -/
namespace GoldbachDirect.Correspondence

def reservedWords : List String := ["alignas", "alignof", "and", "and_eq", "asm", "auto",
  "bitand", "bitor", "bool", "break", "case", "catch", "char", "char8_t", "char16_t",
  "char32_t", "class", "compl", "concept", "const", "consteval", "constexpr", "constinit",
  "const_cast", "continue", "co_await", "co_return", "co_yield", "decltype", "default",
  "delete", "do", "double", "dynamic_cast", "else", "enum", "explicit", "export", "extern",
  "false", "float", "for", "friend", "goto", "if", "inline", "int", "long", "mutable",
  "namespace", "new", "noexcept", "not", "not_eq", "nullptr", "operator", "or", "or_eq",
  "private", "protected", "public", "register", "reinterpret_cast", "requires", "return",
  "short", "signed", "sizeof", "static", "static_assert", "static_cast", "struct", "switch",
  "template", "this", "thread_local", "throw", "true", "try", "typedef", "typeid", "typename",
  "union", "unsigned", "using", "virtual", "void", "volatile", "wchar_t", "while", "xor",
  "xor_eq",
  -- These contextual directive/operator spellings are conservatively excluded;
  -- import/module are not unconditional C++ keywords.
  "import", "module", "_Pragma",
  -- These header-owned type names and CUDA qualifiers cannot be shadowed in
  -- the restricted grammar's fixed type-name environment.
  "uint8_t", "uint32_t", "uint64_t", "int32_t", "size_t", "cudaStream_t", "cudaError_t", "FILE",
  -- NULL has the dedicated nullMacro production, never a variable annotation.
  "NULL", "__host__", "__device__", "__global__"]

def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def syntaxIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: cs => (asciiLetter c || c == '_') &&
      cs.all (fun d => asciiLetter d || ('0' ≤ d && d ≤ '9') || d == '_') &&
      !(name ∈ reservedWords) && !(name.startsWith "__")

def quotedCharacter (c : Char) : Bool :=
  (' ' ≤ c && c ≤ '~') || c == '\n' || c == '\r' || c == '\t'

/-- Literal encoding specified directly by the accepted C++ escape productions. -/
def quoteEscape (c : Char) : String :=
  if c = '\n' then "\\n" else if c = '\r' then "\\r" else if c = '\t' then "\\t"
  else if c = '\\' then "\\\\" else if c = '"' then "\\\"" else String.singleton c

/-- Decimal digits decoded by place value, independently of every string printer.
Leading zeroes are excluded except for the single token `0`, so this cannot
silently interpret a C++ octal spelling as decimal. -/
def DecimalSpelling (digits : String) (value : Nat) : Prop :=
  digits.toList ≠ [] ∧
  digits.toList.all (fun c => '0' ≤ c && c ≤ '9') = true ∧
  (digits.toList.head? ≠ some '0' ∨ digits = "0") ∧
  digits.toList.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = value

instance (digits : String) (value : Nat) : Decidable (DecimalSpelling digits value) := by
  unfold DecimalSpelling
  infer_instance

def literalSyntaxSafe : Literal → Bool
  | .integer value suffix => decide (DecimalSpelling (toString value) value) &&
      suffix ∈ ["", "U", "u", "ULL", "ull", "UL", "ul"]
  | .string value => value.toList.all quotedCharacter
  | .character value => quotedCharacter value
  | _ => true

inductive LiteralSyntax : List String → Literal → Prop where
  | integer (digits : String) (n : Nat) (suffix : String) (decoded : DecimalSpelling digits n)
      (allowed : suffix ∈ ["", "U", "u", "ULL", "ull", "UL", "ul"]) :
      LiteralSyntax [digits ++ suffix] (.integer n suffix)
  | trueLiteral : LiteralSyntax ["true"] (.boolean true)
  | falseLiteral : LiteralSyntax ["false"] (.boolean false)
  | nullMacro : LiteralSyntax ["NULL"] .nullPointer
  | string (value : String) (safe : value.toList.all quotedCharacter = true) :
      LiteralSyntax ["\"" ++ String.join (value.toList.map quoteEscape) ++ "\""] (.string value)
  | character (value : Char) (safe : quotedCharacter value = true) :
      LiteralSyntax ["'" ++ (if value = '\'' then "\\'" else quoteEscape value) ++ "'"]
        (.character value)

inductive TypeSyntax : List String → CType → Prop where
  | void : TypeSyntax ["void"] .void
  | boolean : TypeSyntax ["bool"] .boolean
  | char : TypeSyntax ["char"] .char
  | u8 : TypeSyntax ["uint8_t"] .u8
  | u32 : TypeSyntax ["uint32_t"] .u32
  | u64 : TypeSyntax ["uint64_t"] .u64
  | i32 : TypeSyntax ["int32_t"] .i32
  | size : TypeSyntax ["size_t"] .size
  | int : TypeSyntax ["int"] .int
  | ull : TypeSyntax ["unsigned", "long", "long"] .ull
  | cudaStream : TypeSyntax ["cudaStream_t"] .cudaStream
  | cudaError : TypeSyntax ["cudaError_t"] .cudaError
  | file : TypeSyntax ["FILE"] .file
  | pointer : TypeSyntax ts t → TypeSyntax (ts ++ ["*"]) (.pointer t)
  | const : (match t with | .pointer _ | .const _ => false | _ => true) = true →
      TypeSyntax ts t → TypeSyntax ("const" :: ts) (.const t)

def typeSyntaxSafe : CType → Bool
  | .const (.pointer _) | .const (.const _) => false
  | .pointer t | .const t => typeSyntaxSafe t
  | _ => true

/-- Lower levels bind more tightly: primary, postfix, cast/unary, then the ten
binary precedence classes and the conditional expression. -/
def binaryLevel : Binary → Nat
  | .mul | .div | .mod => 3
  | .add | .sub => 4
  | .shl | .shr => 5
  | .lt | .le | .gt | .ge => 6
  | .eq | .ne => 7
  | .bitAnd => 8
  | .bitXor => 9
  | .bitOr => 10
  | .logicalAnd => 11
  | .logicalOr => 12

/-- The grammar names the operator spellings directly; no renderer map occurs
in these independent productions. -/
inductive UnaryOperatorSyntax : String → Unary → Prop where
  | logicalNot : UnaryOperatorSyntax "!" .logicalNot
  | bitNot : UnaryOperatorSyntax "~" .bitNot
  | negate : UnaryOperatorSyntax "-" .negate
  | address : UnaryOperatorSyntax "&" .address
  | dereference : UnaryOperatorSyntax "*" .dereference

inductive BinaryOperatorSyntax : String → Binary → Prop where
  | add : BinaryOperatorSyntax "+" .add
  | sub : BinaryOperatorSyntax "-" .sub
  | mul : BinaryOperatorSyntax "*" .mul
  | div : BinaryOperatorSyntax "/" .div
  | mod : BinaryOperatorSyntax "%" .mod
  | shl : BinaryOperatorSyntax "<<" .shl
  | shr : BinaryOperatorSyntax ">>" .shr
  | bitAnd : BinaryOperatorSyntax "&" .bitAnd
  | bitOr : BinaryOperatorSyntax "|" .bitOr
  | bitXor : BinaryOperatorSyntax "^" .bitXor
  | eq : BinaryOperatorSyntax "==" .eq
  | ne : BinaryOperatorSyntax "!=" .ne
  | lt : BinaryOperatorSyntax "<" .lt
  | le : BinaryOperatorSyntax "<=" .le
  | gt : BinaryOperatorSyntax ">" .gt
  | ge : BinaryOperatorSyntax ">=" .ge
  | logicalAnd : BinaryOperatorSyntax "&&" .logicalAnd
  | logicalOr : BinaryOperatorSyntax "||" .logicalOr

theorem unary_token_syntax (op : Unary) : UnaryOperatorSyntax op.token op := by
  cases op <;> constructor

theorem binary_token_syntax (op : Binary) : BinaryOperatorSyntax op.token op := by
  cases op <;> constructor

inductive ExpressionSyntax : Nat → List String → Expr → Prop where
  | literal : LiteralSyntax ts value → ExpressionSyntax 0 ts (.literal value)
  | variable (name : String) (valid : syntaxIdentifier name = true) :
      ExpressionSyntax 0 [name] (.variable name)
  | paren : ExpressionSyntax 13 ts e → ExpressionSyntax 0 ("(" :: ts ++ [")"]) (.paren e)
  | lift (h : i ≤ j) : ExpressionSyntax i ts e → ExpressionSyntax j ts e
  | cast : TypeSyntax typeTokens type → ExpressionSyntax 2 ts e →
      ExpressionSyntax 2 (["("] ++ typeTokens ++ [")"] ++ ts) (.cast type e)
  | unary : UnaryOperatorSyntax token op → ExpressionSyntax 2 ts e →
      ExpressionSyntax 2 (token :: ts) (.unary op e)
  | binary : BinaryOperatorSyntax token op → ExpressionSyntax (binaryLevel op) left a →
      ExpressionSyntax (binaryLevel op - 1) right b →
      ExpressionSyntax (binaryLevel op) (left ++ [token] ++ right) (.binary op a b)
  | index : ExpressionSyntax 1 base a → ExpressionSyntax 13 offset b →
      ExpressionSyntax 1 (base ++ ["["] ++ offset ++ ["]"]) (.index a b)
  | member : ExpressionSyntax 1 base a → syntaxIdentifier field = true →
      ExpressionSyntax 1 (base ++ [if arrow then "->" else ".", field]) (.member a field arrow)
  | call (name : String) (valid : syntaxIdentifier name = true)
      (tokenLists : List (List String)) (sameLength : tokenLists.length = args.length)
      (arguments : ∀ i : Fin args.length,
        ExpressionSyntax 13
          (tokenLists[i.val]'(by simpa only [sameLength] using i.isLt)) args[i.val]) :
      ExpressionSyntax 1
        ([name, "("] ++ List.flatten (tokenLists.intersperse [","]) ++ [")"]) (.call name args)
  | conditional : ExpressionSyntax 12 test a → ExpressionSyntax 13 yes b →
      ExpressionSyntax 13 no c →
      ExpressionSyntax 13 (test ++ ["?"] ++ yes ++ [":"] ++ no) (.conditional a b c)

/-- True exactly for AST outer forms that can occur before `[` or `.` without
parentheses. Prefix operators and C-style casts are deliberately excluded. -/
def postfixSafe : Expr → Bool
  | .literal _ | .variable _ | .paren _ | .index .. | .member .. | .call .. => true
  | _ => false

def exprSyntaxSafe : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .literal value => literalSyntaxSafe value
  | _ + 1, .variable name => syntaxIdentifier name
  | fuel + 1, .paren e => exprSyntaxSafe fuel e
  | fuel + 1, .cast type e => typeSyntaxSafe type && e.atomic && exprSyntaxSafe fuel e
  | fuel + 1, .unary _ e => e.atomic && exprSyntaxSafe fuel e
  | fuel + 1, .binary _ a b => a.atomic && b.atomic &&
      exprSyntaxSafe fuel a && exprSyntaxSafe fuel b
  | fuel + 1, .index a b => postfixSafe a && exprSyntaxSafe fuel a && exprSyntaxSafe fuel b
  | fuel + 1, .member a field _ =>
      postfixSafe a && syntaxIdentifier field && exprSyntaxSafe fuel a
  | fuel + 1, .call name args => syntaxIdentifier name && args.all (exprSyntaxSafe fuel)
  | fuel + 1, .conditional a b c => a.atomic && b.atomic && c.atomic &&
      exprSyntaxSafe fuel a && exprSyntaxSafe fuel b && exprSyntaxSafe fuel c

theorem type_tokens_syntax (type : CType) (safe : typeSyntaxSafe type = true) :
    TypeSyntax type.tokens type := by
  induction type with
  | pointer t ih => exact .pointer (ih safe)
  | const t ih =>
      cases t <;> try cases safe
      all_goals exact .const rfl (ih rfl)
  | _ => constructor

theorem literal_tokens_syntax (value : Literal) (safe : literalSyntaxSafe value = true) :
    LiteralSyntax value.tokens value := by
  cases value with
  | integer n suffix =>
      have checked : DecimalSpelling (toString n) n ∧
          suffix ∈ ["", "U", "u", "ULL", "ull", "UL", "ul"] := by
        simpa [literalSyntaxSafe] using safe
      exact .integer (toString n) n suffix checked.1 checked.2
  | boolean b => cases b <;> constructor
  | nullPointer => exact .nullMacro
  | string value =>
      convert LiteralSyntax.string value safe using 1
      rfl
  | character value =>
      convert LiteralSyntax.character value safe using 1
      rfl

theorem atomic_expression_syntax {e : Expr} {ts : List String} {level : Nat}
    (atomic : e.atomic = true) (parsed : ExpressionSyntax level ts e) :
    ExpressionSyntax 2 ts e := by
  induction parsed with
  | literal h => exact .lift (by decide) (.literal h)
  | «variable» name h => exact .lift (by decide) (.variable name h)
  | paren h _ => exact .lift (by decide) (.paren h)
  | lift _ _ ih => exact ih atomic
  | cast ht he _ => exact .cast ht he
  | unary hop he _ => exact .unary hop he
  | binary => simp [Expr.atomic] at atomic
  | index ha hb _ _ => exact .lift (by decide) (.index ha hb)
  | member ha hf _ => exact .lift (by decide) (.member ha hf)
  | call name hn chunks hlen args _ => exact .lift (by decide) (.call name hn chunks hlen args)
  | conditional => simp [Expr.atomic] at atomic

theorem postfix_expression_syntax {e : Expr} {ts : List String} {level : Nat}
    (hpost : postfixSafe e = true) (parsed : ExpressionSyntax level ts e) :
    ExpressionSyntax 1 ts e := by
  induction parsed with
  | literal h => exact .lift (by decide) (.literal h)
  | «variable» name h => exact .lift (by decide) (.variable name h)
  | paren h _ => exact .lift (by decide) (.paren h)
  | lift _ _ ih => exact ih hpost
  | cast => simp [postfixSafe] at hpost
  | unary => simp [postfixSafe] at hpost
  | binary => simp [postfixSafe] at hpost
  | index ha hb _ _ => exact .index ha hb
  | member ha hf _ => exact .member ha hf
  | call name hn chunks hlen args _ => exact .call name hn chunks hlen args
  | conditional => simp [postfixSafe] at hpost

theorem exprSyntaxSafe_sound {fuel : Nat} {e : Expr}
    (safe : exprSyntaxSafe fuel e = true) : ExpressionSyntax 13 e.tokens e := by
  induction fuel generalizing e with
  | zero => cases safe
  | succ fuel ih =>
      cases e <;> simp only [Expr.tokens]
      case literal value => exact .lift (by decide) (.literal (literal_tokens_syntax value safe))
      case «variable» name => exact .lift (by decide) (.variable name safe)
      case paren e => exact .lift (by decide) (.paren (ih safe))
      case cast type e =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          exact .lift (by decide) (.cast (type_tokens_syntax type safe.1.1)
            (atomic_expression_syntax safe.1.2 (ih safe.2)))
      case unary op e =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          exact .lift (by decide) (.unary (unary_token_syntax op)
            (atomic_expression_syntax safe.1 (ih safe.2)))
      case binary op a b =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          have ha := atomic_expression_syntax safe.1.1.1 (ih safe.1.2)
          have hb := atomic_expression_syntax safe.1.1.2 (ih safe.2)
          have lower : 2 ≤ binaryLevel op - 1 := by cases op <;> decide
          have upper : binaryLevel op ≤ 13 := by cases op <;> decide
          have left : 2 ≤ binaryLevel op := by cases op <;> decide
          exact .lift upper (.binary (binary_token_syntax op) (.lift left ha) (.lift lower hb))
      case index a b =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          exact .lift (by decide)
            (.index (postfix_expression_syntax safe.1.1 (ih safe.1.2)) (ih safe.2))
      case member a field arrow =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          exact .lift (by decide)
            (.member (postfix_expression_syntax safe.1.1 (ih safe.2)) safe.1.2)
      case call name args =>
          simp only [exprSyntaxSafe, Bool.and_eq_true, List.all_eq_true] at safe
          apply ExpressionSyntax.lift (by decide : 1 ≤ 13)
          apply ExpressionSyntax.call name safe.1 (args.map Expr.tokens) (by simp)
          intro i
          simpa only [List.getElem_map] using ih (safe.2 args[i.val] (List.getElem_mem i.isLt))
      case conditional a b c =>
          simp only [exprSyntaxSafe, Bool.and_eq_true] at safe
          have ha := atomic_expression_syntax safe.1.1.1.1.1 (ih safe.1.1.2)
          exact .conditional (.lift (by decide) ha) (ih safe.1.2) (ih safe.2)

/-- The old atomic/grouped checks admit two different ASTs for the same token
sequence. C++ postfix precedence chooses `parsedDereferenceIndex`. -/
def ambiguousDereferenceIndex : Expr :=
  .index (.unary .dereference (.variable "p")) (.variable "i")

def parsedDereferenceIndex : Expr :=
  .unary .dereference (.index (.variable "p") (.variable "i"))

theorem ambiguous_index_grouped : ambiguousDereferenceIndex.grouped = true := by decide

theorem ambiguous_index_same_tokens :
    ambiguousDereferenceIndex.tokens = parsedDereferenceIndex.tokens := by
  simp [ambiguousDereferenceIndex, parsedDereferenceIndex, Expr.tokens]

theorem ambiguous_index_rejected : exprSyntaxSafe 8 ambiguousDereferenceIndex = false := by decide

theorem ambiguous_index_parses_as_dereference :
    ExpressionSyntax 13 ambiguousDereferenceIndex.tokens parsedDereferenceIndex := by
  rw [ambiguous_index_same_tokens]
  exact exprSyntaxSafe_sound (fuel := 8) (by decide)

def minimumLevel : Expr → Nat
  | .literal _ | .variable _ | .paren _ => 0
  | .index .. | .member .. | .call .. => 1
  | .cast .. | .unary .. => 2
  | .binary op _ _ => binaryLevel op
  | .conditional .. => 13

theorem ExpressionSyntax.minimum_level {level : Nat} {tokens : List String} {e : Expr}
    (parsed : ExpressionSyntax level tokens e) : minimumLevel e ≤ level := by
  induction parsed with
  | lift h _ ih => exact Nat.le_trans ih h
  | _ => simp [minimumLevel]

def postfixBaseCompatible : Expr → Prop
  | .index base _ | .member base _ _ => minimumLevel base ≤ 1
  | _ => True

theorem ExpressionSyntax.postfix_base {level : Nat} {tokens : List String} {e : Expr}
    (parsed : ExpressionSyntax level tokens e) : postfixBaseCompatible e := by
  induction parsed with
  | lift _ _ ih => exact ih
  | index ha _ _ _ => exact ha.minimum_level
  | member ha _ _ => exact ha.minimum_level
  | _ => trivial

/-- Unlike a failure of the new executable guard alone, this proves that the
historically grouped AST has no derivation at all in the independent grammar. -/
theorem ambiguous_index_has_no_derivation (level : Nat) (tokens : List String) :
    ¬ ExpressionSyntax level tokens ambiguousDereferenceIndex := by
  intro parsed
  have impossible := parsed.postfix_base
  simp [ambiguousDereferenceIndex, postfixBaseCompatible, minimumLevel] at impossible

end GoldbachDirect.Correspondence

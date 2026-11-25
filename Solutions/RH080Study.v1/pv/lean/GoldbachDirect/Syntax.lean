import Mathlib.Data.List.Defs

/-! A proof-side restricted C/CUDA syntax. Authoritative native source is authored
separately. There is deliberately no arbitrary source-text statement constructor. -/
namespace GoldbachDirect

inductive CType where
  | void | boolean | char | u8 | u32 | u64 | i32 | size | int | ull | cudaStream | cudaError | file
  | pointer (element : CType)
  | const (element : CType)
  deriving Repr, DecidableEq

inductive Unary where
  | logicalNot | bitNot | negate | address | dereference
  deriving Repr, DecidableEq

inductive Binary where
  | add | sub | mul | div | mod | shl | shr | bitAnd | bitOr | bitXor
  | eq | ne | lt | le | gt | ge | logicalAnd | logicalOr
  deriving Repr, DecidableEq

inductive Literal where
  | integer (value : Nat) (suffix : String := "")
  | boolean (value : Bool)
  | nullPointer
  | string (value : String)
  | character (value : Char)
  deriving Repr, DecidableEq

inductive Expr where
  | literal (value : Literal)
  | paren (value : Expr)
  | variable (name : String)
  | cast (type : CType) (value : Expr)
  | unary (op : Unary) (value : Expr)
  | binary (op : Binary) (left right : Expr)
  | index (base offset : Expr)
  | member (base : Expr) (field : String) (arrow : Bool := false)
  | call (name : String) (arguments : List Expr)
  | conditional (test yes no : Expr)
  deriving Repr

inductive Stmt where
  | block (body : List Stmt)
  | declare (type : CType) (name : String) (initial : Option Expr)
  | assign (destination value : Expr)
  | assignOp (op : Binary) (destination value : Expr)
  | expression (value : Expr)
  | ite (condition : Expr) (yes : Stmt) (no : Option Stmt)
  | whileLoop (condition : Expr) (body : Stmt)
  | forLoop (initial : Stmt) (condition : Expr) (advance : Stmt) (body : Stmt)
  | returnValue (value : Option Expr)
  | breakLoop | continueLoop
  | label (name : String)
  | gotoLabel (name : String)
  | launch (name : String) (grid block shared stream : Expr) (arguments : List Expr)
  deriving Repr

inductive Qualifier where
  | static | inline | host | device | global
  deriving Repr

structure Function where
  qualifiers : List Qualifier := []
  emptyVoid : Bool := false
  result : CType
  name : String
  parameters : List (CType × String)
  body : Stmt
  deriving Repr

inductive Header where
  | stdint | stddef | stdbool | stdlib | stdio | inttypes | cudaRuntime | primes | kernels
  deriving Repr

inductive Top where
  | include (header : Header)
  | pragmaOnce
  | function (value : Function)
  deriving Repr

abbrev Program := List Top

end GoldbachDirect

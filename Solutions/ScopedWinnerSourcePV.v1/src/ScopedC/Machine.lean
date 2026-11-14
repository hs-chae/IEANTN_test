/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.Grammar
import ScopedC.Scalar
import ScopedC.NatArena

namespace ScopedC.Machine
open ScopedC.Syntax
set_option autoImplicit false
set_option maxHeartbeats 0

structure Layout where
  integers : List (String × Scalar.IntType)
  records : List (String × List (String × String))
  booleanType : Scalar.IntType := ⟨true,32⟩

structure Address where
  object : Nat
  index : Nat := 0
  fields : List String := []
  deriving Repr, DecidableEq

inductive Value where
  | integer (value : Scalar.Value)
  | natObject (slot : Nat)
  | record (type : String) (values : List Value)
  | aggregate (values : List Value)
  | pointer (address : Address) (writable : Bool)
  | null
  | uninitialized
  | unit
  deriving Repr

structure Object where
  type : String
  cells : List (Option Value)
  isArray : Bool := false
  writable : Bool := true
  deriving Repr

abbrev Env := List (String × Address)
structure State where
  heap : List Object
  env : Env
  globals : Env
  nats : NatArena.Arena

abbrev Call := String → List Value → State → Option (Value × State)

def empty : State := ⟨[],[],[],NatArena.empty⟩
def hasPrefix (lead text : String) : Bool := lead.toList.isPrefixOf text.toList
def stripPrefix (lead text : String) : String :=
  if hasPrefix lead text then String.ofList (text.toList.drop lead.length) else text
def normalizeType (t : String) : String := stripPrefix "const " (stripPrefix "static " t)
def isPointerType (t : String) : Bool := t.toList.getLast? == some '*'
def pointerTarget (t : String) : String := String.ofList t.toList.dropLast
def boolean (cfg : Layout) (b : Bool) : Value :=
  .integer ⟨cfg.booleanType,if b then 1 else 0⟩
def truth : Value → Bool
  | .integer v => Scalar.truth v
  | .natObject _ => true
  | .pointer _ _ => true
  | _ => false
def asNat : Value → Option Nat
  | .integer v => if 0 ≤ v.number then some v.number.toNat else none
  | _ => none

def getVar (st : State) (name : String) : Option Address :=
  (st.env.lookup name).orElse (fun _ => st.globals.lookup name)

def fieldsOf (cfg : Layout) (type : String) : Option (List (String × String)) :=
  cfg.records.lookup (normalizeType type)

def typeAt (cfg : Layout) : String → List String → Option String
  | t,[] => some t
  | t,field::rest => do
    let fs ← fieldsOf cfg t
    let next ← fs.lookup field
    typeAt cfg next rest

def addressType (cfg : Layout) (st : State) (a : Address) : Option String := do
  let obj ← st.heap[a.object]?
  if a.index < obj.cells.length then typeAt cfg obj.type a.fields else none

def initialized : Nat → Value → Bool
  | 0,_ => false
  | _+1,.uninitialized => false
  | n+1,.record _ xs | n+1,.aggregate xs => xs.all (initialized n)
  | _+1,_ => true

def uninitializedValue (cfg : Layout) : Nat → String → Value
  | 0,_ => .uninitialized
  | n+1,type => match fieldsOf cfg type with
    | none => .uninitialized
    | some fs => .record (normalizeType type) (fs.map (fun f => uninitializedValue cfg n f.2))

def nested (cfg : Layout) : Value → List String → Option Value
  | v,[] => if initialized 1000 v then some v else none
  | .record tag values,f::rest => do
    let fs ← fieldsOf cfg tag
    let i ← fs.findIdx? (fun x => x.1 == f)
    let v ← values[i]?
    nested cfg v rest
  | _,_ => none

def read (cfg : Layout) (st : State) (a : Address) : Option Value := do
  let obj ← st.heap[a.object]?
  let cell ← obj.cells[a.index]?
  let v ← cell
  nested cfg v a.fields

def castValue (cfg : Layout) (st : State) : Nat → String → Value → Option Value
  | 0,_,_ => none
  | fuel+1,type,v => do
    let t := normalizeType type
    if t == "N" then
      match v with
      | .natObject slot =>
        let _ ← NatArena.read st.nats slot
        pure v
      | .null => pure .null
      | .integer x => if x.number = 0 then pure .null else none
      | _ => none
    else if let some ti := cfg.integers.lookup t then
      let .integer x := v | none
      pure (.integer (←Scalar.cast ti x))
    else if isPointerType t then
      match v with
      | .null => pure .null
      | .integer x => if x.number = 0 then pure .null else none
      | .pointer a writable =>
        let target ← addressType cfg st a
        let expected := pointerTarget t
        if normalizeType target != expected ||
            (!(hasPrefix "const " type) && !writable) then none
        else pure (.pointer a (writable && !(hasPrefix "const " type)))
      | _ => none
    else
      let fs ← fieldsOf cfg t
      let xs ← match v with
        | .record tag xs => if tag == t then some xs else none
        | .aggregate xs => some xs
        | _ => none
      if fs.length != xs.length then none else
        let converted ← (fs.zip xs).mapM
          (fun item => castValue cfg st fuel item.1.2 item.2)
        pure (.record t converted)

def replaceNested (cfg : Layout) : Value → List String → Value → Option Value
  | _,[],v => some v
  | .record tag values,f::rest,v => do
    let fs ← fieldsOf cfg tag
    let i ← fs.findIdx? (fun x => x.1 == f)
    let old ← values[i]?
    let changed ← replaceNested cfg old rest v
    pure (.record tag (values.set i changed))
  | _,_,_ => none

def write (cfg : Layout) (st : State) (a : Address) (writable : Bool)
    (v : Value) : Option (Value × State) := do
  if !writable then none else
    let type ← addressType cfg st a
    let represented ← castValue cfg st 100 type v
    let obj ← st.heap[a.object]?
    let cell ← obj.cells[a.index]?
    let stored ← match a.fields with
      | [] => some represented
      | _ => do
        let old ← cell
        replaceNested cfg old a.fields represented
    let changed : Object := {obj with cells := obj.cells.set a.index (some stored)}
    pure (represented,{st with heap := st.heap.set a.object changed})

def allocate (st : State) (type name : String) (v : Option Value) : State :=
  let a : Address := ⟨st.heap.length,0,[]⟩
  {st with heap := st.heap ++ [{type:=type,cells:=[v]}],env := (name,a)::st.env}

def binaryValue (cfg : Layout) (st : State) (op : String) (a b : Value) : Option Value :=
  match a,b with
  | .integer x,.integer y => do
    let v ← Scalar.binary op x y
    if ["<","<=",">",">=","==","!="].contains op then
      some (boolean cfg (Scalar.truth v)) else some (.integer v)
  | .pointer a writable,.integer n => do
    if op != "+" || !a.fields.isEmpty || n.number < 0 then none else
      let obj ← st.heap[a.object]?
      let index := a.index+n.number.toNat
      if index ≤ obj.cells.length then
        pure (.pointer {a with index:=index} writable)
      else none
  | .null,.null =>
    if op == "==" then some (boolean cfg true)
    else if op == "!=" then some (boolean cfg false) else none
  | .natObject _,.null | .pointer _ _,.null | .null,.natObject _ | .null,.pointer _ _ =>
    if op == "==" then some (boolean cfg false)
    else if op == "!=" then some (boolean cfg true) else none
  | _,_ => none

/-! These are generic expression rules. Application calls remain a parameter
only at this intermediate layer. Final source-program acceptance must close
them by finite executions of the installed function bodies, with only the
enumerated pinned runtime Nat ABI operations at the external boundary. -/
mutual
def evalExpr (cfg : Layout) (call : Call) : Nat → State → Expr → Option (Value × State)
  | 0,_,_ => none
  | fuel+1,st,.nat n => do
    let v ← Scalar.checked ⟨true,32⟩ (n : Int)
    pure (.integer v,st)
  | fuel+1,st,.uint n => do
    let v ← Scalar.checked ⟨false,32⟩ (n : Int)
    pure (.integer v,st)
  | fuel+1,st,.character n => do
    let v ← Scalar.checked ⟨true,8⟩ (n : Int)
    pure (.integer v,st)
  | fuel+1,st,.stringLiteral text => do
    if text.toList.any (fun c => 127 < c.toNat) then none else
      let a : Address := ⟨st.heap.length,0,[]⟩
      let cells := (text.toList.map (fun c =>
        some (.integer ⟨⟨true,8⟩,(c.toNat : Int)⟩))) ++
        [some (.integer ⟨⟨true,8⟩,0⟩)]
      let next := {st with heap := st.heap ++
        [{type:="char",cells:=cells,isArray:=true,writable:=false}]}
      pure (.pointer a false,next)
  | fuel+1,st,.conditional test yes no => do
    let (v,next) ← evalExpr cfg call fuel st test
    evalExpr cfg call fuel next (if truth v then yes else no)
  | fuel+1,st,.var name => do
    if name == "true" then pure (boolean cfg true,st)
    else if name == "false" then pure (boolean cfg false,st)
    else if name == "nullptr" || name == "NULL" then pure (.null,st)
    else
      let a ← getVar st name
      let obj ← st.heap[a.object]?
      if obj.isArray && a.fields.isEmpty then pure (.pointer a obj.writable,st)
      else pure (←read cfg st a,st)
  | fuel+1,st,.unary "&" e => do
    let (a,writable,next) ← evalLValue cfg call fuel st e
    pure (.pointer a writable,next)
  | fuel+1,st,.unary "*" e => do
    let (.pointer a _,next) ← evalExpr cfg call fuel st e | none
    pure (←read cfg next a,next)
  | fuel+1,st,.unary "!" e => do
    let (v,next) ← evalExpr cfg call fuel st e
    pure (boolean cfg (!truth v),next)
  | fuel+1,st,.unary "-" e => do
    let (.integer v,next) ← evalExpr cfg call fuel st e | none
    let n ← Scalar.make v.type (-v.number)
    pure (.integer n,next)
  | fuel+1,st,.unary op e => do
    if op != "++" && op != "--" then none else
      let (a,writable,next) ← evalLValue cfg call fuel st e
      let .integer v ← read cfg next a | none
      let n ← Scalar.make v.type (v.number + (if op == "++" then 1 else -1))
      write cfg next a writable (.integer n)
  | fuel+1,st,.post op e => do
    if op != "++" && op != "--" then none else
      let (a,writable,next) ← evalLValue cfg call fuel st e
      let old ← read cfg next a
      let .integer v := old | none
      let n ← Scalar.make v.type (v.number + (if op == "++" then 1 else -1))
      let (_,last) ← write cfg next a writable (.integer n)
      pure (old,last)
  | fuel+1,st,.cast type e => do
    let (v,next) ← evalExpr cfg call fuel st e
    pure (←castValue cfg next 100 type v,next)
  | fuel+1,st,.binary "=" lhs rhs => do
    let (v,next) ← evalExpr cfg call fuel st rhs
    let (a,writable,last) ← evalLValue cfg call fuel next lhs
    write cfg last a writable v
  | fuel+1,st,.binary "," lhs rhs => do
    let (_,next) ← evalExpr cfg call fuel st lhs
    evalExpr cfg call fuel next rhs
  | fuel+1,st,.binary "&&" lhs rhs => do
    let (v,next) ← evalExpr cfg call fuel st lhs
    if truth v then
      let (r,last) ← evalExpr cfg call fuel next rhs
      pure (boolean cfg (truth r),last)
    else pure (boolean cfg false,next)
  | fuel+1,st,.binary "||" lhs rhs => do
    let (v,next) ← evalExpr cfg call fuel st lhs
    if truth v then pure (boolean cfg true,next) else
      let (r,last) ← evalExpr cfg call fuel next rhs
      pure (boolean cfg (truth r),last)
  | fuel+1,st,.binary op lhs rhs => do
    let (v,next) ← evalExpr cfg call fuel st lhs
    let (r,last) ← evalExpr cfg call fuel next rhs
    pure (←binaryValue cfg last op v r,last)
  | fuel+1,st,.field "." obj field => do
    let (v,next) ← evalExpr cfg call fuel st obj
    pure (←nested cfg v [field],next)
  | fuel+1,st,.field "->" obj field => do
    let (.pointer a _,next) ← evalExpr cfg call fuel st obj | none
    pure (←read cfg next {a with fields := a.fields ++ [field]},next)
  | fuel+1,st,.index obj index => do
    let (a,_,next) ← evalLValue cfg call fuel st (.index obj index)
    pure (←read cfg next a,next)
  | fuel+1,st,.record xs => do
    let (vs,next) ← xs.foldlM (fun (acc,state) e => do
      let (v,last) ← evalExpr cfg call fuel state e
      pure (acc ++ [v],last)) ([],st)
    pure (.aggregate vs,next)
  | fuel+1,st,.call (.var name) args => do
    let (vs,next) ← args.foldlM (fun (acc,state) e => do
      let (v,last) ← evalExpr cfg call fuel state e
      pure (acc ++ [v],last)) ([],st)
    call name vs next
  | _,_,_ => none

def evalLValue (cfg : Layout) (call : Call) :
    Nat → State → Expr → Option (Address × Bool × State)
  | 0,_,_ => none
  | fuel+1,st,.var name => do
      let a ← getVar st name
      let obj ← st.heap[a.object]?
      pure (a,obj.writable,st)
  | fuel+1,st,.unary "*" e => do
    let (.pointer a writable,next) ← evalExpr cfg call fuel st e | none
    let _ ← addressType cfg next a
    pure (a,writable,next)
  | fuel+1,st,.field "." obj field => do
    let (a,writable,next) ← evalLValue cfg call fuel st obj
    let target : Address := {a with fields := a.fields ++ [field]}
    let _ ← addressType cfg next target
    pure (target,writable,next)
  | fuel+1,st,.field "->" obj field => do
    let (.pointer a writable,next) ← evalExpr cfg call fuel st obj | none
    let target : Address := {a with fields := a.fields ++ [field]}
    let _ ← addressType cfg next target
    pure (target,writable,next)
  | fuel+1,st,.index obj index => do
    let (.pointer base writable,next) ← evalExpr cfg call fuel st obj | none
    if !base.fields.isEmpty then none else
      let (idx,last) ← evalExpr cfg call fuel next index
      let n ← asNat idx
      let a : Address := {base with index := base.index+n}
      let _ ← addressType cfg last a
      pure (a,writable,last)
  | _,_,_ => none
end

def declarations (cfg : Layout) (call : Call) (ds : List Decl) (st : State) : Option State :=
  ds.foldlM (fun current d => do
    if let some extent := d.arrayExtent then
      if d.value.isSome then none else
        let a : Address := ⟨current.heap.length,0,[]⟩
        pure { current with
          heap := current.heap ++ [{ type := d.type, cells := List.replicate extent none, isArray := true }]
          env := (d.name,a)::current.env }
    else match d.value with
    | none => pure (allocate current d.type d.name (some (uninitializedValue cfg 100 d.type)))
    | some e =>
      let (v,next) ← evalExpr cfg call 1000 current e
      let represented ← castValue cfg next 100 d.type v
      pure (allocate next d.type d.name (some represented))) st

/-- Only C stack objects are popped. Runtime ownership changes, writes to
older arrays/global objects and application pool state survive scope exit. -/
def popScope (before after : State) : State :=
  {after with heap := after.heap.take before.heap.length,env := before.env}

def bindArgs (cfg : Layout) (parameters : List (String × String))
    (args : List Value) (st : State) : Option State := do
  if parameters.length != args.length then none else
    (parameters.zip args).foldlM (fun current item => do
      let represented ← castValue cfg current 100 item.1.1 item.2
      pure (allocate current item.1.1 item.1.2 (some represented))) {st with env := []}

theorem popScope_runtime (before after : State) :
    (popScope before after).nats = after.nats := rfl

#print axioms popScope_runtime
end ScopedC.Machine

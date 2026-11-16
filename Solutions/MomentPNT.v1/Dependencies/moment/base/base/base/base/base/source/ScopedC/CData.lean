/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.Grammar
import ScopedNumerical.Input

namespace ScopedC.CData
open ScopedC.Syntax
set_option autoImplicit false

/-- Literal mathematical input, never a computed interval or acceptance bit.
The same formal Node list is consumed by the independently proved DAG-to-old-
program equality. The C decimal parser's correctness is a separate obligation.
-/
def nodeInitializer (n : ScopedNumerical.Input.Node) : Expr :=
  .record [.uint n.op,.uint n.a,.uint n.b,
    .stringLiteral (toString n.num),.stringLiteral (toString n.den)]

def nodeArray (name : String) (nodes : List ScopedNumerical.Input.Node) : Decl := {
  type := "static const Node"
  name := name
  value := some (.record (nodes.map nodeInitializer))
  arrayExtent := some nodes.length }

def renderArray (name : String) (nodes : List ScopedNumerical.Input.Node) : Option String := do
  pure ((←renderDecl (nodeArray name nodes))++";\n")

def rowInitializer (name : String) (count cells : Nat) : Expr :=
  .record [.var name,.uint count,.uint cells]

def rowArray (rows : List (String × Nat × Nat)) : Decl := {
  type := "static const Row"
  name := "allRows"
  value := some (.record (rows.map (fun (name,count,cells) => rowInitializer name count cells)))
  arrayExtent := some rows.length }

def depthArray (depths : List Nat) : Decl := {
  type := "static const unsigned"
  name := "allDepths"
  value := some (.record (depths.map Expr.uint))
  arrayExtent := some depths.length }

theorem node_fields_from_same_input (n : ScopedNumerical.Input.Node) :
    nodeInitializer n = .record [.uint n.op,.uint n.a,.uint n.b,
      .stringLiteral (toString n.num),.stringLiteral (toString n.den)] := rfl

end ScopedC.CData

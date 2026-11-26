/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTPairedIntModel
import Lean

/-! An untrusted DATA elaborator, not a proof producer. It proposes ordinary
safe definitions containing kernel-checked Int and List constructors. Every
arithmetic/trace property still requires its separate kernel proof. Avoiding
thousands of overloaded numeral elaborations changes no mathematical check. -/
open Lean Elab Command

private def literalInt : Int → Expr
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkNatLit n)

syntax (name := pairCertificateData) "pair_certificate " ident " from " str " count " num : command

@[command_elab pairCertificateData]
def elabPairCertificateData : CommandElab := fun stx => do
  let `(pair_certificate $id:ident from $file:str count $amount:num) := stx
    | throwUnsupportedSyntax
  let parent := (System.FilePath.mk (← getFileName)).parent.getD (System.FilePath.mk ".")
  let path := parent / file.getString
  let contents ← IO.FS.readFile path
  let mut entries : Array Expr := #[]
  let intType := mkConst ``Int
  let pairType := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) intType intType
  for line in contents.splitOn "\n" do
    if line.isEmpty then continue
    let fields := line.splitOn ","
    unless fields.length=2 do throwError "Malformed pair certificate line"
    let some a := fields[0]!.toInt? | throwError "Invalid first integer"
    let some b := fields[1]!.toInt? | throwError "Invalid second integer"
    entries := entries.push (mkApp4 (mkConst ``Prod.mk [Level.zero,Level.zero])
      intType intType (literalInt a) (literalInt b))
  unless entries.size=amount.getNat do throwError "Wrong pair certificate length"
  let mut value := mkApp (mkConst ``List.nil [Level.zero]) pairType
  for entry in entries.reverse do
    value := mkApp3 (mkConst ``List.cons [Level.zero]) pairType entry value
  let name := (← getCurrNamespace)++id.getId
  liftCoreM <| addDecl (.defnDecl {
    name := name
    levelParams := []
    type := mkApp (mkConst ``List [Level.zero]) pairType
    value := value
    hints := .regular 0
    safety := .safe })
  modifyEnv (addNoncomputable · name)

syntax (name := forestCertificateData) "forest_certificate " ident " from " str " width " num " rows " num : command

@[command_elab forestCertificateData]
def elabForestCertificateData : CommandElab := fun stx => do
  let `(forest_certificate $id:ident from $file:str width $widthLit:num rows $rowsLit:num) := stx
    | throwUnsupportedSyntax
  let columns :=  widthLit.getNat
  let rowCount :=  rowsLit.getNat
  unless columns>0 do throwError "Zero forest width"
  let parent := (System.FilePath.mk (← getFileName)).parent.getD (System.FilePath.mk ".")
  let contents ← IO.FS.readFile (parent / file.getString)
  let intType := mkConst ``Int
  let pairType := mkApp2 (mkConst ``Prod [Level.zero,Level.zero]) intType intType
  let listType := mkApp (mkConst ``List [Level.zero]) pairType
  let mut entries : Array Expr := #[]
  for line in contents.splitOn "\n" do
    if line.isEmpty then continue
    let fields := line.splitOn ","
    unless fields.length=2 do throwError "Malformed forest pair"
    let some a := fields[0]!.toInt? | throwError "Invalid first forest integer"
    let some b := fields[1]!.toInt? | throwError "Invalid second forest integer"
    entries := entries.push (mkApp4 (mkConst ``Prod.mk [Level.zero,Level.zero])
      intType intType (literalInt a) (literalInt b))
  unless entries.size=columns*rowCount do throwError "Wrong forest dimensions"
  let mut forest := mkApp (mkConst ``List.nil [Level.zero]) listType
  for r in (List.range rowCount).reverse do
    let mut row := mkApp (mkConst ``List.nil [Level.zero]) pairType
    for j in (List.range columns).reverse do
      row := mkApp3 (mkConst ``List.cons [Level.zero]) pairType entries[r*columns+j]! row
    forest := mkApp3 (mkConst ``List.cons [Level.zero]) listType row forest
  let name := (← getCurrNamespace)++id.getId
  liftCoreM <| addDecl (.defnDecl {
    name := name, levelParams := [], type := mkApp (mkConst ``List [Level.zero]) listType
    value := forest, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

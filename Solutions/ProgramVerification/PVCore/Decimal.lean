/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import PVCore.Kernel

/-!
# Decoding decimal literals in the kernel

`PVCore.Exec` gives a C literal the value `FKS2Scalar.decimal s` rounded by `round64`. `decimal`
splits on `"."` with `String.splitOn` (a well-founded recursion over UTF-8 byte positions) and reads
digits with `String.toNat?` (a slice iterator). In Lean 4.34 `String` is `ByteArray`-backed and
neither function reduces in the kernel, which is why `PVCore.decode` needed `native_decide`.

This module replaces that native fact by a theorem, for every string:

* `splitOnFuel` is `String.splitOnAux` with a fuel argument, so it is structurally recursive;
  `splitOnFuel_sound` shows that whenever it returns, `splitOnAux` returns the same list (one
  unfolding of `splitOnAux`'s equation per step).
* `toNatList?` is `String.Slice.toNat?` read on the character list; `toNat?_eq` is the library's
  `forIn`/`foldl` → `toList` lemmas.
* `decimalL s = some q → decimal s = some q` (`decimal_of_decimalL`), and the same for whole
  programs: `decodeL p = some v → decode p = some v` (`decode_of_decodeL`).

`decimalL` and `decodeL` use only the byte-level primitives `get`, `next`, `atEnd`, `extract` and
`toList`, which reduce in the kernel, so `decodeL p = some v` is proved by `decide +kernel`. The
literal semantics is unchanged: it is still `decimal`, and the decoded values are the ones
`decode` would give.
-/

namespace PVCore

open String FKS2Scalar

/-- `String.splitOnAux` with fuel. -/
def splitOnFuel : ℕ → String → String → Pos.Raw → Pos.Raw → Pos.Raw → List String →
    Option (List String)
  | 0, _, _, _, _, _, _ => none
  | n + 1, s, sep, b, i, j, r =>
    if Pos.Raw.atEnd s i = true then some (Pos.Raw.extract s b i :: r).reverse
    else if (Pos.Raw.get s i == Pos.Raw.get sep j) = true then
      if Pos.Raw.atEnd sep (Pos.Raw.next sep j) = true then
        splitOnFuel n s sep (Pos.Raw.next s i) (Pos.Raw.next s i) 0
          (Pos.Raw.extract s b ((Pos.Raw.next s i).unoffsetBy (Pos.Raw.next sep j)) :: r)
      else splitOnFuel n s sep b (Pos.Raw.next s i) (Pos.Raw.next sep j) r
    else splitOnFuel n s sep b (Pos.Raw.next s (i.unoffsetBy j)) 0 r

/-- One step of `String.splitOnAux`, from its equation. -/
theorem splitOnAux_unfold (s sep : String) (b i j : Pos.Raw) (r : List String) :
    s.splitOnAux sep b i j r =
      if Pos.Raw.atEnd s i = true then (Pos.Raw.extract s b i :: r).reverse
      else if (Pos.Raw.get s i == Pos.Raw.get sep j) = true then
        if Pos.Raw.atEnd sep (Pos.Raw.next sep j) = true then
          s.splitOnAux sep (Pos.Raw.next s i) (Pos.Raw.next s i) 0
            (Pos.Raw.extract s b ((Pos.Raw.next s i).unoffsetBy (Pos.Raw.next sep j)) :: r)
        else s.splitOnAux sep b (Pos.Raw.next s i) (Pos.Raw.next sep j) r
      else s.splitOnAux sep b (Pos.Raw.next s (i.unoffsetBy j)) 0 r := by
  rw [String.splitOnAux.eq_def]

theorem splitOnFuel_sound : ∀ (n : ℕ) (s sep : String) (b i j : Pos.Raw) (r res : List String),
    splitOnFuel n s sep b i j r = some res → s.splitOnAux sep b i j r = res
  | 0, _, _, _, _, _, _, _, h => by simp [splitOnFuel] at h
  | n + 1, s, sep, b, i, j, r, res, h => by
      rw [splitOnAux_unfold]
      simp only [splitOnFuel] at h
      by_cases h1 : Pos.Raw.atEnd s i = true
      · simp only [h1, ite_true, Option.some.injEq] at h ⊢
        exact h
      · simp only [h1] at h ⊢
        by_cases h2 : (Pos.Raw.get s i == Pos.Raw.get sep j) = true
        · simp only [h2, ite_true] at h ⊢
          by_cases h3 : Pos.Raw.atEnd sep (Pos.Raw.next sep j) = true
          · simp only [h3, ite_true] at h ⊢
            exact splitOnFuel_sound n _ _ _ _ _ _ _ h
          · simp only [h3] at h ⊢
            exact splitOnFuel_sound n _ _ _ _ _ _ _ h
        · simp only [h2] at h ⊢
          exact splitOnFuel_sound n _ _ _ _ _ _ _ h

/-- `String.Slice.isNat`, on the character list. -/
def isNatList (l : List Char) : Bool := Id.run do
  let mut lastWasDigit := false

  for c in l do
    if c = '_' then
      if !lastWasDigit then
        return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else
      return false

  return lastWasDigit

/-- `String.Slice.toNat?`, on the character list. -/
def toNatList? (l : List Char) : Option ℕ :=
  if isNatList l then
    some <| l.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0
  else
    none

theorem isNat_eq (a : String) : a.toSlice.isNat = isNatList a.toList := by
  simp only [String.Slice.isNat, isNatList, String.Slice.forIn_eq_forIn_toList, String.copy_toSlice]

theorem toNat?_eq (a : String) : a.toNat? = toNatList? a.toList := by
  simp only [String.toNat?, String.Slice.toNat?, isNat_eq, String.Slice.foldl_eq_foldl_toList,
    String.copy_toSlice, toNatList?]

/-- `FKS2Scalar.decimal` with `splitOnFuel` and `toNatList?`: what the kernel evaluates. -/
def decimalL (s : String) : Option ℚ :=
  match splitOnFuel (s.length + 2) s "." 0 0 0 [] with
  | some [a, b] =>
    match toNatList? a.toList, toNatList? b.toList with
    | some n, some m => some ((n : ℚ) + (m : ℚ) / (10 ^ b.length : ℕ))
    | _, _ => none
  | _ => none

theorem decimal_of_decimalL {s : String} {q : ℚ} (h : decimalL s = some q) :
    decimal s = some q := by
  unfold decimalL at h
  split at h
  · rename_i a b hsplit
    have hs : s.splitOn "." = [a, b] := by
      have := splitOnFuel_sound _ s "." 0 0 0 [] [a, b] hsplit
      simp only [String.splitOn]
      have hne : ("." == "") = false := by decide
      simp only [hne, Bool.false_eq_true, ite_false]
      exact this
    split at h
    · rename_i n m hn hm
      have hn' : a.toNat? = some n := by rw [toNat?_eq]; exact hn
      have hm' : b.toNat? = some m := by rw [toNat?_eq]; exact hm
      unfold decimal
      simp only [hs, hn', hm', Option.pure_def, Option.bind_eq_bind, Option.bind_some]
      exact h
    · simp at h
  · simp at h

/-- `loadLiteral` through `decimalL`. -/
def loadLiteralL (s : String) : Option ℚ := (decimalL s).bind round64

theorem loadLiteral_of_L {s : String} {x : ℚ} (h : loadLiteralL s = some x) :
    loadLiteral s = some x := by
  unfold loadLiteralL at h
  unfold loadLiteral
  cases hd : decimalL s with
  | none => simp [hd] at h
  | some q =>
    rw [hd] at h
    rw [decimal_of_decimalL hd]
    exact h

theorem mapM_of_L {l : List String} {xs : List ℚ} (h : l.mapM loadLiteralL = some xs) :
    l.mapM loadLiteral = some xs := by
  induction l generalizing xs with
  | nil => simpa using h
  | cons s l ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    exact ⟨x, loadLiteral_of_L hx, ys, ih hys, rfl⟩

/-- `decode` through `loadLiteralL`. -/
def decodeL (p : Program) : Option (List ℚ × ℚ × List (Sign × ℚ)) := do
  let xs ← p.inputs.mapM loadLiteralL
  let scale ← loadLiteralL p.scale
  let ops ← p.ops.mapM fun o => (loadLiteralL o.2).map fun c => (o.1, c)
  return (xs, scale, ops)

theorem opsM_of_L {os : List (Sign × String)} {vs : List (Sign × ℚ)}
    (h : os.mapM (fun o => (loadLiteralL o.2).map fun c => (o.1, c)) = some vs) :
    os.mapM (fun o => (loadLiteral o.2).map fun c => (o.1, c)) = some vs := by
  induction os generalizing vs with
  | nil => simpa using h
  | cons o os ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨v, hv, ws, hws, rfl⟩ := h
    refine ⟨v, ?_, ws, ih hws, rfl⟩
    cases hl : loadLiteralL o.2 with
    | none => simp [hl] at hv
    | some c =>
      rw [hl] at hv
      rw [loadLiteral_of_L hl]
      exact hv

/-- **No native fact for decoding.** `decodeL p = some v` (kernel-decidable) gives `decode p = some v`. -/
theorem decode_of_decodeL {p : Program} {v : List ℚ × ℚ × List (Sign × ℚ)}
    (h : decodeL p = some v) : decode p = some v := by
  unfold decodeL at h
  unfold decode loadOps
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h ⊢
  obtain ⟨xs, hxs, scale, hsc, ops, hops, rfl⟩ := h
  exact ⟨xs, mapM_of_L hxs, scale, loadLiteral_of_L hsc, ops, opsM_of_L hops, rfl⟩

end PVCore

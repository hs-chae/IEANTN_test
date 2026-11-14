/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.TypedFrameBasic

namespace ScopedC.TypedFrames
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

 theorem cast_aggregate (cfg : Layout) (s : State) (fuel : Nat) (type tag : String)
    (fields : List (String × String)) (values converted : List Value)
    (normalize : normalizeType type = tag) (canonical : normalizeType tag = tag)
    (notNat : tag ≠ "N") (notInt : cfg.integers.lookup tag = none)
    (notPtr : isPointerType tag = false) (record : cfg.records.lookup tag = some fields)
    (length : fields.length = values.length)
    (each : (fields.zip values).mapM (fun item => castValue cfg s fuel item.1.2 item.2) = some converted) :
    castValue cfg s (fuel+1) type (.aggregate values) = some (.record tag converted) := by
  change (if normalizeType type == "N" then none
    else if let some _ := cfg.integers.lookup (normalizeType type) then none
    else if isPointerType (normalizeType type) then none
    else do
      let fs ← fieldsOf cfg (normalizeType type)
      if fs.length != values.length then none else
        let ws ← (fs.zip values).mapM (fun item => castValue cfg s fuel item.1.2 item.2)
        pure (Value.record (normalizeType type) ws)) = some (.record tag converted)
  have hn : (tag == "N") = false := by simp [notNat]
  have hl : (fields.length != values.length) = false := by simp [length]
  simp only [normalize,hn,Bool.false_eq_true,↓reduceIte,notInt,notPtr,fieldsOf,canonical,record]
  simp only [bind,Option.bind,hl,Bool.false_eq_true,↓reduceIte,each]
  rfl

 theorem cast_record (cfg : Layout) (s : State) (fuel : Nat) (type tag : String)
    (fields : List (String × String)) (values converted : List Value)
    (normalize : normalizeType type = tag) (canonical : normalizeType tag = tag)
    (notNat : tag ≠ "N") (notInt : cfg.integers.lookup tag = none)
    (notPtr : isPointerType tag = false) (record : cfg.records.lookup tag = some fields)
    (length : fields.length = values.length)
    (each : (fields.zip values).mapM (fun item => castValue cfg s fuel item.1.2 item.2) = some converted) :
    castValue cfg s (fuel+1) type (.record tag values) = some (.record tag converted) := by
  change (if normalizeType type == "N" then none
    else if let some _ := cfg.integers.lookup (normalizeType type) then none
    else if isPointerType (normalizeType type) then none
    else do
      let fs ← fieldsOf cfg (normalizeType type)
      let xs ← if tag == normalizeType type then some values else none
      if fs.length != xs.length then none else
        let ws ← (fs.zip xs).mapM (fun item => castValue cfg s fuel item.1.2 item.2)
        pure (Value.record (normalizeType type) ws)) = some (.record tag converted)
  have hn : (tag == "N") = false := by simp [notNat]
  have hl : (fields.length != values.length) = false := by simp [length]
  simp only [normalize,hn,Bool.false_eq_true,↓reduceIte,notInt,notPtr,fieldsOf,canonical,record,BEq.rfl]
  simp only [bind,Option.bind,hl,Bool.false_eq_true,↓reduceIte,each]
  rfl

end ScopedC.TypedFrames

/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalValues
import SynergyC.WordRemainder
import ScopedC.ExpressionBinary

namespace SynergyC.PositiveSubBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def difference (a b : Int) : Int := max 0 (a-b)
def rawDifference (a b : Int) : Value :=
  if b < a then value (a-b) else .integer MulBody.intZero
def endpoint (a b : Expr) : Expr := .conditional (.binary ">" a b) (.binary "-" a b) (.nat 0)
def initializer : Expr := .record [
  endpoint (.field "." (.var "a") "lo") (.field "." (.var "b") "hi"),
  endpoint (.field "." (.var "a") "hi") (.field "." (.var "b") "lo")]
def declaration : Decl := {type:="I",name:="r",value:=some initializer,arrayExtent:=none}
def resultFrame (s : State) (al ah bl bh : Int) : State :=
  allocate (IntervalValues.frame s al ah bl bh) "I" "r"
    (some (interval (difference al bh) (difference ah bl)))

theorem difference_range {a b : Int} (ha : Range a) (hb : Range b) : Range (difference a b) := by
  constructor
  · exact le_max_left _ _
  · exact lt_of_le_of_lt (max_le ha.1 (by have h:=hb.1; omega)) ha.2

theorem cast_difference (s : State) (fuel : Nat) {a b : Int} (ha : Range a) (hb : Range b) :
    castValue Header.layout s (fuel+1) "U" (rawDifference a b) = some (value (difference a b)) := by
  by_cases h : b < a
  · have hm : difference a b = a-b := max_eq_right (by omega)
    simp only [rawDifference,h,↓reduceIte,hm]
    exact cast_word_positive _ _ (by simpa [hm] using difference_range ha hb)
  · have hm : difference a b = 0 := max_eq_left (by omega)
    simp only [rawDifference,h,↓reduceIte,hm]
    have h0 : Range 0 := by change (0:Int) ≤ 0 ∧ 0 < 2^512; decide +kernel
    change (do let x ← Scalar.make type 0; pure (Value.integer x)) = _
    rw [Scalar.make_exact (range_scalar h0)]
    rfl

theorem word_gt {a b : Int} (ha : Range a) (hb : Range b) :
    Scalar.binary ">" (word a) (word b) = some (Scalar.boolean (decide (b<a))) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b)
             pure (Scalar.boolean (decide (x.number>y.number)))) = _
  rw [cast_scalar ha,cast_scalar hb]
  rfl

theorem eval_endpoint (service : Call) (fuel : Nat) {s : State} {a b : Int} {left right : Expr}
    (ha : Range a) (hb : Range b)
    (ea : evalExpr Header.layout service (fuel+1) s left = some (value a,s))
    (eb : evalExpr Header.layout service (fuel+1) s right = some (value b,s)) :
    evalExpr Header.layout service (fuel+3) s (endpoint left right) = some (rawDifference a b,s) := by
  have bg : binaryValue Header.layout s ">" (value a) (value b) =
      some (boolean Header.layout (decide (b<a))) := by
    simp only [binaryValue,value,word_gt ha hb,Option.bind_some]
    by_cases h : b<a <;> simp [h,Bind.bind,Option.bind,Scalar.boolean,Scalar.truth]
  have test := ExpressionTemplates.binary Header.layout service
    (by decide) (by decide) (by decide) (by decide) ea eb bg
  apply ExpressionTemplates.conditional Header.layout service test
  by_cases h : b<a
  · have bs : binaryValue Header.layout s "-" (value a) (value b) = some (value (a-b)) := by
      simp only [binaryValue,value,word_sub ha hb h.le,Option.bind_some]
      rfl
    have sub := ExpressionTemplates.binary Header.layout service
      (by decide) (by decide) (by decide) (by decide) ea eb bs
    simpa [truth,Machine.boolean,Scalar.truth,h,rawDifference] using sub
  · simp only [truth,Machine.boolean,Scalar.truth,h,decide_false,rawDifference,↓reduceIte]
    rfl

theorem eval_initializer (s : State) (al ah bl bh : Int)
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh) :
    evalExpr Header.layout RuntimeCore.call 1000 (IntervalValues.frame s al ah bl bh) initializer =
      some (.aggregate [rawDifference al bh,rawDifference ah bl],IntervalValues.frame s al ah bl bh) := by
  exact ExpressionTemplates.record_two Header.layout RuntimeCore.call
    (eval_endpoint _ 996 hal hbh (IntervalValues.eval_a_lo _ 995 s al ah bl bh)
      (IntervalValues.eval_b_hi _ 995 s al ah bl bh))
    (eval_endpoint _ 996 hah hbl (IntervalValues.eval_a_hi _ 995 s al ah bl bh)
      (IntervalValues.eval_b_lo _ 995 s al ah bl bh))

theorem declared (s : State) (al ah bl bh : Int)
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh) :
    declarations Header.layout RuntimeCore.call [declaration] (IntervalValues.frame s al ah bl bh) =
      some (resultFrame s al ah bl bh) := by
  have casts := TypedFrames.cast_aggregate Header.layout (IntervalValues.frame s al ah bl bh) 99 "I" "I"
    [("lo","U"),("hi","U")] [rawDifference al bh,rawDifference ah bl]
    [value (difference al bh),value (difference ah bl)]
    rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
    (by
      change (do let x ← castValue Header.layout _ 99 "U" (rawDifference al bh)
                 let y ← castValue Header.layout _ 99 "U" (rawDifference ah bl); pure [x,y]) = _
      rw [cast_difference _ 98 hal hbh,cast_difference _ 98 hah hbl]
      rfl)
  simp only [declarations,declaration,List.foldlM,eval_initializer s al ah bl bh hal hah hbl hbh,
    Bind.bind,Option.bind]
  rw [casts]
  rfl

theorem source_positiveSub (code : List Function) (installed : Generated.f_positiveSub ∈ code)
    (s : State) {al ah bl bh : Int}
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh) :
    SourceCall Header.layout code 1 "positiveSub" [interval al ah,interval bl bh] s
      (interval (difference al bh) (difference ah bl)) s := by
  have localEval : Eval Header.layout RuntimeCore.call (.var "r") (resultFrame s al ah bl bh)
      (resultFrame s al ah bl bh) (interval (difference al bh) (difference ah bl)) := by
    refine ⟨2,?_⟩
    exact TypedFrames.allocate_eval Header.layout RuntimeCore.call 1 (IntervalValues.frame s al ah bl bh)
      "I" "r" _ (by rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have body : Run Header.layout RuntimeCore.call Generated.f_positiveSub.body
      (IntervalValues.frame s al ah bl bh)
      (.returned (IntervalValues.frame s al ah bl bh) (interval (difference al bh) (difference ah bl))) := by
    change Run Header.layout RuntimeCore.call (.sequence [.declare [declaration],.returnStmt (.var "r")])
      (IntervalValues.frame s al ah bl bh) _
    apply Loops.StmtRun.sequence
    · exact Loops.SeqRun.next (Loops.StmtRun.declare (declared s al ah bl bh hal hah hbl hbh))
        (Loops.SeqRun.returned (Loops.StmtRun.returnValue localEval))
    · exact ⟨rfl,(TypedFrames.pop_allocate (IntervalValues.frame s al ah bl bh) "I" "r"
        (some (interval (difference al bh) (difference ah bl)))).symm⟩
  have finish : Finish Header.layout Generated.f_positiveSub s
      (.returned (IntervalValues.frame s al ah bl bh) (interval (difference al bh) (difference ah bl)))
      (interval (difference al bh) (difference ah bl)) s := by
    change castValue Header.layout (IntervalValues.frame s al ah bl bh) 100 "static I"
      (interval (difference al bh) (difference ah bl)) = some _ ∧ s = popScope s (IntervalValues.frame s al ah bl bh)
    exact ⟨IntervalValues.cast_record _ 98 (difference_range hal hbh) (difference_range hah hbl),
      (IntervalValues.pop_frame s al ah bl bh).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=0) installed
    (fun _ _ _ _ _ h=>h) (IntervalValues.bind s hal hah hbl hbh) body finish

end SynergyC.PositiveSubBody

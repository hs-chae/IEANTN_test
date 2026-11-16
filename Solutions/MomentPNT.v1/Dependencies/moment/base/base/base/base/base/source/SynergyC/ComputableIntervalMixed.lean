/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ComputableIntervalInput
import SynergyC.ComputableIntervalLibrary

namespace SynergyC.ComputableIntervalMixed
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
open SynergyC.ComputableIntervalInput
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

local instance (n : Int) : Decidable (Range n) := by unfold Range;infer_instance
local instance (n : Int) : Decidable (SmallWord.Range n) := by unfold SmallWord.Range;infer_instance

def ratAllowed (n d : Int) : Prop := Range n ∧ Range d ∧ 0<d ∧ Range (n*UnitBody.scale)
local instance (n d : Int) : Decidable (ratAllowed n d) := by unfold ratAllowed;infer_instance

def rat : List Value→State→Option (Value×State) := fun args s=>do
  let [.integer n,.integer d]:=args | none
  if ratAllowed n.number d.number then some (RatBody.result n.number d.number,s) else none

theorem rat_closed (code : List Function) (lib : ComputableIntervalService.Library code)
    {s t : State} (maxCtx : MaxContext s) (scaleCtx : UnitBody.ScaleContext s)
    {args : List Value} {v : Value} (h : rat args s=some (v,t)) :
    SourceCall Header.layout code 3 "rat" args s v t := by
  unfold rat at h
  split at h
  · rename_i n d
    split_ifs at h with good
    simp only[Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rcases good with ⟨hn,hd,positive,fit⟩
    have canonical:=RatBody.source_rat code lib.rat lib.addU lib.mulU lib.ceilDiv lib.arithmeticParameters
      maxCtx scaleCtx hn hd positive fit
    apply ArgumentConversion.replace_arguments canonical
    · rfl
    · intro f member named
      rw[ComputableIntervalService.rat_parameters code lib.mixedParameters f member named]
      have raw:=TypedFrames.bind_two Header.layout s "U" "n" "U" "d"
        (.integer n) (.integer d) (value n.number) (value d.number)
        (ArithmeticService.cast_integer _ n hn) (ArithmeticService.cast_integer _ d hd)
      rw[raw,RatFrames.bind s hn hd]
      rfl
  · contradiction

def divNAllowed (a : Bounds) (n : Int) : Prop := Range a.lo ∧ Range a.hi ∧ SmallWord.Range n ∧ 0<n
local instance (a : Bounds) (n : Int) : Decidable (divNAllowed a n) := by unfold divNAllowed;infer_instance

def divN : List Value→State→Option (Value×State) := fun args s=>do
  let [raw,.integer n]:=args | none
  let a←interval? raw
  if divNAllowed a.val n.number then some (DivNBody.result a.val.lo a.val.hi n.number,s) else none

theorem cast_small_integer (s : State) (a : Scalar.Value) (ha : SmallWord.Range a.number) :
    castValue Header.layout s 100 "unsigned int" (.integer a)=some (SmallWord.value a.number) := by
  change (do let x←Scalar.make SmallWord.type a.number;pure (Value.integer x))=_
  rw[Scalar.make_exact (SmallWord.scalar_range ha)]
  rfl

theorem divN_closed (code : List Function) (lib : ComputableIntervalService.Library code)
    {s t : State} (maxCtx : MaxContext s) {args : List Value} {v : Value}
    (h : divN args s=some (v,t)) : SourceCall Header.layout code 3 "divN" args s v t := by
  unfold divN at h
  split at h
  · rename_i raw n
    cases ha : interval? raw with
    | none=>simp [ha] at h
    | some a=>
      simp only[ha,Bind.bind,Option.bind] at h
      split_ifs at h with good
      simp only[Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rcases a with ⟨a,ax⟩
      change SourceCall Header.layout code 3 "divN" [raw,.integer n] s (DivNBody.result a.lo a.hi n.number) s
      change divNAllowed a n.number at good
      rw[ax]
      rcases good with ⟨al,ah,hn,positive⟩
      have canonical:=DivNBody.source_divN code lib.divN lib.addU lib.mulU lib.ceilDiv lib.arithmeticParameters
        maxCtx al ah hn positive
      apply ArgumentConversion.replace_arguments canonical
      · rfl
      · intro f member named
        rw[ComputableIntervalService.divN_parameters code lib.mixedParameters f member named]
        have raw:=TypedFrames.bind_two Header.layout s "I" "a" "unsigned int" "n"
          (ZeroBody.interval a.lo a.hi) (.integer n) (ZeroBody.interval a.lo a.hi) (SmallWord.value n.number)
          (IntervalValues.cast_record _ 98 al ah) (cast_small_integer _ n hn)
        rw[raw,DivNFrames.bind s al ah hn]
        rfl
  · contradiction

end SynergyC.ComputableIntervalMixed

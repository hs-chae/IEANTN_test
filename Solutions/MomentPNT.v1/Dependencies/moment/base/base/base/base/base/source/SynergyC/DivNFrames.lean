/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.SmallWord

namespace SynergyC.DivNFrames
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (al ah n : Int) : State :=
  allocate (allocate {s with env:=[]} "I" "a" (some (interval al ah)))
    "unsigned int" "n" (some (SmallWord.value n))

theorem bind (s : State) {al ah n : Int} (hal : Range al) (hah : Range ah) (hn : SmallWord.Range n) :
    bindArgs Header.layout [("I","a"),("unsigned int","n")]
      [interval al ah,SmallWord.value n] s = some (frame s al ah n) :=
  TypedFrames.bind_two Header.layout s "I" "a" "unsigned int" "n"
    (interval al ah) (SmallWord.value n) (interval al ah) (SmallWord.value n)
    (IntervalValues.cast_record _ 98 hal hah) (SmallWord.cast_small_int _ hn)

theorem eval_a (service : Call) (fuel : Nat) (s : State) (al ah n : Int) :
    evalExpr Header.layout service (fuel+1) (frame s al ah n) (.var "a") =
      some (interval al ah,frame s al ah n) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,interval,value]

theorem eval_n (service : Call) (fuel : Nat) (s : State) (al ah n : Int) :
    evalExpr Header.layout service (fuel+1) (frame s al ah n) (.var "n") =
      some (SmallWord.value n,frame s al ah n) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,SmallWord.value]

theorem eval_lo (service : Call) (fuel : Nat) (s : State) (al ah n : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah n) (.field "." (.var "a") "lo") =
      some (value al,frame s al ah n) :=
  ExpressionTemplates.field Header.layout service (eval_a service fuel s al ah n) (IntervalValues.lo_field al ah)

theorem eval_hi (service : Call) (fuel : Nat) (s : State) (al ah n : Int) :
    evalExpr Header.layout service (fuel+2) (frame s al ah n) (.field "." (.var "a") "hi") =
      some (value ah,frame s al ah n) :=
  ExpressionTemplates.field Header.layout service (eval_a service fuel s al ah n) (IntervalValues.hi_field al ah)

def maxContext {s : State} (ctx : MaxContext s) (al ah n : Int) : MaxContext (frame s al ah n) :=
  WordService.allocateContext
    (WordService.allocateContext (WordService.emptyEnvContext ctx) "I" "a" (some (interval al ah)))
    "unsigned int" "n" (some (SmallWord.value n))

theorem pop_frame (s : State) (al ah n : Int) : popScope s (frame s al ah n) = s := by
  simp [popScope,frame,allocate,List.take_append]

end SynergyC.DivNFrames

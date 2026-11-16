/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalMulExpr

namespace SynergyC.RatFrames
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frame (s : State) (n d : Int) : State :=
  allocate (allocate {s with env:=[]} "U" "n" (some (value n))) "U" "d" (some (value d))
def withProduct (s : State) (n d : Int) : State :=
  allocate (frame s n d) "U" "a" (some (value (n*scale)))

theorem bind (s : State) {n d : Int} (hn : Range n) (hd : Range d) :
    bindArgs Header.layout [("U","n"),("U","d")] [value n,value d] s = some (frame s n d) :=
  TypedFrames.bind_two Header.layout s "U" "n" "U" "d" (value n) (value d) (value n) (value d)
    (cast_word _ hn) (cast_word _ hd)

theorem eval_n (service : Call) (fuel : Nat) (s : State) (n d : Int) :
    evalExpr Header.layout service (fuel+1) (frame s n d) (.var "n") = some (value n,frame s n d) := by
  simp [evalExpr,getVar,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,value]

theorem eval_a (service : Call) (fuel : Nat) (s : State) (n d : Int) :
    evalExpr Header.layout service (fuel+1) (withProduct s n d) (.var "a") =
      some (value (n*scale),withProduct s n d) := by
  simp [evalExpr,getVar,withProduct,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,value]

theorem eval_d (service : Call) (fuel : Nat) (s : State) (n d : Int) :
    evalExpr Header.layout service (fuel+1) (withProduct s n d) (.var "d") =
      some (value d,withProduct s n d) := by
  simp [evalExpr,getVar,withProduct,frame,allocate,List.lookup,List.getElem?_append,
    Machine.read,nested,initialized,value]

theorem eval_scale (service : Call) (fuel : Nat) {s : State} (ctx : ScaleContext s) (n d : Int) :
    evalExpr Header.layout service (fuel+1) (frame s n d) (.var "S") =
      some (value scale,frame s n d) := by
  have get : getVar (frame s n d) "S" = some ctx.address := by
    simp [getVar,frame,allocate,List.lookup,ctx.located]
  have read : Machine.read Header.layout (frame s n d) ctx.address = some (value scale) := by
    rw [frame,WordFrames.read_append]
    · rw [WordFrames.read_append]
      · exact ctx.contents
      · exact ctx.allocated
    · simpa [allocate] using Nat.lt.step ctx.allocated
  have heap : (frame s n d).heap[ctx.address.object]? = some ctx.object := by
    simp only [frame,allocate]
    rw [List.getElem?_append_left (by simpa using Nat.lt.step ctx.allocated)]
    rw [List.getElem?_append_left ctx.allocated]
    exact ctx.heap_entry
  rw [evalExpr]
  simp [get,heap,ctx.scalar,read]

def maxContext {s : State} (ctx : MaxContext s) (n d : Int) : MaxContext (frame s n d) :=
  WordService.allocateContext
    (WordService.allocateContext (WordService.emptyEnvContext ctx) "U" "n" (some (value n)))
    "U" "d" (some (value d))

def productMaxContext {s : State} (ctx : MaxContext s) (n d : Int) : MaxContext (withProduct s n d) :=
  WordService.allocateContext (maxContext ctx n d) "U" "a" (some (value (n*scale)))

theorem pop_frame (s : State) (n d : Int) : popScope s (frame s n d) = s := by
  simp [popScope,frame,allocate,List.take_append]

end SynergyC.RatFrames

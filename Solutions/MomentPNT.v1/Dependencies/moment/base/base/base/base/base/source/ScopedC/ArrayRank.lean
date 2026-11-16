/- Monotonicity of source execution depth; does not assert any output. -/
import ScopedC.ArraySourceCalls

namespace ScopedC.ArrayRank
open ScopedC ScopedC.Machine ScopedC.ArraySourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0

theorem one_more {cfg : Layout} {code : List Syntax.Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (h : SourceCall cfg code rank name args s v t) :
    SourceCall cfg code (rank+1) name args s v t := by
  induction rank generalizing name args s v t with
  | zero => exact runtime_leaf h
  | succ rank ih =>
      rcases h with runtime | ⟨f,installed,named,service,closed,frame,arguments,outcome,body,finish⟩
      · exact runtime_leaf runtime
      · exact Or.inr ⟨f,installed,named,service,
          (fun called actual start value final check => ih (closed called actual start value final check)),
          frame,arguments,outcome,body,finish⟩

theorem lift {cfg : Layout} {code : List Syntax.Function} {rank : Nat}
    {name : String} {args : List Value} {s t : State} {v : Value}
    (extra : Nat) (h : SourceCall cfg code rank name args s v t) :
    SourceCall cfg code (rank+extra) name args s v t := by
  induction extra with
  | zero => exact h
  | succ extra ih => exact one_more ih

theorem of_le {cfg : Layout} {code : List Syntax.Function} {r sRank : Nat}
    {name : String} {args : List Value} {before after : State} {v : Value}
    (hrs : r ≤ sRank) (h : SourceCall cfg code r name args before v after) :
    SourceCall cfg code sRank name args before v after := by
  obtain ⟨extra,he⟩ := Nat.exists_eq_add_of_le hrs
  rw [he]
  exact lift extra h

#print axioms of_le
#print axioms one_more
#print axioms lift
end ScopedC.ArrayRank

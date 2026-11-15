/- The entire actual subsequent printS generation loop. The recursion is
justified by n/10<n; the final zero check still performs the source allocation.
No loop invariant, callback result or desired output is an added assumption. -/
import ScopedIO.PrintSTailStep

namespace ScopedIO.PrintSTailLoop
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSIteration ScopedIO.PrintSTailPost
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem loop_exists (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (nrInstalled : Generated.f_nr ∈ code)
    (smallInstalled : Generated.f_small ∈ code) (nleInstalled : Generated.f_nle ∈ code)
    (ndInstalled : Generated.f_nd ∈ code) (nzInstalled : Generated.f_nz ∈ code)
    (neInstalled : Generated.f_ne ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    (l : PoolLayout) (a : Value) (n : Nat) (c : Cursor) (slot : Nat) (ds : List Nat)
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+6*(Nat.digits 10 n).length+1 ≤ capacity)
    (prefixBound : ds.length+(Nat.digits 10 n).length ≤ 1024) :
    ∃ final outputSlot es,Post code l c final a slot outputSlot n ds es := by
  induction n using Nat.strong_induction_on generalizing c slot ds with
  | h n ih =>
    by_cases zero : n=0
    · subst n
      have lenZero : (Nat.digits 10 0).length=0 := by simp
      exact PrintSTailPost.zero_case code nzInstalled nuInstalled neInstalled keepInstalled
        ctx live (by omega) a ds
    · apply PrintSTailStep.extend code nuInstalled nrInstalled smallInstalled nleInstalled
        ndInstalled nzInstalled neInstalled keepInstalled l a n zero ?_ c slot ds ctx live room prefixBound
      intro nextCursor nextSlot nextDigits nextCtx nextLive nextRoom nextPrefix
      exact ih (n/10) (Nat.div_lt_self (by omega) (by decide))
        nextCursor nextSlot nextDigits nextCtx nextLive nextRoom nextPrefix

end ScopedIO.PrintSTailLoop

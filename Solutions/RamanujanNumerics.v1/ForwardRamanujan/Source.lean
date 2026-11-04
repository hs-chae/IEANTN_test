/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Table4.Rounding
import SumStability.Source

namespace ForwardRamanujan
open FKS2Scalar FKS2Table4 SumStability

/-- Source-identical decimal/RN and loop interpretation reused from the earlier application. -/
def loadLiteral (s : String) : Option ℚ := (decimal s).bind round64

def runSum : List ℚ → ℚ → Option ℚ
  | [],s => some s
  | x::xs,s => do let r ← round64 (s+x);runSum xs r

def chainCheck : List ℚ → ℚ → ℚ → Bool
  | [],s,out => s==out
  | x::xs,s,out => match round64 (s+x) with
    | none => false
    | some r => additionCheck (s+x) r && chainCheck xs r out

theorem chain_sound (xs : List ℚ) (s out : ℚ) (h : chainCheck xs s out=true) :
    FKS2SumBridge.SumRun xs s out := by
  induction xs generalizing s with
  | nil =>
    have he : s=out := by simpa [chainCheck] using h
    subst out
    exact .nil _
  | cons x xs ih =>
    unfold chainCheck at h
    split at h
    · contradiction
    · rename_i r he
      simp only [Bool.and_eq_true] at h
      exact .cons (additionCheck_sound h.1) (ih _ h.2)

theorem kernel_from_chain {xs : List ℚ} {s : ℚ}
    (hc : chainCheck xs 0 s=true) (hn : xs.length≤64) :
    ∃ final,ExecC selectedSumProgram (FKS2SumBridge.sumInitial xs) final s := by
  have hrun := chain_sound xs 0 s hc
  obtain ⟨last,hl,hout⟩ := FKS2SumBridge.run_to_for hrun (FKS2SumBridge.sumInitial xs) rfl
    (by simp [FKS2SumBridge.sumInitial]) rfl (by simp [FKS2SumBridge.sumInitial]) hn
  refine ⟨{last with returned := some last.acc},rfl,last,?_,rfl,hout.symm⟩
  simpa [initialized,FKS2SumBridge.sumInitial] using hl

/-- Restricted selected-sum wrapper; no user-supplied accuracy or output field. -/
structure Program where
  inputs : List String
  scale : String
  fixedOffset : String
  positiveOffset : String
  deriving DecidableEq,Repr

def renderProgram (p : Program) : String :=
  (SumStability.render selectedSumProgram).getD "" ++
  "static const double inputs[" ++ toString p.inputs.length ++ "] = {" ++
  String.intercalate "," p.inputs ++ "};" ++
  "double ramanujan_epsilon_bound(void) { double s = sum(inputs," ++
  toString p.inputs.length ++ "); double r = (s * " ++ p.scale ++ ");" ++
  "r = (r - " ++ p.fixedOffset ++ "); r = (r - " ++ p.positiveOffset ++ "); return r; }"

/-- Existing selected-sum scanner with the one subtraction symbol needed by this wrapper.
All token boundaries, index/loop tokens, and rejection of comments/directives are preserved. -/
def scan : Nat → List Char → Option (List String)
  | 0,_ => none
  | _+1,[] => some []
  | n+1,c::cs => do
    if c.isWhitespace then scan n cs
    else if c.isAlphanum || c=='_' || c=='.' then
      let word := (c::cs).takeWhile (fun x => x.isAlphanum || x=='_' || x=='.')
      return String.ofList word::(←scan n ((c::cs).drop word.length))
    else if c=='+' && cs.head?==some '+' then
      return "++"::(←scan n (cs.drop 1))
    else if c=='+' && cs.head?==some '=' then
      return "+="::(←scan n (cs.drop 1))
    else if ['(',')','{','}','[',']',';','=','+','-','*','<',','].contains c then
      return String.singleton c::(←scan n cs)
    else none

def tokens (s : String) := scan (s.length+1) s.toList

def sourceMatches (src : String) (p : Program) : Bool :=
  let ts := ForwardRamanujan.tokens src
  ts.isSome && ts==ForwardRamanujan.tokens (renderProgram p)

def suffix (p : Program) (s : ℚ) : Option ℚ := do
  let scale ← loadLiteral p.scale
  let fixed ← loadLiteral p.fixedOffset
  let positive ← loadLiteral p.positiveOffset
  let r ← round64 (s*scale)
  let r ← round64 (r-fixed)
  round64 (r-positive)

def SuffixIEEE (p : Program) (s out : ℚ) : Prop :=
  ∃ scale fixed positive r0 r1 : ℚ,
    loadLiteral p.scale=some scale ∧ loadLiteral p.fixedOffset=some fixed ∧
    loadLiteral p.positiveOffset=some positive ∧
    RN64 (s*scale) r0 ∧ RN64 (r0-fixed) r1 ∧ RN64 (r1-positive) out

def Exec (src : String) (p : Program) (initial : CState) (out : ℚ) : Prop :=
  sourceMatches src p=true ∧ 1≤p.inputs.length ∧ p.inputs.length≤64 ∧
  ∃ xs s final,
    p.inputs.mapM loadLiteral=some xs ∧ RepresentsInput initial xs ∧
    runSum xs 0=some s ∧ ExecC selectedSumProgram initial final s ∧
    suffix p s=some out ∧ SuffixIEEE p s out

def forwardError (scale s eps : ℚ) (n : ℕ) : ℚ :=
  scale*(s/(1-gamma (n-1))-s)+eps

theorem output_unique {src : String} {p : Program} {initial : CState}
    {xs : List ℚ} {s q out : ℚ} (he : Exec src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hs : suffix p s=some q) : out=q := by
  obtain ⟨_,_,_,ys,v,final,hy,hrep,hv,hkernel,hout,hIEEE⟩ := he
  have hys : ys=xs := Option.some.inj (hy.symm.trans hl)
  subst ys
  have hvv : v=s := Option.some.inj (hv.symm.trans hr)
  subst v
  exact Option.some.inj (hout.symm.trans hs)

/-- Consumes the actual selected indexed sum execution, with the exact n-1 stability factor. -/
theorem sum_upper {src : String} {p : Program} {initial : CState}
    {xs : List ℚ} {s out : ℚ} (he : Exec src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hn : 1≤xs.length ∧ xs.length≤64) (hd : ValidInputs xs)
    (habs : (xs.map abs).sum=xs.sum) (hg : (gamma (xs.length-1):ℝ)<1) :
    (xs.sum:ℝ) ≤ (s:ℝ)/(1-(gamma (xs.length-1):ℝ)) := by
  obtain ⟨_,_,_,ys,v,final,hy,hrep,hv,hkernel,hout,hIEEE⟩ := he
  have hys : ys=xs := Option.some.inj (hy.symm.trans hl)
  subst ys
  have hvv : v=s := Option.some.inj (hv.symm.trans hr)
  subst v
  have herr := c_sum_forward_error_real xs initial final s hn hd hrep hkernel
  change |(s:ℝ)-(xs.sum:ℚ)| ≤ (gamma (xs.length-1):ℝ)*((xs.map abs).sum:ℚ) at herr
  rw [habs] at herr
  have hlo := (abs_le.mp herr).1
  apply (le_div_iff₀ (by linarith : (0:ℝ)<1-(gamma (xs.length-1):ℝ))).mpr
  nlinarith

/-- Arbitrary modeled output soundness, applied to the actual loaded/operational source instance. -/
theorem source_linked_upper {src : String} {p : Program} {initial : CState}
    {targets xs : List ℚ} {s q out scale fixed positive eps : ℚ}
    (he : Exec src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hs : suffix p s=some q) (hn : 1≤xs.length ∧ xs.length≤64)
    (hd : ValidInputs xs) (habs : (xs.map abs).sum=xs.sum)
    (hg : (gamma (xs.length-1):ℝ)<1) (hscale : 0≤scale)
    (ht : (targets.sum:ℝ) ≤ (scale:ℝ)*(xs.sum:ℝ))
    (hf : |(q:ℝ)-((scale:ℝ)*(s:ℝ)-(fixed:ℝ)-(positive:ℝ))| ≤ (eps:ℝ)) :
    (targets.sum:ℝ)-(fixed:ℝ)-(positive:ℝ) ≤
      (out:ℝ)+(forwardError scale s eps xs.length:ℝ) := by
  have hsum := sum_upper he hl hr hn hd habs hg
  have hm := mul_le_mul_of_nonneg_left hsum
    (show (0:ℝ)≤(scale:ℝ) by exact_mod_cast hscale)
  have hpost := (abs_le.mp hf).1
  rw [output_unique he hl hr hs]
  unfold forwardError
  push_cast at ht hm ⊢
  nlinarith
end ForwardRamanujan

import SumStability.Analysis

namespace SumStability

inductive CExpr where
  | zero64 | accumulator | indexedInput
  | add (left right : CExpr)
  deriving DecidableEq, Repr

inductive CUpdate where
  | plusAssign (value : CExpr)
  deriving DecidableEq, Repr

structure CFor where
  initialIndex : Nat
  unsignedWidth : Nat
  conditionIsLessThanLength : Bool
  increment : Nat
  body : CUpdate
  deriving DecidableEq, Repr

/-- Restricted typed function AST. Its signature is double(const double*, unsigned32). -/
structure CProgram where
  accumulatorInit : CExpr
  loop : CFor
  returnValue : CExpr
  deriving DecidableEq, Repr

def selectedSumProgram : CProgram :=
  ⟨.zero64, ⟨0, 32, true, 1, .plusAssign .indexedInput⟩, .accumulator⟩

def exprText : CExpr → String
  | .zero64 => "0.0"
  | .accumulator => "s"
  | .indexedInput => "a[i]"
  | .add a b => "(" ++ exprText a ++ "+" ++ exprText b ++ ")"

def render (p : CProgram) : Option String := do
  if p.loop.unsignedWidth != 32 || !p.loop.conditionIsLessThanLength ||
      p.loop.increment != 1 then return ← none
  let .plusAssign v := p.loop.body
  return "double sum(const double *a, unsigned n) { double s = " ++
    exprText p.accumulatorInit ++ "; for (unsigned i = " ++ toString p.loop.initialIndex ++
    "; i < n; ++i) { s += " ++ exprText v ++ "; } return " ++ exprText p.returnValue ++ "; }"

def scan : Nat → List Char → Option (List String)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, c :: cs => do
    if c.isWhitespace then scan n cs
    else if c.isAlphanum || c == '_' || c == '.' then
      let word := (c :: cs).takeWhile (fun x => x.isAlphanum || x == '_' || x == '.')
      return String.ofList word :: (← scan n ((c :: cs).drop word.length))
    else if c == '+' && cs.head? == some '+' then
      return "++" :: (← scan n (cs.drop 1))
    else if c == '+' && cs.head? == some '=' then
      return "+=" :: (← scan n (cs.drop 1))
    else if ['(', ')', '{', '}', '[', ']', ';', '=', '+', '*', '<', ','].contains c then
      return String.singleton c :: (← scan n cs)
    else none

def tokens (s : String) := scan (s.length + 1) s.toList

def selectedSource : String := include_str ".."/".."/"sum.c"

def SourceCorresponds (text : String) (p : CProgram) : Prop :=
  ∃ printed, render p = some printed ∧ tokens text = tokens printed ∧ (tokens text).isSome

set_option maxRecDepth 8192 in
/-- Only a finite source/token check; no numerical input enumeration. -/
theorem selected_source_checked : SourceCorresponds selectedSource selectedSumProgram := by
  refine ⟨(render selectedSumProgram).getD "", ?_, ?_, ?_⟩ <;> decide

/-- A typed allocated array object at a byte address; no writes to this object occur. -/
structure CState where
  buffer : List ℚ
  base : Nat
  extent : Nat
  n : Nat
  i : Nat
  acc : ℚ
  returned : Option ℚ
  deriving DecidableEq, Repr

def RepresentsInput (st : CState) (xs : List ℚ) : Prop :=
  st.buffer = xs ∧ st.extent = xs.length ∧ st.n = xs.length ∧
  st.base % 8 = 0 ∧ st.base + 8 * st.extent < 2 ^ 64 ∧ 0 < st.base

def readDouble (st : CState) (address : Nat) : Option ℚ :=
  if st.base ≤ address ∧ (address - st.base) % 8 = 0 then
    st.buffer[(address - st.base) / 8]?
  else none

def advance (st : CState) (r : ℚ) : CState :=
  { st with i := (st.i + 1) % 2 ^ 32, acc := r }

def initialized (st : CState) : CState :=
  { st with i := 0, acc := 0, returned := none }

/-- Big-step interpretation of for(unsigned i=0;i<n;++i){s+=a[i];}.
The guard, actual address load, binary64 add, assignment, and uint32 increment are explicit. -/
inductive ForExec : CState → CState → Prop
  | done (st : CState) (hguard : ¬ st.i < st.n) : ForExec st st
  | step (st : CState) (final : CState) (x r : ℚ)
      (hguard : st.i < st.n)
      (hload : readDouble st (st.base + 8 * st.i) = some x)
      (hadd : RN64 (st.acc + x) r)
      (hrest : ForExec (advance st r) final) : ForExec st final

/-- Dedicated interpretation of the selected restricted AST, not a general ISO C frontend.
The AST selector fixes initialization/body/condition/increment/return; unsupported ASTs reject. -/
def ExecC (p : CProgram) (initial final : CState) (out : ℚ) : Prop :=
  p = selectedSumProgram ∧ ∃ last,
    ForExec (initialized initial) last ∧
    final = { last with returned := some last.acc } ∧ out = last.acc

/-- The source-facing endpoint also records the checked correspondence of this actual file. -/
def ExecSelectedSource (initial final : CState) (out : ℚ) : Prop :=
  SourceCorresponds selectedSource selectedSumProgram ∧ ExecC selectedSumProgram initial final out

theorem read_index (st : CState) :
    readDouble st (st.base + 8 * st.i) = st.buffer[st.i]? := by
  simp [readDouble]

theorem advance_rep {st : CState} {xs : List ℚ} (h : RepresentsInput st xs) (r : ℚ) :
    RepresentsInput (advance st r) xs := h

theorem initialized_rep {st : CState} {xs : List ℚ} (h : RepresentsInput st xs) :
    RepresentsInput (initialized st) xs := h

theorem increment_safe {st : CState} {xs : List ℚ} (hrep : RepresentsInput st xs)
    (hn : xs.length ≤ 64) (hguard : st.i < st.n) (r : ℚ) :
    (advance st r).i = st.i + 1 := by
  have : st.i + 1 < 2 ^ 32 := by have := hrep.2.2.1; omega
  exact Nat.mod_eq_of_lt this

/-- The C loop consumes precisely the input prefix, in increasing index order. -/
theorem for_exec_accum {initial final : CState} (h : ForExec initial final)
    (xs : List ℚ) (hrep : RepresentsInput initial xs) (hn : xs.length ≤ 64)
    (hi : initial.i ≤ initial.n) (ha : Accum (xs.take initial.i) initial.acc) :
    Accum xs final.acc ∧ final.i = final.n ∧ RepresentsInput final xs := by
  induction h with
  | done st hg =>
    have he : st.i = xs.length := by have := hrep.2.2.1; omega
    simpa [he, hrep.2.2.1] using And.intro ha (And.intro he hrep)
  | step st final x r hg hl hr hrest ih =>
    have hidx : st.i < xs.length := by rw [← hrep.2.2.1]; exact hg
    have hload : xs[st.i]? = some x := by
      rw [read_index, hrep.1] at hl
      exact hl
    have hnext : xs.take (st.i + 1) = xs.take st.i ++ [x] := by
      rw [List.take_add_one, hload]
      rfl
    have hincr := increment_safe hrep hn hg r
    apply ih (advance_rep hrep r) ?_ ?_
    · change (advance st r).i ≤ st.n
      rw [hincr]
      omega
    · rw [hincr, hnext]
      exact Accum.step ha hr

/-- Every loop state with a consumed supported prefix satisfies its next-operation safety
conditions. They are consequences of the input/prefix facts, not additional ExecC premises. -/
theorem next_operation_safe {st : CState} {xs : List ℚ}
    (hrep : RepresentsInput st xs) (hn : xs.length ≤ 64) (hd : ValidInputs xs)
    (ha : Accum (xs.take st.i) st.acc) (hg : st.i < st.n) :
    st.i < st.extent ∧ st.base + 8 * st.i < 2 ^ 64 ∧ st.i + 1 < 2 ^ 32 ∧
    ∃ x, readDouble st (st.base + 8 * st.i) = some x ∧ Binary64 x ∧
      low ≤ st.acc + x ∧ st.acc + x ≤ 128 := by
  have hi : st.i < xs.length := by rw [← hrep.2.2.1]; exact hg
  have hx := hd xs[st.i] (List.getElem_mem hi)
  have hprefix : ValidInputs (xs.take st.i) := by
    intro z hz
    exact hd z (List.mem_of_mem_take hz)
  have hlen : (xs.take st.i).length ≤ 64 := by rw [List.length_take_of_le hi.le]; omega
  have hinv := accum_invariant ha hprefix hlen
  have hs : 0 ≤ st.acc ∧ st.acc ≤ 2 * (st.i : ℚ) := by
    by_cases he : xs.take st.i = []
    · have hz := hinv.1 he
      rw [hz]
      constructor <;> positivity
    · have hh := hinv.2 he
      have heq : (xs.take st.i).length = st.i := List.length_take_of_le hi.le
      rw [heq] at hh
      constructor
      · exact le_trans (by norm_num [low]) hh.1
      · exact hh.2.1
  refine ⟨by have := hrep.2.1; omega, ?_, by omega, xs[st.i], ?_, hx.1, ?_, ?_⟩
  · have := hrep.2.2.2.2.1
    have := hrep.2.1
    omega
  · rw [read_index, hrep.1]
    simp [hi]
  · linarith [hx.2.1]
  · have hnq : (st.i : ℚ) ≤ 63 := by exact_mod_cast (show st.i ≤ 63 by omega)
    linarith [hx.2.2]

theorem c_sum_forward_error (xs : List ℚ) (initial final : CState) (out : ℚ)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hdomain : ValidInputs xs)
    (hrep : RepresentsInput initial xs) (hexec : ExecC selectedSumProgram initial final out) :
    |out - xs.sum| ≤ gamma (xs.length - 1) * (xs.map abs).sum := by
  obtain ⟨_, last, hloop, hfinal, hout⟩ := hexec
  have ha : Accum (xs.take (initialized initial).i) (initialized initial).acc := by
    simpa [initialized] using Accum.zero
  have hh := for_exec_accum hloop xs (initialized_rep hrep) hn.2 (by simp [initialized]) ha
  have hne : xs ≠ [] := by intro h; simp [h] at hn
  have hi := (accum_invariant hh.1 hdomain hn.2).2 hne
  rw [hout, sumAbs_eq_sum hdomain]
  exact hi.2.2.2

theorem actual_source_forward_error (xs : List ℚ) (initial final : CState) (out : ℚ)
    (hn : 1 ≤ xs.length ∧ xs.length ≤ 64) (hdomain : ValidInputs xs)
    (hrep : RepresentsInput initial xs) (hexec : ExecSelectedSource initial final out) :
    |out - xs.sum| ≤ gamma (xs.length - 1) * (xs.map abs).sum :=
  c_sum_forward_error xs initial final out hn hdomain hrep hexec.2

end SumStability

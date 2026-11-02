import SumStability.Source

namespace SumStability

theorem rn_self {x : ℚ} (hx : Binary64 x) : RN64 x x := by
  refine ⟨hx, ?_, ?_⟩
  · intro z hz
    simp only [sub_self, abs_zero]
    exact abs_nonneg _
  · rintro ⟨z, hz, hne, he⟩
    have he' : |z - x| = 0 := by simpa using he
    exact False.elim (hne (sub_eq_zero.mp (abs_eq_zero.mp he')))

theorem half_binary64 : Binary64 (1 / 2) := by
  refine ⟨1, -1, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

theorem one_binary64 : Binary64 1 := by
  exact ⟨1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

def stateFor (xs : List ℚ) : CState := ⟨xs, 4096, xs.length, xs.length, 999, 17, some 9⟩

def halfInput : List ℚ := [1 / 2]
def halvesInput : List ℚ := [1 / 2, 1 / 2]

def halfFinal : CState :=
  let last := advance (initialized (stateFor halfInput)) (1 / 2)
  { last with returned := some last.acc }

def halvesFinal : CState :=
  let last := advance (advance (initialized (stateFor halvesInput)) (1 / 2)) 1
  { last with returned := some last.acc }

theorem half_formal_execution :
    ExecSelectedSource (stateFor halfInput) halfFinal (1 / 2) := by
  refine ⟨selected_source_checked, rfl, advance (initialized (stateFor halfInput)) (1 / 2),
    ?_, rfl, rfl⟩
  apply ForExec.step _ _ (1 / 2) (1 / 2)
  · norm_num [initialized, stateFor, halfInput]
  · norm_num [readDouble, initialized, stateFor, halfInput]
  · simpa [initialized] using rn_self half_binary64
  · apply ForExec.done
    norm_num [advance, initialized, stateFor, halfInput]

theorem halves_formal_execution :
    ExecSelectedSource (stateFor halvesInput) halvesFinal 1 := by
  refine ⟨selected_source_checked, rfl,
    advance (advance (initialized (stateFor halvesInput)) (1 / 2)) 1, ?_, rfl, rfl⟩
  apply ForExec.step _ _ (1 / 2) (1 / 2)
  · norm_num [initialized, stateFor, halvesInput]
  · norm_num [readDouble, initialized, stateFor, halvesInput]
  · simpa [initialized] using rn_self half_binary64
  · apply ForExec.step _ _ (1 / 2) 1
    · norm_num [advance, initialized, stateFor, halvesInput]
    · norm_num [readDouble, advance, initialized, stateFor, halvesInput]
    · convert rn_self one_binary64 using 1
      norm_num [advance]
    · apply ForExec.done
      norm_num [advance, initialized, stateFor, halvesInput]

theorem examples_valid : ValidInputs halfInput ∧ ValidInputs halvesInput := by
  constructor <;> intro x hx
  all_goals
    have he : x = 1 / 2 := by simpa [halfInput, halvesInput] using hx
    subst x
    exact ⟨half_binary64, by norm_num [low], by norm_num⟩

theorem examples_represented :
    RepresentsInput (stateFor halfInput) halfInput ∧
    RepresentsInput (stateFor halvesInput) halvesInput := by
  norm_num [RepresentsInput, stateFor, halfInput, halvesInput]

theorem examples_different : halfInput ≠ halvesInput ∧ (1 / 2 : ℚ) ≠ 1 := by
  norm_num [halfInput, halvesInput]

end SumStability

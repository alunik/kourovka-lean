import Kourovka2135.SLTwoFiveGoodSetData

/-! Actual upper/lower elementary generators cover all of SL2(F5).
The explicit 120 finite matrix/word pairs are independently checked by
ordinary decide. The abstract group laws are those of actual SL2, and no
search or group-generation conclusion is assumed. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Kourovka2135.SLTwoFiveGenerationData
open Matrix SLTwoFiveGoodSetData

/-- Exact matrices and words in upper, lower and their inverses. -/
def witness : Fin 120 → S × List (Fin 4) :=
  ![(⟨!![0, 1; 4, 0], by decide⟩, [0, 3, 0]),
    (⟨!![0, 1; 4, 1], by decide⟩, [0, 3]),
    (⟨!![0, 1; 4, 2], by decide⟩, [0, 3, 2]),
    (⟨!![0, 1; 4, 3], by decide⟩, [0, 3, 2, 2]),
    (⟨!![0, 1; 4, 4], by decide⟩, [0, 3, 0, 0]),
    (⟨!![0, 2; 2, 0], by decide⟩, [2, 3, 2, 3, 2]),
    (⟨!![0, 2; 2, 1], by decide⟩, [0, 0, 1, 1]),
    (⟨!![0, 2; 2, 2], by decide⟩, [2, 3, 2, 3]),
    (⟨!![0, 2; 2, 3], by decide⟩, [0, 0, 1, 1, 0]),
    (⟨!![0, 2; 2, 4], by decide⟩, [0, 0, 1, 1, 2]),
    (⟨!![0, 3; 3, 0], by decide⟩, [0, 1, 0, 1, 0]),
    (⟨!![0, 3; 3, 1], by decide⟩, [2, 2, 3, 3]),
    (⟨!![0, 3; 3, 2], by decide⟩, [0, 1, 0, 1]),
    (⟨!![0, 3; 3, 3], by decide⟩, [2, 2, 3, 3, 2]),
    (⟨!![0, 3; 3, 4], by decide⟩, [0, 1, 0, 1, 2]),
    (⟨!![0, 4; 1, 0], by decide⟩, [1, 2, 1]),
    (⟨!![0, 4; 1, 1], by decide⟩, [2, 1]),
    (⟨!![0, 4; 1, 2], by decide⟩, [2, 1, 0]),
    (⟨!![0, 4; 1, 3], by decide⟩, [2, 1, 0, 0]),
    (⟨!![0, 4; 1, 4], by decide⟩, [1, 1, 2, 1]),
    (⟨!![1, 0; 0, 1], by decide⟩, []),
    (⟨!![1, 0; 1, 1], by decide⟩, [1]),
    (⟨!![1, 0; 2, 1], by decide⟩, [1, 1]),
    (⟨!![1, 0; 3, 1], by decide⟩, [3, 3]),
    (⟨!![1, 0; 4, 1], by decide⟩, [3]),
    (⟨!![1, 1; 0, 1], by decide⟩, [0]),
    (⟨!![1, 1; 1, 2], by decide⟩, [1, 0]),
    (⟨!![1, 1; 2, 3], by decide⟩, [1, 1, 0]),
    (⟨!![1, 1; 3, 4], by decide⟩, [3, 3, 0]),
    (⟨!![1, 1; 4, 0], by decide⟩, [3, 0]),
    (⟨!![1, 2; 0, 1], by decide⟩, [0, 0]),
    (⟨!![1, 2; 1, 3], by decide⟩, [1, 0, 0]),
    (⟨!![1, 2; 2, 0], by decide⟩, [1, 1, 0, 0]),
    (⟨!![1, 2; 3, 2], by decide⟩, [3, 3, 0, 0]),
    (⟨!![1, 2; 4, 4], by decide⟩, [3, 0, 0]),
    (⟨!![1, 3; 0, 1], by decide⟩, [2, 2]),
    (⟨!![1, 3; 1, 4], by decide⟩, [1, 2, 2]),
    (⟨!![1, 3; 2, 2], by decide⟩, [1, 1, 2, 2]),
    (⟨!![1, 3; 3, 0], by decide⟩, [3, 3, 2, 2]),
    (⟨!![1, 3; 4, 3], by decide⟩, [3, 2, 2]),
    (⟨!![1, 4; 0, 1], by decide⟩, [2]),
    (⟨!![1, 4; 1, 0], by decide⟩, [1, 2]),
    (⟨!![1, 4; 2, 4], by decide⟩, [1, 1, 2]),
    (⟨!![1, 4; 3, 3], by decide⟩, [3, 3, 2]),
    (⟨!![1, 4; 4, 2], by decide⟩, [3, 2]),
    (⟨!![2, 0; 0, 3], by decide⟩, [0, 0, 3, 3, 2, 3]),
    (⟨!![2, 0; 1, 3], by decide⟩, [0, 1, 0, 0]),
    (⟨!![2, 0; 2, 3], by decide⟩, [2, 2, 1, 1, 0]),
    (⟨!![2, 0; 3, 3], by decide⟩, [0, 0, 3, 3, 2]),
    (⟨!![2, 0; 4, 3], by decide⟩, [2, 3, 2, 2]),
    (⟨!![2, 1; 0, 3], by decide⟩, [1, 1, 0, 1]),
    (⟨!![2, 1; 1, 1], by decide⟩, [0, 1]),
    (⟨!![2, 1; 2, 4], by decide⟩, [3, 2, 3, 0]),
    (⟨!![2, 1; 3, 2], by decide⟩, [1, 0, 1]),
    (⟨!![2, 1; 4, 0], by decide⟩, [2, 3, 0]),
    (⟨!![2, 2; 0, 3], by decide⟩, [0, 3, 3, 2, 3]),
    (⟨!![2, 2; 1, 4], by decide⟩, [0, 1, 2, 2]),
    (⟨!![2, 2; 2, 0], by decide⟩, [3, 2, 3, 2]),
    (⟨!![2, 2; 3, 1], by decide⟩, [0, 0, 3, 3]),
    (⟨!![2, 2; 4, 2], by decide⟩, [2, 3, 2]),
    (⟨!![2, 3; 0, 3], by decide⟩, [1, 1, 0, 1, 0]),
    (⟨!![2, 3; 1, 2], by decide⟩, [0, 1, 0]),
    (⟨!![2, 3; 2, 1], by decide⟩, [2, 2, 1, 1]),
    (⟨!![2, 3; 3, 0], by decide⟩, [1, 0, 1, 0]),
    (⟨!![2, 3; 4, 4], by decide⟩, [2, 3, 0, 0]),
    (⟨!![2, 4; 0, 3], by decide⟩, [3, 3, 2, 3]),
    (⟨!![2, 4; 1, 0], by decide⟩, [0, 1, 2]),
    (⟨!![2, 4; 2, 2], by decide⟩, [3, 2, 3]),
    (⟨!![2, 4; 3, 4], by decide⟩, [1, 0, 1, 2]),
    (⟨!![2, 4; 4, 1], by decide⟩, [2, 3]),
    (⟨!![3, 0; 0, 2], by decide⟩, [0, 0, 1, 0, 1, 1]),
    (⟨!![3, 0; 1, 2], by decide⟩, [0, 0, 1, 0]),
    (⟨!![3, 0; 2, 2], by decide⟩, [0, 1, 1, 2, 2]),
    (⟨!![3, 0; 3, 2], by decide⟩, [0, 0, 1, 0, 1]),
    (⟨!![3, 0; 4, 2], by decide⟩, [2, 2, 3, 2]),
    (⟨!![3, 1; 0, 2], by decide⟩, [1, 0, 1, 1]),
    (⟨!![3, 1; 1, 4], by decide⟩, [0, 0, 1, 2, 2]),
    (⟨!![3, 1; 2, 1], by decide⟩, [0, 1, 1]),
    (⟨!![3, 1; 3, 3], by decide⟩, [2, 3, 3, 2]),
    (⟨!![3, 1; 4, 0], by decide⟩, [2, 2, 3, 0]),
    (⟨!![3, 2; 0, 2], by decide⟩, [2, 3, 2, 3, 3]),
    (⟨!![3, 2; 1, 1], by decide⟩, [0, 0, 1]),
    (⟨!![3, 2; 2, 0], by decide⟩, [0, 1, 1, 0, 0]),
    (⟨!![3, 2; 3, 4], by decide⟩, [2, 3, 3, 0]),
    (⟨!![3, 2; 4, 3], by decide⟩, [1, 0, 0, 1]),
    (⟨!![3, 3; 0, 2], by decide⟩, [0, 1, 0, 1, 1]),
    (⟨!![3, 3; 1, 3], by decide⟩, [3, 2, 2, 3]),
    (⟨!![3, 3; 2, 4], by decide⟩, [0, 1, 1, 2]),
    (⟨!![3, 3; 3, 0], by decide⟩, [2, 3, 3, 2, 2]),
    (⟨!![3, 3; 4, 1], by decide⟩, [2, 2, 3]),
    (⟨!![3, 4; 0, 2], by decide⟩, [3, 2, 3, 3]),
    (⟨!![3, 4; 1, 0], by decide⟩, [0, 0, 1, 2]),
    (⟨!![3, 4; 2, 3], by decide⟩, [0, 1, 1, 0]),
    (⟨!![3, 4; 3, 1], by decide⟩, [2, 3, 3]),
    (⟨!![3, 4; 4, 4], by decide⟩, [1, 0, 0, 1, 2]),
    (⟨!![4, 0; 0, 4], by decide⟩, [0, 0, 3, 0, 0, 3]),
    (⟨!![4, 0; 1, 4], by decide⟩, [1, 2, 1, 1, 2]),
    (⟨!![4, 0; 2, 4], by decide⟩, [2, 1, 1, 2]),
    (⟨!![4, 0; 3, 4], by decide⟩, [0, 3, 3, 0]),
    (⟨!![4, 0; 4, 4], by decide⟩, [0, 0, 3, 0, 0]),
    (⟨!![4, 1; 0, 4], by decide⟩, [0, 3, 0, 0, 3]),
    (⟨!![4, 1; 1, 3], by decide⟩, [0, 3, 2, 2, 3]),
    (⟨!![4, 1; 2, 2], by decide⟩, [0, 3, 2, 3]),
    (⟨!![4, 1; 3, 1], by decide⟩, [0, 3, 3]),
    (⟨!![4, 1; 4, 0], by decide⟩, [0, 0, 3, 0]),
    (⟨!![4, 2; 0, 4], by decide⟩, [3, 0, 0, 3]),
    (⟨!![4, 2; 1, 2], by decide⟩, [2, 2, 1, 0]),
    (⟨!![4, 2; 2, 0], by decide⟩, [0, 3, 2, 3, 2]),
    (⟨!![4, 2; 3, 3], by decide⟩, [0, 3, 3, 2]),
    (⟨!![4, 2; 4, 1], by decide⟩, [0, 0, 3]),
    (⟨!![4, 3; 0, 4], by decide⟩, [1, 2, 2, 1]),
    (⟨!![4, 3; 1, 1], by decide⟩, [2, 2, 1]),
    (⟨!![4, 3; 2, 3], by decide⟩, [2, 1, 1, 0]),
    (⟨!![4, 3; 3, 0], by decide⟩, [0, 3, 3, 2, 2]),
    (⟨!![4, 3; 4, 2], by decide⟩, [0, 0, 3, 2]),
    (⟨!![4, 4; 0, 4], by decide⟩, [1, 1, 2, 1, 1]),
    (⟨!![4, 4; 1, 0], by decide⟩, [1, 2, 1, 1]),
    (⟨!![4, 4; 2, 1], by decide⟩, [2, 1, 1]),
    (⟨!![4, 4; 3, 2], by decide⟩, [2, 1, 0, 1]),
    (⟨!![4, 4; 4, 3], by decide⟩, [0, 0, 3, 2, 2]) ]

/-- Every displayed word evaluates to its displayed actual matrix. -/
theorem all_words (i : Fin 120) :
    eval upper lower (witness i).2 = (witness i).1 := by
  fin_cases i <;> decide

/-- The displayed actual matrices cover the actual determinant-one group. -/
theorem targets_complete : ∀ g : S, ∃ i : Fin 120, (witness i).1 = g := by decide

/-- Actual elementary-generator word coverage, with no generation premise. -/
theorem exists_word (g : S) :
    ∃ i : Fin 120, eval upper lower (witness i).2 = g := by
  obtain ⟨i, hi⟩ := targets_complete g
  exact ⟨i, (all_words i).trans hi⟩

end Kourovka2135.SLTwoFiveGenerationData

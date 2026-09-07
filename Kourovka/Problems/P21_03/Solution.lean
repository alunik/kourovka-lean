import Kourovka.Problems.P21_03.Statement
import Kourovka.Problems.P21_03.Proof.AlternatingAsymptotic

/-!
# Solution of Problem 21.3, first question

The uniform symmetric-group success probability tends to `exp (-9 / 2)`.
The alternating-group argument supplies even conjugators. Together these
give a single cutoff independent of the chosen soluble subgroups.
-/

namespace Kourovka.P21_03

/-- An affirmative answer to the first question, for both `S_n` and `A_n`. -/
theorem firstQuestion : FirstQuestion := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp Kourovka213.eventually_kourovka213
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hSym, hAlt⟩ := hN n hn
  constructor
  · intro H K hH hK
    exact hSym ⟨H, hH⟩ ⟨K, hK⟩
  · intro H K hH hK hHA hKA
    exact hAlt ⟨H, hH⟩ ⟨K, hK⟩ hHA hKA

end Kourovka.P21_03

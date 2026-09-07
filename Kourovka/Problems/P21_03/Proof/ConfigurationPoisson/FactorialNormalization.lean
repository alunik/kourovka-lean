import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Fixed-support factorial normalization
-/

open Filter Asymptotics
open scoped Topology

namespace Kourovka213

/-- For fixed support size, the factorial completion ratio differs from
`n^s` only by a factor tending to one. -/
theorem tendsto_factorial_normalization (s : ℕ) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) ^ s * ((n - s).factorial : ℝ) / (n.factorial : ℝ))
      atTop (nhds 1) := by
  have hequiv := (isEquivalent_descFactorial s).symm
  have hz : ∀ᶠ n : ℕ in atTop, (n.descFactorial s : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop s] with n hn
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hn))
  have hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ s / (n.descFactorial s : ℝ))
      atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hz).mp hequiv
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop s] with n hn
  have hfactNat := Nat.factorial_mul_descFactorial hn
  have hfact :
      ((n - s).factorial : ℝ) * (n.descFactorial s : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hsubfac : ((n - s).factorial : ℝ) ≠ 0 := by positivity
  have hdesc : (n.descFactorial s : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hn))
  rw [← hfact]
  field_simp

end Kourovka213

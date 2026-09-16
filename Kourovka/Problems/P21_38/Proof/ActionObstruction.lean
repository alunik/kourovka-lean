import Kourovka.Problems.P21_38.Proof.Spread
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# The fixed-point obstruction to spread two

This is the general action argument behind Golan Polak,
*The "spread" of Thompson's group F*, Lemma 2 and Remark 11 (2024).
The proof below is independent of Thompson's group and of its generation theorem.
-/

namespace Kourovka.P21_38

variable {G X : Type*} [Group G] [MulAction G X]

/-- Two elements fixing a point cannot generate if some group element moves it. -/
theorem not_generatesPair_of_fixed_point {a b : G} {z : X}
    (ha : a • z = z) (hb : b • z = z)
    (hmoved : ∃ g : G, g • z ≠ z) : ¬ GeneratesPair a b := by
  intro hgen
  obtain ⟨g, hg⟩ := hmoved
  have hle : Subgroup.closure ({a, b} : Set G) ≤ MulAction.stabilizer G z := by
    apply (Subgroup.closure_le _).mpr
    intro c hc
    rcases Set.mem_insert_iff.mp hc with rfl | hc
    · exact ha
    · have hcb : c = b := Set.mem_singleton_iff.mp hc
      simpa [hcb] using hb
  have hgmem : g ∈ Subgroup.closure ({a, b} : Set G) := by
    rw [hgen]
    trivial
  exact hg (hle hgmem)

/-- A fixed pair with covering fixed sets has no common companion. -/
theorem no_common_companion_of_fixed_points {a b : G}
    (hfixed : ∀ y : G, ∃ z : X, y • z = z)
    (hmoved : ∀ z : X, ∃ g : G, g • z ≠ z)
    (hcover : ∀ z : X, a • z = z ∨ b • z = z) :
    ∀ y : G, ¬ (GeneratesPair a y ∧ GeneratesPair b y) := by
  intro y hgen
  obtain ⟨z, hz⟩ := hfixed y
  rcases hcover z with ha | hb
  · exact not_generatesPair_of_fixed_point ha hz (hmoved z) hgen.1
  · exact not_generatesPair_of_fixed_point hb hz (hmoved z) hgen.2

/-- The action obstruction, with all quantifiers and nonidentity conditions explicit. -/
theorem not_hasSpreadAtLeast_two_of_fixed_points {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1)
    (hfixed : ∀ y : G, ∃ z : X, y • z = z)
    (hmoved : ∀ z : X, ∃ g : G, g • z ≠ z)
    (hcover : ∀ z : X, a • z = z ∨ b • z = z) :
    ¬ HasSpreadAtLeast G 2 := by
  intro hspread
  obtain ⟨y, hy⟩ := hasSpreadAtLeast_two_iff.mp hspread a b ha hb
  exact no_common_companion_of_fixed_points hfixed hmoved hcover y hy

end Kourovka.P21_38

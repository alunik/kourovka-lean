import Kourovka.Problems.P21_38.Proof.ActionObstruction
import Kourovka.Problems.P21_38.Proof.EndpointSlopes
import Kourovka.Problems.P21_38.Proof.LocalSupport
import Kourovka.Problems.P21_38.Proof.RationalPLFixedPoint
import Mathlib.Order.Iterate

/-!
# The concrete diagonal subgroup does not have spread two

The action is on the open rational unit interval. Equal endpoint exponents
give a rational fixed point by finite affine interpolation. Concrete elements
of the compact core move every point, and two such elements have covering
fixed sets. These facts establish the upper bound independently of any
prescribed-generation theorem.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- The open unit interval of rational points. -/
abbrev Interior : Type := {z : ℚ // 0 < z ∧ z < 1}

theorem f_preserves_interior (g : F) {z : ℚ} (hz : 0 < z ∧ z < 1) :
    0 < g.1 z ∧ g.1 z < 1 := by
  have hmono := compactF_strictMono g.property
  have h0 := hmono hz.1
  have h1 := hmono hz.2
  rw [compactF_fix_nonpos g.property (le_refl 0)] at h0
  rw [compactF_fix_one g.property (le_refl 1)] at h1
  exact ⟨h0, h1⟩

/-- The concrete PL action preserves the open unit interval. -/
instance fInteriorAction : MulAction F Interior where
  smul g z := ⟨g.1 z.1, f_preserves_interior g z.property⟩
  one_smul z := by apply Subtype.ext; rfl
  mul_smul g h z := by apply Subtype.ext; rfl

@[simp] theorem f_smul_interior_val (g : F) (z : Interior) :
    (g • z).1 = g.1 z.1 := rfl

@[simp] theorem diagonal_smul_interior_val (g : diagonalSubgroup) (z : Interior) :
    (g • z).1 = g.1.1 z.1 := rfl

/-- Every element of the diagonal subgroup has an interior rational fixed point. -/
theorem diagonal_has_interior_fixedPoint (g : diagonalSubgroup) :
    ∃ z : ℚ, 0 < z ∧ z < 1 ∧ g.1.1 z = z := by
  obtain ⟨ε, hε, hl⟩ := leftExponent_spec g.1
  obtain ⟨η, hη, hr⟩ := rightExponent_spec g.1
  have hsame : leftExponent g.1 = rightExponent g.1 := g.property
  rw [← hsame] at hr
  obtain ⟨N, B, hgrid⟩ := g.1.property.1.2.1
  let δ : ℚ := min (min ε η) (1 / 4)
  have hδ : 0 < δ := lt_min (lt_min hε hη) (by norm_num)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η := (min_le_left _ _).trans (min_le_right _ _)
  have hδhalf : δ < 1 / 2 :=
    (min_le_right _ _).trans_lt (by norm_num)
  apply rational_grid_affine_interior_fixedPoint hgrid hδ hδhalf
    (slope := (2 : ℚ) ^ leftExponent g.1)
  · intro t ht0 htδ
    exact hl t ht0.le (htδ.le.trans hδε)
  · intro t htδ ht1
    exact hr t (by linarith) ht1.le

theorem diagonal_action_has_fixedPoint (g : diagonalSubgroup) :
    ∃ z : Interior, g • z = z := by
  obtain ⟨z, hz0, hz1, hfixed⟩ := diagonal_has_interior_fixedPoint g
  exact ⟨⟨z, hz0, hz1⟩, Subtype.ext hfixed⟩

/-- Insert an actual compact-core permutation into the diagonal subgroup. -/
def diagonalOfCore (g : Equiv.Perm ℚ) (hg : g ∈ compactCore 0) : diagonalSubgroup :=
  ⟨⟨g, compactCore_le hg⟩, mem_diagonalSubgroup_of_mem_compactCore hg⟩

@[simp] theorem diagonalOfCore_val (g : Equiv.Perm ℚ) (hg : g ∈ compactCore 0) :
    (diagonalOfCore g hg).1.1 = g := rfl

theorem diagonalOfCore_ne_one {g : Equiv.Perm ℚ} (hg : g ∈ compactCore 0)
    (hne : g ≠ 1) : diagonalOfCore g hg ≠ 1 := by
  intro h
  exact hne (congrArg (fun y : diagonalSubgroup => y.1.1) h)

/-- The diagonal subgroup has no global fixed point in the open interval. -/
theorem diagonal_action_moves_every_point (z : Interior) :
    ∃ g : diagonalSubgroup, g • z ≠ z := by
  obtain ⟨g, hg, hmove⟩ := exists_core_move z.property.1 z.property.2
  refine ⟨diagonalOfCore g hg, ?_⟩
  intro hfixed
  exact hmove (congrArg Subtype.val hfixed)

/-- The two bump maps are nonidentity elements of the concrete subgroup,
and every interior point is fixed by at least one of them. -/
theorem diagonal_exists_pair_covering_fixed_sets :
    ∃ a b : diagonalSubgroup, a ≠ 1 ∧ b ≠ 1 ∧
      ∀ z : Interior, a • z = z ∨ b • z = z := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hcover⟩ := exists_core_pair_covering_fixed_sets
  refine ⟨diagonalOfCore a ha, diagonalOfCore b hb,
    diagonalOfCore_ne_one ha ha1, diagonalOfCore_ne_one hb hb1, ?_⟩
  intro z
  rcases hcover z.1 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- A concrete pair in the diagonal subgroup has no common generating companion. -/
theorem diagonal_exists_pair_no_common_companion :
    ∃ a b : diagonalSubgroup, a ≠ 1 ∧ b ≠ 1 ∧
      ∀ y : diagonalSubgroup, ¬ (GeneratesPair a y ∧ GeneratesPair b y) := by
  obtain ⟨a, b, ha, hb, hcover⟩ := diagonal_exists_pair_covering_fixed_sets
  exact ⟨a, b, ha, hb, no_common_companion_of_fixed_points
    diagonal_action_has_fixedPoint diagonal_action_moves_every_point hcover⟩

/-- The concrete equal-endpoint subgroup of Thompson's group has spread at most one. -/
theorem diagonal_not_hasSpreadAtLeast_two : ¬ HasSpreadAtLeast diagonalSubgroup 2 := by
  obtain ⟨a, b, ha, hb, hcover⟩ := diagonal_exists_pair_covering_fixed_sets
  exact not_hasSpreadAtLeast_two_of_fixed_points ha hb
    diagonal_action_has_fixedPoint diagonal_action_moves_every_point hcover

/-- A nontrivial increasing permutation has distinct iterates at a moved point,
so the concrete diagonal subgroup is infinite. -/
theorem diagonal_infinite : Infinite diagonalSubgroup := by
  obtain ⟨h, hh, hmove⟩ := exists_core_move
    (show (0 : ℚ) < 1 / 2 by norm_num) (show (1 / 2 : ℚ) < 1 by norm_num)
  let g : diagonalSubgroup := diagonalOfCore h hh
  have hmono : StrictMono h := compactF_strictMono (compactCore_le hh)
  have hseq : Function.Injective (fun n : ℕ => h^[n] (1 / 2 : ℚ)) := by
    rcases lt_or_gt_of_ne hmove with hlt | hgt
    · exact (hmono.strictAnti_iterate_of_map_lt hlt).injective
    · exact (hmono.strictMono_iterate_of_lt_map hgt).injective
  apply Infinite.of_injective (fun n : ℕ => g ^ n)
  intro m n hpow
  apply hseq
  have heq := congrArg (fun y : diagonalSubgroup => y.1.1 (1 / 2 : ℚ)) hpow
  change (h ^ m) (1 / 2 : ℚ) = (h ^ n) (1 / 2 : ℚ) at heq
  simpa only [Equiv.Perm.coe_pow] using heq

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.diagonal_has_interior_fixedPoint
#audit_axioms Kourovka.P21_38.diagonal_exists_pair_no_common_companion
#audit_axioms Kourovka.P21_38.diagonal_not_hasSpreadAtLeast_two
#audit_axioms Kourovka.P21_38.diagonal_infinite

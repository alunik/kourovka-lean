import Kourovka2135.RelativeCommutatorCharacter
import Kourovka2135.RelativeCommutatorMatrix
import Kourovka2135.OneDimensionalCharacter
import Kourovka2135.LinearCharacterCorrectionAverage
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Nonempty relative commutator fibers from actual extensions with trace one.
The linear character sums are proved from the moving-kernel and generation
conditions. Nonlinear extensions are a visible input to this generic bridge;
the family application constructs them separately.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RelativeCommutatorFiber

open scoped BigOperators
open CharacterPositivity RelativeCommutatorCharacter
attribute [local instance] Fintype.ofFinite

variable {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]

omit [N.Normal] in
private theorem sumCharacter_pair
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ N V) (X : N × N → N) :
    sumCharacter ρ X = ∑ u : N, ∑ v : N, ρ.character (X (u, v)) := by
  unfold sumCharacter
  calc
    _ = ∑ uv : N × N, ρ.character (X uv) := by
      apply Finset.sum_congr
      · ext; simp
      · intro uv _; rfl
    _ = _ := Fintype.sum_prod_type _

/-- Every actual degree-one character gives a nonnegative correction sum. -/
theorem linear_nonnegative
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (n : N)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ N V) (hdim : Module.finrank ℂ V = 1) :
    0 ≤ (sumCharacter ρ (correction N a b n)).re := by
  classical
  let : Fintype N := Fintype.ofFinite N
  let χ := OneDimensionalCharacter.characterHom ρ
  have hχval (x : N) : (χ x : ℂ) = ρ.character x :=
    OneDimensionalCharacter.characterHom_val_eq_character ρ hdim x
  by_cases hχ : χ = 1
  · have hchar (x : N) : ρ.character x = 1 :=
      OneDimensionalCharacter.character_eq_one_of_characterHom_eq_one ρ hdim hχ x
    simp [sumCharacter, hchar]
  · have hzero := LinearCharacterCorrectionAverage.correction_sum_eq_zero
      N χ hχ hmove a b hgen
    have hsum : sumCharacter ρ (correction N a b n) = 0 := by
      rw [sumCharacter_pair]
      simp_rw [← hχval, correction, map_mul, Units.val_mul]
      calc
        (∑ u : N, ∑ v : N,
            (χ n⁻¹ : ℂ) * (χ (abelianCorrection N a b u v) : ℂ)) =
            (χ n⁻¹ : ℂ) * ∑ u : N, ∑ v : N,
              (χ (abelianCorrection N a b u v) : ℂ) := by
          simp only [Finset.mul_sum]
        _ = 0 := by rw [hzero, mul_zero]
    rw [hsum, Complex.zero_re]

/-- A genuine nonlinear extension with trace one gives the exact positive scalar sum. -/
theorem nonlinear_sum
    (a b : G) (n : N)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ N V) [ρ.IsIrreducible]
    (α : Representation ℂ G V) (hα : α.comp N.subtype = ρ)
    (htrace : α.character (paperCommutator a b * (n : G))⁻¹ = 1) :
    sumCharacter ρ (correction N a b n) =
      ((Fintype.card N : ℂ) / (Module.finrank ℂ V : ℂ)) ^ 2 := by
  classical
  let : Fintype N := Fintype.ofFinite N
  have hrestrict (x : N) : α (x : G) = ρ x := DFunLike.congr_fun hα x
  have hchar (x : N) : ρ.character x = α.character (x : G) := by
    unfold Representation.character
    rw [hrestrict]
  rw [sumCharacter_pair]
  simp_rw [hchar, correction_coe]
  rw [RelativeCommutatorMatrix.sum_character_inv_mul_paperCommutator
    N ρ α hrestrict a b (paperCommutator a b * (n : G)), htrace, mul_one]

/-- Actual extensions discharge the nonlinear inequalities; positivity produces
an actual pair in the desired paper-commutator fiber. -/
theorem exists_paperCommutator_eq
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (n : N)
    (hext : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ N V), ρ.IsIrreducible → Module.finrank ℂ V ≠ 1 →
        ∃ α : Representation ℂ G V, α.comp N.subtype = ρ ∧
          α.character (paperCommutator a b * (n : G))⁻¹ = 1) :
    ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) =
      paperCommutator a b * (n : G) := by
  apply exists_paperCommutator_eq_of_character_nonnegative N a b n
  intro V _ _ _ ρ hirred
  let : ρ.IsIrreducible := hirred
  by_cases hdim : Module.finrank ℂ V = 1
  · exact linear_nonnegative N hmove a b hgen n ρ hdim
  · obtain ⟨α, hα, htrace⟩ := hext V ρ hirred hdim
    rw [nonlinear_sum N a b n ρ α hα htrace]
    have heq : ((Fintype.card N : ℂ) / (Module.finrank ℂ V : ℂ)) ^ 2 =
        (((Fintype.card N : ℝ) / (Module.finrank ℂ V : ℝ)) ^ 2 : ℝ) := by
      push_cast
      rfl
    rw [heq, Complex.ofReal_re]
    positivity

end Kourovka2135.RelativeCommutatorFiber

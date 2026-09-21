import Kourovka2135.AbelianCommutatorFiber
import Kourovka2135.CharacterPositivity

/-! Actual relative correction elements in a normal subgroup. The identity
criterion for this finite family gives the desired paper-commutator fiber.
No surjectivity or Fourier identity is assumed in the construction.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RelativeCommutatorCharacter

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def correction (a b : G) (n : N) (uv : N × N) : N :=
  n⁻¹ * abelianCorrection N a b uv.1 uv.2

theorem correction_coe (a b : G) (n : N) (uv : N × N) :
    (correction N a b n uv : G) =
      (paperCommutator a b * (n : G))⁻¹ *
        paperCommutator (a * (uv.1 : G)) (b * (uv.2 : G)) := by
  rw [paperCommutator_mul_eq_correction]
  change (n : G)⁻¹ * (abelianCorrection N a b uv.1 uv.2 : G) = _
  group

theorem correction_eq_one_iff (a b : G) (n : N) (uv : N × N) :
    correction N a b n uv = 1 ↔
      paperCommutator (a * (uv.1 : G)) (b * (uv.2 : G)) =
        paperCommutator a b * (n : G) := by
  constructor
  · intro h
    have hv := congrArg (fun x : N => (x : G)) h
    rw [correction_coe] at hv
    exact (inv_mul_eq_one.mp hv).symm
  · intro h
    apply Subtype.ext
    change (correction N a b n uv : G) = 1
    rw [correction_coe, h, inv_mul_cancel]

/-- Actual nonnegative irreducible character sums imply an actual correction pair. -/
theorem exists_paperCommutator_eq_of_character_nonnegative [Finite G]
    (a b : G) (n : N)
    (h : CharacterPositivity.IrreducibleNonnegative (correction N a b n)) :
    ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) =
      paperCommutator a b * (n : G) := by
  obtain ⟨uv, huv⟩ := CharacterPositivity.exists_eq_one_of_irreducible_nonnegative
    (correction N a b n) h
  exact ⟨uv.1, uv.2, (correction_eq_one_iff N a b n uv).mp huv⟩

end Kourovka2135.RelativeCommutatorCharacter

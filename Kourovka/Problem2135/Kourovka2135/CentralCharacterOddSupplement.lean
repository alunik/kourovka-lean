import Kourovka2135.FiniteActionCharacterAveraging
import Kourovka2135.InvariantCharacterSupExtension

/-! Extend a character of an actual central subgroup across an abelian binary
subgroup and an odd normalizing supplement. Averaging, the semidirect product,
and the uniform binary exponent of the resulting image are all constructed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CentralCharacterOddSupplement

open scoped IsMulCommutative
open InvariantCharacterSupExtension

variable {G k : Type*} [Group G] [Finite G] [Field k] [IsAlgClosed k]

/-- The character extends to the actual join, is trivial on the supplement,
and has image killed by a single power of two. -/
theorem exists_extension
    (Z A C : Subgroup G) [IsMulCommutative A]
    (hZA : Z ≤ A) (hZ : Z ≤ Subgroup.center G)
    (hA : IsPGroup 2 A) (hC : Nat.Coprime 2 (Nat.card C))
    (hnorm : C ≤ Subgroup.normalizer A) (hdisjoint : Disjoint A C)
    (χ₀ : Z →* kˣ) :
    ∃ χ : ↥(A ⊔ C) →* kˣ,
      χ.comp (Subgroup.inclusion (hZA.trans le_sup_left)) = χ₀ ∧
      χ.comp (Subgroup.inclusion (show C ≤ A ⊔ C from le_sup_right)) = 1 ∧
      ∃ r : ℕ, ∀ s : ↥(A ⊔ C), χ s ^ (2 ^ r) = 1 := by
  let : IsMulCommutative Z :=
    ⟨⟨fun z w => Subtype.ext (Subgroup.mem_center_iff.mp (hZ z.property) (w : G)).symm⟩⟩
  let i : Z →* A := Subgroup.inclusion hZA
  have hi : Function.Injective i := Subgroup.inclusion_injective hZA
  have hfix : ∀ (c : C) (z : Z), action A C hnorm c (i z) = i z := by
    intro c z
    apply Subtype.ext
    change (c : G) * (z : G) * (c : G)⁻¹ = (z : G)
    rw [Subgroup.mem_center_iff.mp (hZ z.property) (c : G)]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨ψ, hψ, hψinv⟩ := FiniteActionCharacterAveraging.exists_extension
    (action A C hnorm) hA hC i hi hfix χ₀
  let χ : ↥(A ⊔ C) →* kˣ := extension A C hnorm ψ hψinv hdisjoint
  refine ⟨χ, ?_, extension_comp_right A C hnorm ψ hψinv hdisjoint, ?_⟩
  · apply MonoidHom.ext
    intro z
    change χ (Subgroup.inclusion le_sup_left (i z)) = χ₀ z
    rw [extension_left]
    exact DFunLike.congr_fun hψ z
  · obtain ⟨r, hr⟩ := isPGroup_iff_exists_orderOf_dvd_pow.mp hA
    refine ⟨r, fun s => ?_⟩
    obtain ⟨x, hx⟩ := toSup_surjective A C hnorm s
    have hχ : χ s = ψ x.left := by
      rw [← hx]
      exact extension_apply_mul A C hnorm ψ hψinv hdisjoint x.left x.right
    rw [hχ, ← map_pow, orderOf_dvd_iff_pow_eq_one.mp (hr x.left), map_one]

end Kourovka2135.CentralCharacterOddSupplement

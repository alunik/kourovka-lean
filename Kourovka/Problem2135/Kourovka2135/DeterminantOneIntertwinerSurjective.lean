import Kourovka2135.DeterminantOneIntertwinerGroup
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Actual normalization of intertwiners to determinant one.

For a nonzero finite-dimensional coefficient space, choose a root of
the inverse determinant and multiply the actual operator by that scalar.
The zero-dimensional case is handled separately. Surjectivity of the
actual determinant-one cover follows from honest existence of actual
conjugation intertwiners or representation equivalences.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.DeterminantOneIntertwinerSurjective

open DeterminantOneIntertwinerGroup

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (ρ : Representation k N V)

/-- Scalar multiplication of the actual linear automorphism. -/
def scale (a : kˣ) (T : V ≃ₗ[k] V) : V ≃ₗ[k] V :=
  (LinearEquiv.smulOfUnit a) * T

@[simp] theorem scale_toLinearMap (a : kˣ) (T : V ≃ₗ[k] V) :
    (scale a T).toLinearMap = (a : k) • T.toLinearMap := by
  apply LinearMap.ext
  intro v
  rfl

/-- Multiplying an actual intertwiner by a nonzero scalar preserves its equation. -/
theorem scale_intertwines (g : G) (a : kˣ) (T : V ≃ₗ[k] V)
    (hT : Intertwines N ρ g T) : Intertwines N ρ g (scale a T) := by
  intro n
  rw [scale_toLinearMap, LinearMap.smul_comp, LinearMap.comp_smul, hT n]

/-- The actual determinant changes by the scalar raised to the coefficient dimension. -/
theorem scale_det_val (a : kˣ) (T : V ≃ₗ[k] V) :
    (LinearEquiv.det (scale a T) : k) =
      (a : k) ^ Module.finrank k V * (LinearEquiv.det T : k) := by
  rw [LinearEquiv.coe_det, scale_toLinearMap, LinearMap.det_smul, LinearEquiv.coe_det]

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- Normalize the actual operator, without assuming a chosen root or
excluding the zero-dimensional coefficient space. -/
theorem exists_detOne_intertwiner (g : G) (T : V ≃ₗ[k] V)
    (hT : Intertwines N ρ g T) :
    ∃ U : V ≃ₗ[k] V, Intertwines N ρ g U ∧ LinearEquiv.det U = 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · let : Subsingleton V := hV
    have hT1 : T = 1 := by
      apply LinearEquiv.ext
      intro v
      exact Subsingleton.elim _ _
    exact ⟨T, hT, by rw [hT1, map_one]⟩
  · let : Nontrivial V := hV
    have hd : 0 < Module.finrank k V := Module.finrank_pos
    let δ : k := (LinearEquiv.det T : k)
    have hδ : δ ≠ 0 := (LinearEquiv.det T).ne_zero
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq δ⁻¹ hd
    have ha0 : a ≠ 0 := by
      intro hz
      apply inv_ne_zero hδ
      rw [← ha, hz, zero_pow hd.ne']
    let u : kˣ := Units.mk0 a ha0
    refine ⟨scale u T, scale_intertwines N ρ g u T hT, ?_⟩
    apply Units.ext
    rw [scale_det_val, Units.val_one]
    change a ^ Module.finrank k V * δ = 1
    rw [ha, inv_mul_cancel₀ hδ]

/-- Honest actual intertwiner existence gives surjectivity of the actual
determinant-one cover projection. -/
theorem projection_surjective_of_intertwining
    (h : ∀ g : G, ∃ T : V ≃ₗ[k] V, Intertwines N ρ g T) :
    Function.Surjective (projection N ρ) := by
  intro g
  obtain ⟨T, hT⟩ := h g
  obtain ⟨U, hU, hdet⟩ := exists_detOne_intertwiner N ρ g T hT
  exact ⟨⟨(g, U), hU, hdet⟩, rfl⟩

/-- Actual equivalences to all ambient conjugates supply the honest
intertwiners, and therefore an actual surjective determinant-one cover. -/
theorem projection_surjective_of_equiv
    (h : ∀ g : G, Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom))) :
    Function.Surjective (projection N ρ) := by
  apply projection_surjective_of_intertwining N ρ
  intro g
  obtain ⟨T⟩ := h g
  refine ⟨T.toLinearEquiv, ?_⟩
  intro n
  exact T.isIntertwining' n

end Kourovka2135.DeterminantOneIntertwinerSurjective

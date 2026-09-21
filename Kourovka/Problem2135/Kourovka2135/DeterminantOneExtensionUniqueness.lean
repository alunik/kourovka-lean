import Kourovka2135.DeterminantOneIntertwinerKernel
import Kourovka2135.CentralPGroupOddLift

/-! Two actual determinant-one extensions of the same irreducible
power-of-two-degree representation agree on every odd-order element.
Both representations lift to the concrete intertwiner cover; uniqueness
of odd lifts across its proved central binary kernel gives equality.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.DeterminantOneExtensionUniqueness

open DeterminantOneIntertwinerGroup

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (ρ : Representation k N V)
variable (α : Representation k G V) (hα : α.comp N.subtype = ρ)

include hα in
omit [N.Normal] in
/-- An actual extension retains the original coefficient automorphisms. -/
theorem coefficientAut_subtype (n : N) : coefficientAut α (n : G) = coefficientAut ρ n := by
  apply LinearEquiv.toLinearMap_injective
  simp only [coefficientAut_toLinearMap]
  exact DFunLike.congr_fun hα n

include hα in
/-- Every coefficient operator of an extension implements ambient conjugation. -/
theorem coefficientAut_intertwines (g : G) : Intertwines N ρ g (coefficientAut α g) := by
  apply (intertwines_iff_aut N ρ g (coefficientAut α g)).mpr
  intro n
  rw [← coefficientAut_subtype N ρ α hα n,
    ← coefficientAut_subtype N ρ α hα (MulAut.conjNormal g n)]
  change coefficientAut α g * coefficientAut α (n : G) =
    coefficientAut α (g * (n : G) * g⁻¹) * coefficientAut α g
  rw [map_mul, map_mul, map_inv]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

variable (hdetα : ∀ g : G, LinearMap.det (α g) = 1)

/-- An actual determinant-one extension is an actual homomorphic lift
of the identity map into the concrete cover. -/
def coverLift : G →* Carrier N ρ where
  toFun g := ⟨(g, coefficientAut α g), coefficientAut_intertwines N ρ α hα g,
    (coefficientAut_det_eq_one_iff α g).mpr (hdetα g)⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_one (coefficientAut α)
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact map_mul (coefficientAut α) g h

@[simp] theorem projection_coverLift (g : G) :
    projection N ρ (coverLift N ρ α hα hdetα g) = g := rfl

@[simp] theorem operator_coverLift (g : G) :
    operator N ρ (coverLift N ρ α hα hdetα g) = coefficientAut α g := rfl

variable [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]

include hα hdetα in
/-- No odd scalar ambiguity remains between determinant-one extensions
when the actual irreducible degree is a power of two. -/
theorem apply_eq_of_odd_orderOf
    (β : Representation k G V) (hβ : β.comp N.subtype = ρ)
    (hdetβ : ∀ g : G, LinearMap.det (β g) = 1)
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (g : G) (hg : Odd (orderOf g)) : α g = β g := by
  let A := coverLift N ρ α hα hdetα
  let B := coverLift N ρ β hβ hdetβ
  have hpowA : (A g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hpowB : (B g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hAB : A g = B g := CentralPGroupOddLift.eq_of_common_exponent (projection N ρ)
    (DeterminantOneIntertwinerKernel.kernel_le_center N ρ)
    (DeterminantOneIntertwinerKernel.kernel_isPGroup_two N ρ a hdim)
    hg.coprime_two_left rfl hpowA hpowB
  have h := congrArg (fun x : Carrier N ρ => (operator N ρ x).toLinearMap) hAB
  simpa only [A, B, operator_coverLift, coefficientAut_toLinearMap] using h

end Kourovka2135.DeterminantOneExtensionUniqueness

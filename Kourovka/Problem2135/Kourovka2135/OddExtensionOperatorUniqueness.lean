import Kourovka2135.DeterminantOneExtensionUniqueness

/-! Uniqueness at an odd-order element for actual extensions of an irreducible
representation of power-of-two degree. Determinant one is required only for
that element in the two given representations. The pointwise lifts are actual
elements of the already constructed intertwiner cover; they are not assumed
to assemble into a homomorphism. -/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.OddExtensionOperatorUniqueness

open DeterminantOneIntertwinerGroup

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (ρ : Representation k N V)
variable (α : Representation k G V) (hα : α.comp N.subtype = ρ)

/-- The actual operator above one element, using determinant one only at that element. -/
def coverElement (g : G) (hdet : LinearMap.det (α g) = 1) : Carrier N ρ :=
  ⟨(g, coefficientAut α g),
    DeterminantOneExtensionUniqueness.coefficientAut_intertwines N ρ α hα g,
    (coefficientAut_det_eq_one_iff α g).mpr hdet⟩

@[simp] theorem projection_coverElement (g : G) (hdet : LinearMap.det (α g) = 1) :
    projection N ρ (coverElement N ρ α hα g hdet) = g := rfl

@[simp] theorem operator_coverElement (g : G) (hdet : LinearMap.det (α g) = 1) :
    operator N ρ (coverElement N ρ α hα g hdet) = coefficientAut α g := rfl

/-- A power relation in the ambient group holds for the actual pair of coefficient coordinates. -/
theorem coverElement_pow_eq_one (g : G) (hdet : LinearMap.det (α g) = 1)
    (m : ℕ) (hgm : g ^ m = 1) : (coverElement N ρ α hα g hdet) ^ m = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · change g ^ m = 1
    exact hgm
  · change (coefficientAut α g) ^ m = 1
    rw [← map_pow, hgm, map_one]

variable [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]

include hα in
/-- At one actual element killed by an odd exponent, determinant one removes the scalar ambiguity. -/
theorem apply_eq_of_odd_pow
    (β : Representation k G V) (hβ : β.comp N.subtype = ρ)
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (g : G) (m : ℕ) (hm : Odd m) (hgm : g ^ m = 1)
    (hdetα : LinearMap.det (α g) = 1) (hdetβ : LinearMap.det (β g) = 1) :
    α g = β g := by
  let x := coverElement N ρ α hα g hdetα
  let y := coverElement N ρ β hβ g hdetβ
  have hx : x ^ m = 1 := coverElement_pow_eq_one N ρ α hα g hdetα m hgm
  have hy : y ^ m = 1 := coverElement_pow_eq_one N ρ β hβ g hdetβ m hgm
  have hxy : x = y := CentralPGroupOddLift.eq_of_common_exponent (projection N ρ)
    (DeterminantOneIntertwinerKernel.kernel_le_center N ρ)
    (DeterminantOneIntertwinerKernel.kernel_isPGroup_two N ρ a hdim)
    hm.coprime_two_left rfl hx hy
  have h := congrArg (fun z : Carrier N ρ => (operator N ρ z).toLinearMap) hxy
  simpa only [x, y, operator_coverElement, coefficientAut_toLinearMap] using h

include hα in
/-- The order-of-element formulation needs no determinant hypothesis at any other element. -/
theorem apply_eq_of_odd_orderOf
    (β : Representation k G V) (hβ : β.comp N.subtype = ρ)
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (g : G) (hg : Odd (orderOf g))
    (hdetα : LinearMap.det (α g) = 1) (hdetβ : LinearMap.det (β g) = 1) :
    α g = β g :=
  apply_eq_of_odd_pow N ρ α hα β hβ a hdim g (orderOf g) hg
    (pow_orderOf_eq_one g) hdetα hdetβ

end Kourovka2135.OddExtensionOperatorUniqueness

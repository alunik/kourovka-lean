import Kourovka2135.BinaryCorrectionRadical
import Kourovka2135.BilinearRestrictionRank

/-! Exact rank of the binary correction form on its linear kernel, and the
rank threshold after imposing further linear conditions. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryCorrection
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The scalar correction form on the kernel of its linear projection. -/
abbrev kernelPolarForm (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (D E : V ≃ₗ[ZMod 2] V) :
    (linearPart D E).ker →ₗ[ZMod 2] (linearPart D E).ker →ₗ[ZMod 2] ZMod 2 :=
  (polarForm β D E).compl₁₂ (linearPart D E).ker.subtype (linearPart D E).ker.subtype

/-- Surjectivity of the linear correction and duality force injective radical parametrization. -/
theorem parameterMap_injective_of_linearPart_surjective
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) :
    Function.Injective (parameterMap D E) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro t ht
  change t = 0
  apply hβ t
  intro y
  obtain ⟨z, rfl⟩ := hL y
  rw [alternating_symmetric β hAlt]
  have hh := polarForm_parameterMap β hAlt D E hD hE t z
  rw [show parameterMap D E t = 0 from ht, map_zero, LinearMap.zero_apply] at hh
  exact hh.symm

theorem kernelPolarForm_ker_eq [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) :
    (kernelPolarForm β D E).ker = kernelRadical D E := by
  ext z
  change kernelPolarForm β D E z = 0 ↔ z ∈ kernelRadical D E
  rw [← radical_iff_mem_kernelRadical β hAlt hβ D E hD hE hL]
  constructor
  · intro hz w
    exact LinearMap.congr_fun hz w
  · intro hz
    exact LinearMap.ext hz

theorem kernelRadical_finrank_eq_operatorCommutator_ker [FiniteDimensional (ZMod 2) V]
    (D E : V ≃ₗ[ZMod 2] V) (hinj : Function.Injective (parameterMap D E)) :
    Module.finrank (ZMod 2) (kernelRadical D E) =
      Module.finrank (ZMod 2) (operatorCommutator D E).ker := by
  have hmap := (Submodule.equivMapOfInjective (parameterMap D E) hinj
    (operatorCommutator D E).ker).finrank_eq
  have hsub := (Submodule.comapSubtypeEquivOfLe (commonRadical_le_kernel D E)).finrank_eq
  change Module.finrank (ZMod 2) (operatorCommutator D E).ker =
    Module.finrank (ZMod 2) (commonRadical D E) at hmap
  change Module.finrank (ZMod 2) (kernelRadical D E) =
    Module.finrank (ZMod 2) (commonRadical D E) at hsub
  exact hsub.trans hmap.symm

theorem linearPart_kernel_finrank [FiniteDimensional (ZMod 2) V]
    (D E : V ≃ₗ[ZMod 2] V) (hL : Function.Surjective (linearPart D E)) :
    Module.finrank (ZMod 2) (linearPart D E).ker = Module.finrank (ZMod 2) V := by
  have h := (linearPart D E).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, Module.finrank_prod] at h
  omega

/-- Exact scalar polar rank: the correction loses precisely the fixed directions
in the kernel of the additive operator commutator. -/
theorem kernelPolarForm_finrank_range_eq [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) :
    Module.finrank (ZMod 2) (kernelPolarForm β D E).range =
      Module.finrank (ZMod 2) (operatorCommutator D E).range := by
  have hinj := parameterMap_injective_of_linearPart_surjective β hAlt hβ D E hD hE hL
  have hk := (kernelPolarForm β D E).finrank_range_add_finrank_ker
  rw [kernelPolarForm_ker_eq β hAlt hβ D E hD hE hL,
    kernelRadical_finrank_eq_operatorCommutator_ker D E hinj,
    linearPart_kernel_finrank D E hL] at hk
  have hc := (operatorCommutator D E).finrank_range_add_finrank_ker
  omega

/-- Further linear conditions cost at most twice their codimension. -/
theorem kernelPolarForm_restrict_finrank_ge_twice [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E))
    (W : Submodule (ZMod 2) (linearPart D E).ker) (d : ℕ)
    (hrank : 2 * d + 2 * (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) W) ≤
      Module.finrank (ZMod 2) (operatorCommutator D E).range) :
    2 * d ≤ Module.finrank (ZMod 2)
      ((kernelPolarForm β D E).compl₁₂ W.subtype W.subtype).range := by
  apply bilinear_restrict_finrank_ge_twice (kernelPolarForm β D E) W d
  rw [kernelPolarForm_finrank_range_eq β hAlt hβ D E hD hE hL,
    linearPart_kernel_finrank D E hL]
  exact hrank

/-- The additive operator commutator is an invertible factor times the
paper-convention group commutator minus the identity. -/
theorem operatorCommutator_eq_comp_commutator_sub_id (D E : V ≃ₗ[ZMod 2] V) :
    operatorCommutator D E = (E * D).toLinearMap.comp
      ((D.symm * E.symm * D * E).toLinearMap - LinearMap.id) := by
  apply LinearMap.ext
  intro x
  change D (E x) - E (D x) = E (D ((D.symm * E.symm * D * E) x - x))
  simp only [LinearEquiv.mul_apply, map_sub, D.apply_symm_apply, E.apply_symm_apply]

theorem operatorCommutator_finrank_range_eq_commutator_sub_id
    (D E : V ≃ₗ[ZMod 2] V) :
    Module.finrank (ZMod 2) (operatorCommutator D E).range =
      Module.finrank (ZMod 2) ((D.symm * E.symm * D * E).toLinearMap - LinearMap.id).range := by
  rw [operatorCommutator_eq_comp_commutator_sub_id, LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective (E * D).toLinearMap (E * D).injective
    ((D.symm * E.symm * D * E).toLinearMap - LinearMap.id).range).finrank_eq.symm

/-- The correction form has precisely the moving rank of the group commutator. -/
theorem kernelPolarForm_finrank_range_eq_commutator_sub_id [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) :
    Module.finrank (ZMod 2) (kernelPolarForm β D E).range =
      Module.finrank (ZMod 2) ((D.symm * E.symm * D * E).toLinearMap - LinearMap.id).range := by
  rw [kernelPolarForm_finrank_range_eq β hAlt hβ D E hD hE hL,
    operatorCommutator_finrank_range_eq_commutator_sub_id]

end Kourovka2135.BinaryCorrection

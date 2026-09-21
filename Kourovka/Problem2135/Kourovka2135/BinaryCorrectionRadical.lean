import Kourovka2135.LinearDualCorrection
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! The exact common radical of the binary commutator correction form. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryCorrection
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Linear part of the correction on a pair of quotient vectors. -/
def linearPart (D E : V ≃ₗ[ZMod 2] V) : (V × V) →ₗ[ZMod 2] V :=
  (E.toLinearMap - LinearMap.id).comp (LinearMap.fst _ _ _) +
    (LinearMap.id - D.toLinearMap).comp (LinearMap.snd _ _ _)

/-- Parametrization whose restriction gives the common radical. -/
def parameterMap (D E : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] (V × V) :=
  (LinearMap.id - D.toLinearMap).prod (LinearMap.id - E.toLinearMap)

/-- Additive commutator of the two operators. -/
def operatorCommutator (D E : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V :=
  D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap

/-- Ambient bilinear form, restricted to the kernel of `linearPart` in applications. -/
def polarForm (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (D E : V ≃ₗ[ZMod 2] V) :
    (V × V) →ₗ[ZMod 2] (V × V) →ₗ[ZMod 2] ZMod 2 where
  toFun z := (β z.1).comp (D.toLinearMap.comp (LinearMap.snd _ _ _)) +
    (β.flip z.2).comp (E.toLinearMap.comp (LinearMap.fst _ _ _))
  map_add' z w := by
    apply LinearMap.ext
    intro u
    simp [map_add, add_assoc, add_comm, add_left_comm]
  map_smul' a z := by
    apply LinearMap.ext
    intro u
    simp [map_smul, smul_add]

@[simp] theorem linearPart_apply (D E : V ≃ₗ[ZMod 2] V) (z : V × V) :
    linearPart D E z = E z.1 - z.1 + (z.2 - D z.2) := rfl

@[simp] theorem parameterMap_apply (D E : V ≃ₗ[ZMod 2] V) (t : V) :
    parameterMap D E t = (t - D t, t - E t) := rfl

@[simp] theorem operatorCommutator_apply (D E : V ≃ₗ[ZMod 2] V) (t : V) :
    operatorCommutator D E t = D (E t) - E (D t) := rfl

@[simp] theorem polarForm_apply (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (D E : V ≃ₗ[ZMod 2] V) (z w : V × V) :
    polarForm β D E z w = β z.1 (D w.2) + β (E w.1) z.2 := rfl

theorem alternating_symmetric (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0) (x y : V) : β x y = β y x := by
  apply CharTwo.add_eq_zero.mp
  have h := hAlt (x + y)
  simpa only [map_add, LinearMap.add_apply, hAlt, zero_add, add_zero, add_comm] using h

theorem linearPart_parameterMap (D E : V ≃ₗ[ZMod 2] V) (t : V) :
    linearPart D E (parameterMap D E t) = operatorCommutator D E t := by
  simp only [linearPart_apply, parameterMap_apply, operatorCommutator_apply,
    map_sub]
  abel

/-- This identity determines the whole annihilator of the correction kernel. -/
theorem polarForm_parameterMap
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0) (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y) (t : V) (z : V × V) :
    polarForm β D E (parameterMap D E t) z = β (linearPart D E z) t := by
  simp only [polarForm_apply, parameterMap_apply, linearPart_apply,
    map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply]
  rw [hD, hE, alternating_symmetric β hAlt t (D z.2), alternating_symmetric β hAlt t z.2]
  simp only [CharTwo.sub_eq_add]
  abel

theorem polarForm_nondegenerate
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V) (z : V × V)
    (hz : ∀ w, polarForm β D E z w = 0) : z = 0 := by
  apply Prod.ext
  · apply hβ z.1
    intro y
    have h := hz (0, D.symm y)
    simpa only [polarForm_apply, Prod.fst, Prod.snd, map_zero,
      LinearMap.zero_apply, add_zero, D.apply_symm_apply] using h
  · apply hβ z.2
    intro y
    have h := hz (E.symm y, 0)
    simpa only [polarForm_apply, Prod.fst, Prod.snd, map_zero,
      zero_add, E.apply_symm_apply, alternating_symmetric β hAlt y z.2] using h

/-- The radical is independent of the chosen invariant nondegenerate alternating form. -/
def commonRadical (D E : V ≃ₗ[ZMod 2] V) : Submodule (ZMod 2) (V × V) :=
  (operatorCommutator D E).ker.map (parameterMap D E)

theorem commonRadical_le_kernel (D E : V ≃ₗ[ZMod 2] V) :
    commonRadical D E ≤ (linearPart D E).ker := by
  rintro z ⟨t, ht, rfl⟩
  change linearPart D E (parameterMap D E t) = 0
  rw [linearPart_parameterMap]
  exact ht

theorem radical_iff [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) (z : V × V) :
    (linearPart D E z = 0 ∧
      ∀ w, linearPart D E w = 0 → polarForm β D E z w = 0) ↔
        z ∈ commonRadical D E := by
  constructor
  · rintro ⟨hz, hzB⟩
    obtain ⟨t, ht⟩ := exists_bilinear_correction β hβ (linearPart D E) hL
      (polarForm β D E z) hzB
    have heq : z = parameterMap D E t := by
      apply sub_eq_zero.mp
      apply polarForm_nondegenerate β hAlt hβ D E
      intro w
      rw [map_sub, LinearMap.sub_apply, polarForm_parameterMap β hAlt D E hD hE,
        alternating_symmetric β hAlt (linearPart D E w) t, ht, sub_self]
    refine ⟨t, ?_, heq.symm⟩
    change operatorCommutator D E t = 0
    rw [← linearPart_parameterMap, ← heq, hz]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [linearPart_parameterMap]
      exact ht
    · intro w hw
      rw [polarForm_parameterMap β hAlt D E hD hE, hw, map_zero, LinearMap.zero_apply]

/-- No common fixed vector makes the parametrization injective. -/
theorem parameterMap_injective
    (D E : V ≃ₗ[ZMod 2] V)
    (hfix : ∀ t, D t = t → E t = t → t = 0) :
    Function.Injective (parameterMap D E) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro t ht
  change t = 0
  have hf := congrArg Prod.fst ht
  have hs := congrArg Prod.snd ht
  exact hfix t (sub_eq_zero.mp hf).symm (sub_eq_zero.mp hs).symm

/-- Noncommuting operators force a proper radical once the linear correction is onto. -/
theorem commonRadical_ne_kernel [FiniteDimensional (ZMod 2) V]
    (D E : V ≃ₗ[ZMod 2] V) (hL : Function.Surjective (linearPart D E))
    (hDE : D.toLinearMap.comp E.toLinearMap ≠ E.toLinearMap.comp D.toLinearMap) :
    commonRadical D E ≠ (linearPart D E).ker := by
  have hC : operatorCommutator D E ≠ 0 := sub_ne_zero.mpr hDE
  have hker : (operatorCommutator D E).ker ≠ ⊤ := by
    intro htop
    apply hC
    apply LinearMap.ext
    intro t
    have ht : t ∈ (operatorCommutator D E).ker := by rw [htop]; trivial
    exact ht
  have hdimC := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hker)
  rw [finrank_top] at hdimC
  have hdimT := Submodule.finrank_map_le (parameterMap D E) (operatorCommutator D E).ker
  have hdimL := (linearPart D E).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL, finrank_top, Module.finrank_prod] at hdimL
  intro heq
  change Module.finrank (ZMod 2) (commonRadical D E) ≤ _ at hdimT
  rw [heq] at hdimT
  omega

/-- The common radical regarded as a subspace of the correction kernel itself. -/
def kernelRadical (D E : V ≃ₗ[ZMod 2] V) :
    Submodule (ZMod 2) (linearPart D E).ker :=
  (commonRadical D E).comap (linearPart D E).ker.subtype

/-- Subtype-facing radical criterion for a quadratic map on a correction fiber. -/
theorem radical_iff_mem_kernelRadical [FiniteDimensional (ZMod 2) V]
    (β : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hAlt : ∀ x, β x x = 0)
    (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (D E : V ≃ₗ[ZMod 2] V)
    (hD : ∀ x y, β (D x) (D y) = β x y)
    (hE : ∀ x y, β (E x) (E y) = β x y)
    (hL : Function.Surjective (linearPart D E)) (z : (linearPart D E).ker) :
    (∀ w : (linearPart D E).ker, polarForm β D E z w = 0) ↔
      z ∈ kernelRadical D E := by
  change (∀ w : (linearPart D E).ker, polarForm β D E z w = 0) ↔
    (z : V × V) ∈ commonRadical D E
  rw [← radical_iff β hAlt hβ D E hD hE hL]
  constructor
  · intro h
    refine ⟨z.property, ?_⟩
    intro w hw
    exact h ⟨w, hw⟩
  · intro h w
    exact h.2 w w.property

theorem kernelRadical_ne_top [FiniteDimensional (ZMod 2) V]
    (D E : V ≃ₗ[ZMod 2] V) (hL : Function.Surjective (linearPart D E))
    (hDE : D.toLinearMap.comp E.toLinearMap ≠ E.toLinearMap.comp D.toLinearMap) :
    kernelRadical D E ≠ ⊤ := by
  intro htop
  apply commonRadical_ne_kernel D E hL hDE
  apply le_antisymm (commonRadical_le_kernel D E)
  intro z hz
  have h : (⟨z, hz⟩ : (linearPart D E).ker) ∈ kernelRadical D E := by
    rw [htop]
    trivial
  exact h

end Kourovka2135.BinaryCorrection

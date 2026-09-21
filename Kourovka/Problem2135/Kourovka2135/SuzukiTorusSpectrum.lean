import Kourovka2135.SuzukiBrandlMatrices

/-! The split Suzuki torus parameter is determined up to inversion by its
four characteristic roots. This scalar proof uses the Tits identity alone. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTorusSpectrum

open Polynomial SuzukiBrandlMatrices
open scoped Polynomial

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
/-- Inverting a member preserves the four-element spectrum. -/
theorem inv_mem_weights (σ : F ≃+* F) (a z : F)
    (hz : ∃ i, z = weights σ a i) : ∃ i, z⁻¹ = weights σ a i := by
  obtain ⟨i, rfl⟩ := hz
  fin_cases i
  · exact ⟨3, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, by simp [weights]⟩
  · exact ⟨0, by simp [weights]⟩

/-- The twisted norm of the outer weight is outside the spectrum of any
nonidentity torus parameter. -/
theorem outer_norm_not_mem_weights (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x ^ 2) (a : F) (ha : a ≠ 0) (hne : a ≠ 1) :
    ¬ ∃ i, (a * σ a) * σ (a * σ a) = weights σ a i := by
  have hs : σ a ≠ 0 := (map_ne_zero σ).2 ha
  have hn : a * σ a ≠ 1 := fun h => hne ((norm_eq_one_iff σ hσ a ha).mp h)
  have hni := weights_injective σ hσ (a * σ a) (mul_ne_zero ha hs) hn
  rintro ⟨i, hi⟩
  fin_cases i
  · have hh : weights σ (a * σ a) 0 = weights σ (a * σ a) 1 := hi
    have := hni hh
    norm_num at this
  · have hh : a * (a * σ a) ^ 2 = a * 1 := by
      simpa [weights, map_mul, hσ, pow_two, mul_assoc, mul_left_comm, mul_comm] using hi
    exact hn ((sq_eq_one_iff _).mp (mul_left_cancel₀ ha hh))
  · have hh : (a ^ 2 * σ a) ^ 2 = 1 := by
      have he := congrArg (fun x : F => a * x) hi
      simpa [weights, map_mul, hσ, pow_two, mul_assoc, mul_left_comm, mul_comm, ha] using he
    exact hne ((second_norm_eq_one_iff σ hσ a ha).mp ((sq_eq_one_iff _).mp hh))
  · have hh : weights σ (a * σ a) 0 = weights σ (a * σ a) 2 := hi
    exact (by decide : (0 : Fin 4) ≠ 2) (hni hh)

/-- A nonzero scalar and its twisted norm both lie in a nonidentity torus
spectrum only when the scalar is its middle parameter or its inverse. -/
theorem eq_or_inv_of_mem_weights (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x ^ 2) (a b : F) (ha : a ≠ 0) (hne : a ≠ 1)
    (hb : ∃ i, b = weights σ a i)
    (hbn : ∃ i, b * σ b = weights σ a i) : b = a ∨ b = a⁻¹ := by
  obtain ⟨i, hi⟩ := hb
  fin_cases i
  · exfalso
    change b = a * σ a at hi
    rw [hi] at hbn
    exact outer_norm_not_mem_weights σ hσ a ha hne hbn
  · exact Or.inl hi
  · exact Or.inr hi
  · exfalso
    apply outer_norm_not_mem_weights σ hσ a ha hne
    have hh := inv_mem_weights σ a (b * σ b) hbn
    change b = (a * σ a)⁻¹ at hi
    rw [hi] at hh
    simpa only [map_mul, map_inv₀, mul_inv, inv_inv] using hh

omit [CharP F 2] in
/-- Polynomial equality is used only to extract actual scalar roots. -/
theorem mem_weights_of_polynomial_eq (σ : F ≃+* F) (a b : F)
    (he : (∏ i : Fin 4, (X - C (weights σ a i))) =
      ∏ i : Fin 4, (X - C (weights σ b i))) (j : Fin 4) :
    ∃ i, weights σ b j = weights σ a i := by
  have hr : eval (weights σ b j) (∏ i : Fin 4, (X - C (weights σ b i))) = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  rw [← he, eval_prod] at hr
  obtain ⟨i, _, hi⟩ := (Finset.prod_eq_zero_iff).mp hr
  exact ⟨i, sub_eq_zero.mp (by simpa using hi)⟩

theorem eq_or_inv_of_polynomial_eq (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x ^ 2) (a b : F) (ha : a ≠ 0) (hne : a ≠ 1)
    (he : (∏ i : Fin 4, (X - C (weights σ a i))) =
      ∏ i : Fin 4, (X - C (weights σ b i))) : b = a ∨ b = a⁻¹ :=
  eq_or_inv_of_mem_weights σ hσ a b ha hne
    (mem_weights_of_polynomial_eq σ a b he 1)
    (mem_weights_of_polynomial_eq σ a b he 0)

end Kourovka2135.SuzukiTorusSpectrum

import Kourovka2135.CoinducedLinearCharacter
import Mathlib.LinearAlgebra.StdBasis

/-! The subgroup-supported delta function is an actual cyclic vector in
coinduction of a one-dimensional character. This uses right-coset basis
coordinates and is valid in every characteristic, including when the
subgroup order is zero in the coefficient field. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.CoinducedCharacterCyclic

open CoinducedLinearCharacter CoinducedCharacterFormula
attribute [local instance] Classical.propDecidable

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable (S : Subgroup G) (χ : S →* kˣ)

/-- Character-valued delta on the identity right coset. -/
def delta : Space S χ := by
  classical
  refine ⟨fun g => if hg : g ∈ S then (χ ⟨g, hg⟩ : k) else 0, ?_⟩
  intro s g
  by_cases hg : g ∈ S
  · have hsg := S.mul_mem s.property hg
    change (if h : (s : G) * g ∈ S then (χ ⟨(s : G) * g, h⟩ : k) else 0) =
      (χ s : k) * (if h : g ∈ S then (χ ⟨g, h⟩ : k) else 0)
    rw [dite_eq_left hsg, dite_eq_left hg]
    exact congrArg Units.val (χ.map_mul s ⟨g, hg⟩)
  · have hsg : (s : G) * g ∉ S := fun h => hg ((S.mul_mem_cancel_left s.property).mp h)
    change (if h : (s : G) * g ∈ S then (χ ⟨(s : G) * g, h⟩ : k) else 0) =
      (χ s : k) * (if h : g ∈ S then (χ ⟨g, h⟩ : k) else 0)
    rw [dite_eq_right hsg, dite_eq_right hg, mul_zero]

theorem delta_apply_mem (g : G) (hg : g ∈ S) :
    (delta S χ).val g = (χ ⟨g, hg⟩ : k) := by
  classical
  exact dite_eq_left hg

theorem delta_apply_not_mem (g : G) (hg : g ∉ S) : (delta S χ).val g = 0 := by
  classical
  exact dite_eq_right hg

@[simp] theorem delta_one : (delta S χ).val 1 = 1 := by
  rw [delta_apply_mem S χ 1 S.one_mem]
  exact congrArg Units.val χ.map_one

theorem delta_ne_zero : delta S χ ≠ 0 := by
  intro he
  have hv := congrArg (fun f : Space S χ => f.val 1) he
  rw [delta_one] at hv
  exact one_ne_zero hv

/-- The delta line has its defining subgroup character under right translation. -/
theorem induced_delta (s : S) :
    induced S χ (s : G) (delta S χ) = (χ s : k) • delta S χ := by
  classical
  apply Subtype.ext
  funext g
  change (delta S χ).val (g * (s : G)) = (χ s : k) * (delta S χ).val g
  by_cases hg : g ∈ S
  · rw [delta_apply_mem S χ _ (S.mul_mem hg s.property), delta_apply_mem S χ _ hg]
    have hm := congrArg Units.val (χ.map_mul (⟨g, hg⟩ : S) s)
    exact hm.trans (mul_comm _ _)
  · have hgs : g * (s : G) ∉ S := fun h => hg ((S.mul_mem_cancel_right s.property).mp h)
    rw [delta_apply_not_mem S χ _ hgs, delta_apply_not_mem S χ _ hg, mul_zero]

/-- Translating the subgroup delta produces the actual right-coset basis. -/
theorem translated_delta_coordinates (q : RightCosets S) :
    coindVEquivQuotient S (linear S χ)
      (induced S χ (Quotient.out q)⁻¹ (delta S χ)) = Pi.single q 1 := by
  classical
  funext q'
  change (delta S χ).val (Quotient.out q' * (Quotient.out q)⁻¹) = (Pi.single q (1 : k) : RightCosets S → k) q'
  by_cases he : q' = q
  · subst q'
    simp only [mul_inv_cancel, delta_one, Pi.single_eq_same]
  · have hnot : Quotient.out q' * (Quotient.out q)⁻¹ ∉ S := by
      intro h
      have hrel : QuotientGroup.rightRel S (Quotient.out q) (Quotient.out q') :=
        QuotientGroup.rightRel_apply.mpr h
      have heq : q = q' := by
        simpa only [Quotient.out_eq] using Quotient.sound hrel
      exact he heq.symm
    rw [delta_apply_not_mem S χ _ hnot, Pi.single_eq_of_ne he]

variable [Finite G]

/-- Any invariant subspace containing delta contains the entire induced
module. The proof uses no division by the subgroup order. -/
theorem eq_top_of_delta_mem (W : Submodule k (Space S χ))
    (hW : ∀ (g : G) (v : Space S χ), v ∈ W → induced S χ g v ∈ W)
    (hdelta : delta S χ ∈ W) : W = ⊤ := by
  classical
  let e := coindVEquivQuotient S (linear S χ)
  let b := (Pi.basisFun k (RightCosets S)).map e.symm
  have hmem (q : RightCosets S) : b q ∈ W := by
    have hq := hW (Quotient.out q)⁻¹ (delta S χ) hdelta
    have he : induced S χ (Quotient.out q)⁻¹ (delta S χ) = e.symm (Pi.single q 1) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact translated_delta_coordinates S χ q
    rw [he] at hq
    simpa only [b, Module.Basis.map_apply, Pi.basisFun_apply] using hq
  apply top_unique
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact hmem q

end Kourovka2135.CoinducedCharacterCyclic

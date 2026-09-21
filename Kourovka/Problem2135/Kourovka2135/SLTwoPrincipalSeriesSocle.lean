import Kourovka2135.SLTwoPrincipalSeriesDelta
import Kourovka2135.SLTwoUnipotentInvariants
import Kourovka2135.BinaryTensorSLTwoEvaluation

/-! The nontrivial-character socle of the actual homogeneous-function module.

Distinct torus weights force every nonzero proper stable subspace to contain
the affine indicator. The tensor evaluation image is proper and is generated
by that vector. All assertions concern the concrete representations.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SLTwoPrincipalSeries

open SLTwoHomogeneousFunctions

variable (k : Type u) [Field k] [CharP k 2]
variable {F : Type v} [Field F] [Fintype F] (σ : F →+* k) (n : ℕ)

/-- A nonzero reduced weight has distinct opposite torus characters. -/
theorem exists_distinct_torus_weights (hn : 0 < n) (hnq : n < Fintype.card F - 1) :
    ∃ r : Fˣ, σ (r : F) ^ n ≠ σ ((r⁻¹ : Fˣ) : F) ^ n := by
  classical
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have horder : orderOf r = Fintype.card F - 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hr
  refine ⟨r, ?_⟩
  intro he
  have hs : (σ (r : F) ^ n) ^ 2 = 1 := by
    calc
      _ = σ (r : F) ^ n * σ (r : F) ^ n := pow_two _
      _ = σ (r : F) ^ n * σ ((r⁻¹ : Fˣ) : F) ^ n :=
        congrArg (fun x : k => σ (r : F) ^ n * x) he
      _ = 1 := by rw [← mul_pow, ← map_mul]; simp
  have hp : σ (r : F) ^ n = 1 := by
    simpa only [sq_eq_one_iff, CharTwo.neg_eq, or_self] using hs
  have hpr : (r : F) ^ n = 1 := σ.injective (by simpa only [map_pow, map_one] using hp)
  have hpu : r ^ n = 1 := Units.ext (by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using hpr)
  exact pow_ne_one_of_lt_orderOf (Nat.ne_of_gt hn) (by rwa [horder]) hpu

omit [CharP k 2] [Fintype F] in
/-- Distinct torus weights isolate infinity delta from a fixed vector. -/
theorem infinityDelta_mem_of_fixed_combination
    (W : Submodule k (Carrier k σ n))
    (hstable : ∀ (g : SLTwo.SL2 F) (h : Carrier k σ n), h ∈ W →
      representation k σ n g h ∈ W)
    (r : Fˣ) (hr : σ (r : F) ^ n ≠ σ ((r⁻¹ : Fˣ) : F) ^ n)
    (a b : k) (hb : b ≠ 0)
    (hv : a • affineIndicator k σ n + b • infinityDelta k σ n ∈ W) :
    infinityDelta k σ n ∈ W := by
  let α := σ (r : F) ^ n
  let β := σ ((r⁻¹ : Fˣ) : F) ^ n
  have he : representation k σ n (SLTwo.tor r)
        (a • affineIndicator k σ n + b • infinityDelta k σ n) -
      α • (a • affineIndicator k σ n + b • infinityDelta k σ n) =
      ((β - α) * b) • infinityDelta k σ n := by
    apply (coordinates k σ n).injective
    simp only [map_sub, map_add, map_smul, torus_affineIndicator,
      torus_infinityDelta, coordinates_affineIndicator, coordinates_infinityDelta]
    apply Prod.ext
    · change a * (α * 0) + b * (β * 1) - α * (a * 0 + b * 1) =
        ((β - α) * b) * 1
      ring
    · funext t
      change a * (α * 1) + b * (β * 0) - α * (a * 1 + b * 0) =
        ((β - α) * b) * 0
      ring
  have hm := W.sub_mem (hstable (SLTwo.tor r) _ hv) (W.smul_mem α hv)
  rw [he] at hm
  exact (W.smul_mem_iff (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hr)) hb)).mp hm

/-- Every nonzero proper stable subspace contains the affine fixed line. -/
theorem affineIndicator_mem_of_ne_bot_ne_top
    (W : Submodule k (Carrier k σ n)) (hW : W ≠ ⊥) (hproper : W ≠ ⊤)
    (hstable : ∀ (g : SLTwo.SL2 F) (h : Carrier k σ n), h ∈ W →
      representation k σ n g h ∈ W)
    (r : Fˣ) (hr : σ (r : F) ^ n ≠ σ ((r⁻¹ : Fˣ) : F) ^ n) :
    affineIndicator k σ n ∈ W := by
  have : CharP F 2 := σ.charP σ.injective 2
  obtain ⟨v, hvW, hv, hfix⟩ :=
    SLTwoUnipotentInvariants.exists_nonzero_unipotent_fixed_mem
      (representation k σ n) W hW (fun t h hh => hstable (SLTwo.uni t) h hh)
  obtain ⟨a, b, hvab⟩ := (unipotent_fixed_iff k σ n v).mp hfix
  have hb : b = 0 := by
    by_contra hb
    apply hproper
    apply eq_top_of_infinityDelta_mem k σ n W hstable
    apply infinityDelta_mem_of_fixed_combination k σ n W hstable r hr a b hb
    rwa [← hvab]
  rw [hb, zero_smul, add_zero] at hvab
  have ha : a ≠ 0 := by
    intro ha
    apply hv
    simpa [ha] using hvab
  rw [hvab] at hvW
  exact (W.smul_mem_iff ha).mp hvW

section Tensor

variable {f : ℕ} (I : Finset (Fin f))
variable (hcard : Fintype.card F = 2 ^ f)

omit [Fintype F] in
/-- The top of the actual tensor evaluation is the affine indicator. -/
theorem evaluation_top_eq_affineIndicator
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I) :
    BinaryTensorSLTwoEvaluation.evaluation k σ I
      (BinaryTensorCoefficient.basis k I Finset.univ) =
      affineIndicator k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) := by
  apply (coordinates k σ _).injective
  rw [coordinates_affineIndicator, ← BinaryTensorSLTwoSimplicity.global_basis_top]
  exact BinaryTensorSLTwoEvaluation.evaluationLinear_top_coordinates k σ I hn

include hcard

/-- Infinity delta cannot occur in the tensor evaluation image. -/
theorem infinityDelta_not_mem_evaluation_range
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I) :
    infinityDelta k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) ∉
      LinearMap.range (BinaryTensorSLTwoEvaluation.evaluation k σ I).toLinearMap := by
  rintro ⟨v, hv⟩
  change BinaryTensorSLTwoEvaluation.evaluation k σ I v = _ at hv
  have hfix : ∀ t : F, BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v = v := by
    intro t
    apply BinaryTensorSLTwoEvaluation.evaluation_injective k σ I hcard
    rw [BinaryTensorSLTwoEvaluation.evaluation_apply,
      BinaryTensorSLTwoEvaluation.evaluationLinear_action]
    change representation k σ _ (SLTwo.uni t)
        (BinaryTensorSLTwoEvaluation.evaluation k σ I v) =
      BinaryTensorSLTwoEvaluation.evaluation k σ I v
    rw [hv, unipotent_infinityDelta]
  obtain ⟨a, ha⟩ :=
    (BinaryTensorSLTwoSimplicity.unipotent_fixed_iff_top k I σ hcard v).mp hfix
  rw [ha, map_smul, evaluation_top_eq_affineIndicator k σ I hn] at hv
  exact infinityDelta_ne_smul_affineIndicator k σ _ a hv.symm

/-- The actual tensor image is a proper subspace, without a dimension premise. -/
theorem evaluation_range_ne_top
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I) :
    LinearMap.range (BinaryTensorSLTwoEvaluation.evaluation k σ I).toLinearMap ≠ ⊤ := by
  intro h
  apply infinityDelta_not_mem_evaluation_range k σ I hcard hn
  rw [h]
  trivial

/-- Every stable subspace containing the affine indicator contains the tensor image. -/
theorem evaluation_range_le_of_affineIndicator_mem
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I)
    (W : Submodule k (Carrier k σ (BinaryExteriorGroupAlgebra.subsetWeight f I)))
    (hstable : ∀ (g : SLTwo.SL2 F) (h : Carrier k σ _), h ∈ W →
      representation k σ _ g h ∈ W)
    (hA : affineIndicator k σ (BinaryExteriorGroupAlgebra.subsetWeight f I) ∈ W) :
    LinearMap.range (BinaryTensorSLTwoEvaluation.evaluation k σ I).toLinearMap ≤ W := by
  let P := W.comap (BinaryTensorSLTwoEvaluation.evaluation k σ I).toLinearMap
  have hP : P = ⊤ := by
    apply BinaryTensorSLTwoSimplicity.eq_top_of_stable k I σ hcard P
    · refine ⟨BinaryTensorCoefficient.basis k I Finset.univ, ?_,
        (BinaryTensorCoefficient.basis k I).ne_zero _⟩
      change BinaryTensorSLTwoEvaluation.evaluation k σ I _ ∈ W
      rwa [evaluation_top_eq_affineIndicator k σ I hn]
    · intro g v hv
      change BinaryTensorSLTwoEvaluation.evaluationLinear k σ I
        (BinaryTensorSLTwo.representation k σ I g v) ∈ W
      rw [BinaryTensorSLTwoEvaluation.evaluationLinear_action]
      exact hstable g _ hv
  rintro _ ⟨v, rfl⟩
  change v ∈ P
  rw [hP]
  trivial

/-- The tensor image is contained in every nonzero stable subspace at its
positive reduced weight. Torus separation is derived from the finite field. -/
theorem evaluation_range_le_of_ne_bot
    (hn : 0 < BinaryExteriorGroupAlgebra.subsetWeight f I)
    (hnq : BinaryExteriorGroupAlgebra.subsetWeight f I < Fintype.card F - 1)
    (W : Submodule k (Carrier k σ (BinaryExteriorGroupAlgebra.subsetWeight f I)))
    (hW : W ≠ ⊥)
    (hstable : ∀ (g : SLTwo.SL2 F) (h : Carrier k σ _), h ∈ W →
      representation k σ _ g h ∈ W) :
    LinearMap.range (BinaryTensorSLTwoEvaluation.evaluation k σ I).toLinearMap ≤ W := by
  by_cases htop : W = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := exists_distinct_torus_weights k σ _ hn hnq
  apply evaluation_range_le_of_affineIndicator_mem k σ I hcard hn W hstable
  exact affineIndicator_mem_of_ne_bot_ne_top k σ _ W hW htop hstable r hr

end Tensor
end Kourovka2135.SLTwoPrincipalSeries

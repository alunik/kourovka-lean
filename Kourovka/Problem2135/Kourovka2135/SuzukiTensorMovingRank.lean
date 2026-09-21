import Kourovka2135.SuzukiTensorWeightCount
import Kourovka2135.SuzukiBrandlMatrices
import Kourovka2135.SuzukiNaturalH1
import Kourovka2135.RepresentationEmbeddingModel

/-! Actual moving ranks of Suzuki Frobenius tensors. Four distinct natural
split-torus eigenvalues give at most one fixed choice in each one-coordinate
fiber, retaining all pure-tensor multiplicities. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorMovingRank

open SuzukiTorusMovingRank SuzukiTensorNatural
open scoped TensorProduct PiTensorProduct Classical

variable (k : Type) [Field k] [CharP k 2] (m : ℕ)
variable (σ : K m →+* k) (u : (K m)ˣ)

/-- The natural eigenvalues are pairwise distinct at every nonidentity parameter. -/
theorem torusWeights_injective (hu : u ≠ 1) : Function.Injective (torusWeights m u) := by
  have he : torusWeights m u =
      SuzukiBrandlMatrices.weights (tits m) ((u : K m) ^ (2 ^ m)) := by
    funext j
    fin_cases j <;> simp [torusWeights, SuzukiBrandlMatrices.weights, tits_middle,
      pow_add, mul_comm]
  rw [he]
  exact SuzukiBrandlMatrices.weights_injective (tits m) (tits_sq m) _
    (pow_ne_zero _ u.ne_zero) (middle_ne_one m u hu)

def factorWeight (n : ℕ) (j : Fin 4) : k := (σ (torusWeights m u j)) ^ (2 ^ n)

theorem factorWeight_injective (hu : u ≠ 1) (n : ℕ) :
    Function.Injective (factorWeight k m σ u n) := by
  intro a b h
  apply torusWeights_injective m u hu
  apply σ.injective
  exact (iterateFrobenius k 2 n).injective h

omit [CharP k 2] in
theorem factorWeight_ne_zero (n : ℕ) (j : Fin 4) : factorWeight k m σ u n j ≠ 0 := by
  apply pow_ne_zero
  apply (map_ne_zero σ).mpr
  fin_cases j <;> simp [torusWeights, u.ne_zero]

theorem factorWeight_ne_one (hu : u ≠ 1) (n : ℕ) (j : Fin 4) :
    factorWeight k m σ u n j ≠ 1 := by
  intro h
  apply torusWeights_ne_one m u hu j
  apply σ.injective
  apply (iterateFrobenius k 2 n).injective
  simpa only [factorWeight, iterateFrobenius_def, map_one] using h

theorem naturalTwist_torus_basis (n : ℕ) (j : Fin 4) :
    naturalTwist k m σ n (torusHom m u) (Pi.basisFun k (Fin 4) j) =
      factorWeight k m σ u n j • Pi.basisFun k (Fin 4) j := by
  ext l
  fin_cases j <;> fin_cases l <;>
    simp [naturalTwist_apply, matrixHom, torusHom,
      BenderSuzuki.MatrixGroups.SuzukiTorusGL,
      BenderSuzuki.MatrixGroups.SuzukiTorusMatrix,
      Fin.sum_univ_four, Pi.basisFun_apply, factorWeight, torusWeights]

variable (I : Finset (Fin (2 * m + 1)))

def eigenvalue (a : I → Fin 4) : k := ∏ i : I, factorWeight k m σ u i.val.val (a i)

theorem torus_basis (a : I → Fin 4) :
    representation k m I σ (torusHom m u) (tensorBasis k m I a) =
      eigenvalue k m σ u I a • tensorBasis k m I a := by
  simp only [tensorBasis, Basis.piTensorProduct_apply, representation_tprod,
    naturalTwist_torus_basis]
  exact (PiTensorProduct.tprod k).map_smul_univ _ _

abbrev Rest (i : I) := {j : I // j ≠ i}
def rest (i : I) (a : I → Fin 4) : Rest m I i → Fin 4 := fun j => a j.val

theorem eigenvalue_injective_on_fiber (hu : u ≠ 1) (i : I) (a b : I → Fin 4)
    (hr : rest m I i a = rest m I i b)
    (he : eigenvalue k m σ u I a = eigenvalue k m σ u I b) : a = b := by
  classical
  have hrest : ∏ j ∈ Finset.univ.erase i, factorWeight k m σ u j.val.val (a j) =
      ∏ j ∈ Finset.univ.erase i, factorWeight k m σ u j.val.val (b j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjne := (Finset.mem_erase.mp hj).1
    rw [show a j = b j from congrFun hr (⟨j, hjne⟩ : Rest m I i)]
  have ha := Finset.mul_prod_erase Finset.univ
    (fun j : I => factorWeight k m σ u j.val.val (a j)) (Finset.mem_univ i)
  have hb := Finset.mul_prod_erase Finset.univ
    (fun j : I => factorWeight k m σ u j.val.val (b j)) (Finset.mem_univ i)
  change (∏ j : I, factorWeight k m σ u j.val.val (a j)) =
    ∏ j : I, factorWeight k m σ u j.val.val (b j) at he
  rw [← ha, ← hb, hrest] at he
  have hn : (∏ j ∈ Finset.univ.erase i,
      factorWeight k m σ u j.val.val (b j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => factorWeight_ne_zero k m σ u j.val.val (b j))
  have hi : a i = b i := factorWeight_injective k m σ u hu i.val.val (mul_right_cancel₀ hn he)
  funext j
  by_cases hj : j = i
  · simpa only [hj] using hi
  · exact congrFun hr (⟨j, hj⟩ : Rest m I i)

theorem rest_card (i : I) : Fintype.card (Rest m I i) = I.card - 1 := by
  classical
  have he : Finset.univ.filter (fun j : I => j ≠ i) = Finset.univ.erase i := by
    ext j; simp
  rw [Fintype.card_subtype, he, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

theorem fixed_card_le (hu : u ≠ 1) (i : I) :
    (Finset.univ.filter (fun a : I → Fin 4 => eigenvalue k m σ u I a = 1)).card ≤
      4 ^ (I.card - 1) := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise (f := rest m I i)
    (s := Finset.univ.filter (fun a : I → Fin 4 => eigenvalue k m σ u I a = 1))
    (t := Finset.univ) (fun a _ => Finset.mem_univ (rest m I i a))
  rw [hc]
  calc
    _ ≤ ∑ r : Rest m I i → Fin 4, 1 := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact eigenvalue_injective_on_fiber k m σ u I hu i a b
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
        ((Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2.trans
          (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2.symm)
    _ = _ := by simp [rest_card m I i]

/-- Every basis vector with a nonidentity eigenvalue lies in the actual moving range. -/
theorem moved_card_le_rank :
    (Finset.univ.filter (fun a : I → Fin 4 => eigenvalue k m σ u I a ≠ 1)).card ≤
      Module.finrank k (representation k m I σ (torusHom m u) - LinearMap.id).range := by
  classical
  let S := Finset.univ.filter (fun a : I → Fin 4 => eigenvalue k m σ u I a ≠ 1)
  let v : S → TensorSpace k m I := fun a => tensorBasis k m I a.val
  have hlin : LinearIndependent k v :=
    (tensorBasis k m I).linearIndependent.comp _ Subtype.val_injective
  have hsub : Submodule.span k (Set.range v) ≤
      (representation k m I σ (torusHom m u) - LinearMap.id).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hn : eigenvalue k m σ u I a.val - 1 ≠ 0 :=
      sub_ne_zero.mpr (Finset.mem_filter.mp a.property).2
    refine ⟨(eigenvalue k m σ u I a.val - 1)⁻¹ • tensorBasis k m I a.val, ?_⟩
    have hd : (representation k m I σ (torusHom m u) - LinearMap.id :
        Module.End k (TensorSpace k m I))
        (tensorBasis k m I a.val) =
        (eigenvalue k m σ u I a.val - 1) • tensorBasis k m I a.val := by
      simp only [LinearMap.sub_apply, LinearMap.id_apply, torus_basis]
      exact (sub_smul (eigenvalue k m σ u I a.val) (1 : k)
        (tensorBasis k m I a.val)).trans (by rw [one_smul]) |>.symm
    change (representation k m I σ (torusHom m u) - LinearMap.id :
      Module.End k (TensorSpace k m I))
      ((eigenvalue k m σ u I a.val - 1)⁻¹ • tensorBasis k m I a.val) =
        tensorBasis k m I a.val
    rw [LinearMap.map_smul, hd, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hdim := finrank_span_eq_card hlin
  have hle := Submodule.finrank_mono hsub
  rw [hdim] at hle
  simpa only [Fintype.card_coe] using hle

/-- The actual tensor moving rank is at least three quarters of its dimension. -/
theorem three_quarters_le_rank (hu : u ≠ 1) (hI : I.Nonempty) :
    3 * 4 ^ (I.card - 1) ≤
      Module.finrank k (representation k m I σ (torusHom m u) - LinearMap.id).range := by
  classical
  obtain ⟨i, hi⟩ := hI
  have hf := fixed_card_le k m σ u I hu ⟨i, hi⟩
  have hm := moved_card_le_rank k m σ u I
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (I → Fin 4))) (fun a => eigenvalue k m σ u I a = 1)
  have heq : Finset.univ.filter (fun a : I → Fin 4 => ¬ eigenvalue k m σ u I a = 1) =
      Finset.univ.filter (fun a : I → Fin 4 => eigenvalue k m σ u I a ≠ 1) := by
    ext a
    simp only [Finset.mem_filter]
  rw [heq] at hc
  have hn : 1 ≤ I.card := Finset.one_le_card.mpr ⟨i, hi⟩
  have hd : 4 ^ I.card = 4 * 4 ^ (I.card - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe] at hc
  rw [hd] at hc
  omega

/-- The proved Frobenius support bound is strong enough for the correction inequality. -/
theorem tensor_correction_inequality (hu : u ≠ 1) (hm : 2 ≤ m) (hI : 2 ≤ I.card) :
    2 + 2 * Module.finrank k (groupCohomology (Rep.of (representation k m I σ)) 1) ≤
      Module.finrank k (representation k m I σ (torusHom m u) - LinearMap.id).range := by
  have hH := SuzukiTensorWeightCount.finrank_H1_le_five m I k σ hm hI
  have hmove := three_quarters_le_rank k m σ u I hu
    (Finset.card_pos.mp (by omega))
  have he : I.card - 1 = I.card - 2 + 1 := by omega
  rw [he, pow_succ] at hmove
  have hp : 1 ≤ 4 ^ (I.card - 2) := Nat.one_le_pow _ _ (by omega)
  omega

end Kourovka2135.SuzukiTensorMovingRank

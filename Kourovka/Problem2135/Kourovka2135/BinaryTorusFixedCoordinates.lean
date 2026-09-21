import Kourovka2135.BinaryTorusCharacterWeights
import Kourovka2135.DiagonalFixedCoordinates

/-! Exact low-degree bounds for the concrete binary torus characters.

The fixed-coordinate indices are identified with the already classified
modular-weight indices. The linear-algebra consequences here are generic;
applications to cohomology must supply the actual equivariant coordinate map.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinaryTorusFixedCoordinates
open BinaryCochainGraded BinarySurvivorWeights DiagonalFixedCoordinates
variable (k : Type*) [Field k] {f : ℕ} (I : Finset (Fin f))

/-- The scalar character on an actual surviving exponent. -/
def character (r : kˣ) (n : ℕ) (a : SurvivorIndex I n) : k :=
  BinaryCochainTorus.blockWeight k I ((r ^ BinaryTensorTorus.binaryWeight I)⁻¹)
    (BinaryExteriorScaling.torusCoefficients k f r) a.val.val

/-- Weight-one coordinates are precisely the modular-weight indices. -/
def fixedIndexEquiv (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (n : ℕ) :
    FixedIndex (character k I r n) ≃ ZeroWeightIndex I n where
  toFun a := ⟨a.val,
    (BinaryTorusCharacterWeights.scalar_blockWeight_eq_one_iff k I r a.val.val.val hr).mp
      a.property⟩
  invFun a := ⟨a.val,
    (BinaryTorusCharacterWeights.scalar_blockWeight_eq_one_iff k I r a.val.val.val hr).mpr
      a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem subsingleton_fixedIndex_one (r : kˣ) (hr : orderOf r = 2 ^ f - 1)
    (hf : 2 ≤ f) : Subsingleton (FixedIndex (character k I r 1)) := by
  let := subsingleton_degree_one hf I
  exact (fixedIndexEquiv k I r hr 1).injective.subsingleton

theorem isEmpty_fixedIndex_one (r : kˣ) (hr : orderOf r = 2 ^ f - 1)
    (hf : 2 ≤ f) (hI : I.card ≠ 1) : IsEmpty (FixedIndex (character k I r 1)) := by
  let := isEmpty_degree_one hf I hI
  exact ⟨fun a => isEmptyElim (fixedIndexEquiv k I r hr 1 a)⟩

theorem subsingleton_fixedIndex_two (r : kˣ) (hr : orderOf r = 2 ^ f - 1)
    (hf : 3 ≤ f) (i : Fin f) :
    Subsingleton (FixedIndex (character k {i} r 2)) := by
  let := subsingleton_degree_two hf i
  exact (fixedIndexEquiv k {i} r hr 2).injective.subsingleton

theorem isEmpty_fixedIndex_two_at_two (r : kˣ) (hr : orderOf r = 2 ^ 2 - 1)
    (i : Fin 2) : IsEmpty (FixedIndex (character k {i} r 2)) := by
  let := isEmpty_degree_two_at_two i
  exact ⟨fun a => isEmptyElim (fixedIndexEquiv k {i} r hr 2 a)⟩

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Any injective coordinate map with these proved eigenvalues gives the H1-size bound. -/
theorem finrank_fixed_one_le (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 2 ≤ f)
    (T : V →ₗ[k] V) (q : V →ₗ[k] (SurvivorIndex I 1 → k))
    (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k I r 1 a * q v a) :
    Module.finrank k (T - LinearMap.id).ker ≤ 1 := by
  let := subsingleton_fixedIndex_one k I r hr hf
  exact (finrank_fixed_le T q (character k I r 1) hq hdiag).trans
    (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)

/-- Nonsingleton supports have no fixed vectors once actual equivariance is proved. -/
theorem fixed_one_eq_bot (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 2 ≤ f)
    (hI : I.card ≠ 1) (T : V →ₗ[k] V)
    (q : V →ₗ[k] (SurvivorIndex I 1 → k)) (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k I r 1 a * q v a) :
    (T - LinearMap.id).ker = ⊥ := by
  let := isEmpty_fixedIndex_one k I r hr hf hI
  exact fixedSpace_eq_bot_of_no_weight_one T q (character k I r 1) hq hdiag
    (fun a ha => isEmptyElim (⟨a, ha⟩ : FixedIndex (character k I r 1)))

/-- The natural support gives at most one fixed degree-two coordinate. -/
theorem finrank_fixed_two_le (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 3 ≤ f)
    (i : Fin f) (T : V →ₗ[k] V) (q : V →ₗ[k] (SurvivorIndex {i} 2 → k))
    (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k {i} r 2 a * q v a) :
    Module.finrank k (T - LinearMap.id).ker ≤ 1 := by
  let := subsingleton_fixedIndex_two k r hr hf i
  exact (finrank_fixed_le T q (character k {i} r 2) hq hdiag).trans
    (Fintype.card_le_one_iff_subsingleton.mpr inferInstance)

/-- At extension degree two, the natural support gives no fixed degree-two vector. -/
theorem fixed_two_at_two_eq_bot (r : kˣ) (hr : orderOf r = 2 ^ 2 - 1)
    (i : Fin 2) (T : V →ₗ[k] V) (q : V →ₗ[k] (SurvivorIndex {i} 2 → k))
    (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k {i} r 2 a * q v a) :
    (T - LinearMap.id).ker = ⊥ := by
  let := isEmpty_fixedIndex_two_at_two k r hr i
  exact fixedSpace_eq_bot_of_no_weight_one T q (character k {i} r 2) hq hdiag
    (fun a ha => isEmptyElim (⟨a, ha⟩ : FixedIndex (character k {i} r 2)))

end Kourovka2135.BinaryTorusFixedCoordinates

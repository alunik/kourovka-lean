import Kourovka2135.SuzukiBrandlOrders
import Kourovka2135.SuzukiTorusSpectrum
import Kourovka2135.SuzukiSplitSylow
import Kourovka2135.BinarySplitGoodSetGeneration

/-! Actual split-prime generating good sets in the concrete Suzuki group.
Proper-subgroup solubility is the explicit structural hypothesis. All order,
conjugacy, generation and matrix facts are derived in the actual group. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiSplitGoodSet

open Matrix Polynomial SuzukiTorusMovingRank SuzukiBrandlMatrices SuzukiBrandlCommutator
open SuzukiBrandlOrders
open BenderSuzuki.MatrixGroups
open scoped Matrix MatrixGroups Polynomial

variable {r : ℕ} [Fact r.Prime]

def weyl (m : ℕ) : G m :=
  ⟨SuzukiWeylGL m, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

theorem weyl_conj_torus (m : ℕ) (u : (K m)ˣ) :
    weyl m * torusHom m u * (weyl m)⁻¹ = torusHom m u⁻¹ := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, torusHom, SuzukiTorusGL, SuzukiTorusMatrix,
      SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
      inv_pow]

theorem isConj_torus_inverse (m : ℕ) (u : (K m)ˣ) :
    IsConj (torusHom m u) (torusHom m u⁻¹) :=
  isConj_iff.mpr ⟨weyl m, weyl_conj_torus m u⟩

theorem charpoly_eq_of_isConj (m : ℕ) {a b : G m} (h : IsConj a b) :
    (matrixHom m a).charpoly = (matrixHom m b).charpoly := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  rw [← hg, map_mul, map_mul]
  symm
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem lambda_injective (m : ℕ) : Function.Injective (lambda m) := by
  intro x z hxz
  apply Units.ext
  apply (iterateFrobeniusEquiv (K m) 2 m).injective
  simpa only [iterateFrobeniusEquiv_def, iterateFrobenius_def] using hxz

theorem isConj_torus_of_charpoly (m : ℕ) (hr : r ∣ SuzukiGeometry.q m - 1)
    (u : (K m)ˣ) (hu : orderOf u = r) (g : G m) (hg : orderOf g = r)
    (hc : (matrixHom m g).charpoly = (matrixHom m (torusHom m u)).charpoly) :
    IsConj (torusHom m u) g := by
  obtain ⟨v, _, hv⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime m hr g hg
  have hune : u ≠ 1 := by
    rintro rfl
    exact (Fact.out : r.Prime).ne_one (by simpa using hu.symm)
  have hpoly := (charpoly_eq_of_isConj m hv).trans hc
  rw [charpoly_torus, charpoly_torus] at hpoly
  rcases SuzukiTorusSpectrum.eq_or_inv_of_polynomial_eq (tits m) (tits_sq m)
    (lambda m u) (lambda m v) (pow_ne_zero _ u.ne_zero)
    (middle_ne_one m u hune) hpoly.symm with h | h
  · have hvu : v = u := lambda_injective m h
    rwa [hvu] at hv
  · have hvu : v = u⁻¹ := lambda_injective m (by simpa [lambda, inv_pow] using h)
    rw [hvu] at hv
    exact (isConj_torus_inverse m u).trans hv

theorem commutator_isConj_square (m : ℕ) (hr : r ∣ SuzukiGeometry.q m - 1)
    (u : (K m)ˣ) (hu : orderOf u = r) :
    IsConj (torusHom m (u ^ 2)) (paperCommutator (torusHom m u) (partner m u)) := by
  have hu2 : orderOf (u ^ 2) = r :=
    (BinarySplitTorusGoodPair.orderOf_square u).trans hu
  apply isConj_torus_of_charpoly m hr (u ^ 2) hu2 _
    (commutator_order m r Fact.out u hu)
  rw [charpoly_commutator, charpoly_torus]
  congr 3
  simp only [lambda, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]

def orderSet (m r : ℕ) : Set (G m) := {g | orderOf g = r}

theorem exists_pair_torus (m : ℕ) (hr : r ∣ SuzukiGeometry.q m - 1)
    (v : (K m)ˣ) (hv : orderOf v = r) :
    ∃ a ∈ orderSet m r, ∃ b ∈ orderSet m r,
      paperCommutator a b = torusHom m v := by
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective
    (BinarySplitTorusGoodPair.square_injective (F := K m)) v
  change u ^ 2 = v at hu
  have huo : orderOf u = r := by
    rw [← BinarySplitTorusGoodPair.orderOf_square u, hu, hv]
  obtain ⟨g, hg⟩ := isConj_iff.mp (commutator_isConj_square m hr u huo).symm
  let f : G m ≃* G m := MulAut.conj g
  refine ⟨f (torusHom m u), ?_, f (partner m u), ?_, ?_⟩
  · change orderOf (f _) = r
    rw [f.orderOf_eq, orderOf_torus, huo]
  · change orderOf (f _) = r
    rw [f.orderOf_eq, partner_order m r Fact.out u huo]
  · change paperCommutator (f.toMonoidHom (torusHom m u))
      (f.toMonoidHom (partner m u)) = _
    rw [← map_paperCommutator f.toMonoidHom]
    exact hg.trans (congrArg (torusHom m) hu)

theorem isGeneratingGoodSet (m : ℕ) (hr : r ∣ SuzukiGeometry.q m - 1)
    (hsolv : ∀ H : Subgroup (G m), H < ⊤ → Group.IsSolvable H) :
    Kourovka2135.IsGeneratingGoodSet (orderSet m r) := by
  intro t ht
  obtain ⟨v, hv, hvt⟩ := SuzukiSplitSylow.exists_isConj_torus_of_order_prime m hr t ht
  obtain ⟨a, ha, b, hb, hab⟩ := exists_pair_torus m hr v hv
  have hgen : Subgroup.closure ({a, b} : Set (G m)) = ⊤ := by
    apply BinarySplitGoodSetGeneration.closure_eq_top_of_three_prime_orders hsolv
      (SuzukiSplitSylow.subgroup_sylow_isCyclic m hr) a b ha hb
    rw [hab, orderOf_torus, hv]
  obtain ⟨g, hg⟩ := isConj_iff.mp hvt
  let f : G m ≃* G m := MulAut.conj g
  refine ⟨f a, ?_, f b, ?_, ?_, ?_⟩
  · exact (f.orderOf_eq a).trans ha
  · exact (f.orderOf_eq b).trans hb
  · change paperCommutator (f.toMonoidHom a) (f.toMonoidHom b) = _
    rw [← map_paperCommutator f.toMonoidHom, hab]
    exact hg
  · change Subgroup.closure ({f.toMonoidHom a, f.toMonoidHom b} : Set (G m)) = ⊤
    rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective f.toMonoidHom f.surjective

end Kourovka2135.SuzukiSplitGoodSet

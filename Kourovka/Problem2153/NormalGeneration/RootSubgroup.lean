import Kourovka.Problem2153.RootRelations
import Kourovka.Problem2153.RankOne.SimpleWeyl
import Mathlib.GroupTheory.Subgroup.Centralizer

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem
open scoped commutatorElement
open RootRelations

private theorem last_product_symmetric : ∀ a b : Fin 8,
    productCoordinates 11 a b = productCoordinates 11 b a := by decide +kernel

theorem root11_commute (a b : Fin 8) : Commute (root 11 a) (root 11 b) := by
  change root 11 a * root 11 b = root 11 b * root 11 a
  rw [root_product, root_product, last_product_symmetric]

theorem Z_abelian : IsMulCommutative Z := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact (root11_commute a b).eq

theorem root_commute_root11 (i : Fin 12) (a b : Fin 8) : Commute (root i a) (root 11 b) := by
  by_cases hi : i = 11
  · subst i; exact root11_commute a b
  have hil : i < 11 := by omega
  have hc := root_commutator i 11 a b hil
  have hz : commutatorCoordinates i 11 a b = fun _ => 0 := by
    funext k
    exact commutator_support i 11 k a b hil (by omega)
  rw [hz, coordinateGroup_zero] at hc
  have he : ⁅(root i a)⁻¹, (root 11 b)⁻¹⁆ = 1 := by
    simpa only [commutatorElement_def, inv_inv] using hc
  have he' := (commutatorElement_eq_one_iff_commute.mp he).inv_left.inv_right
  simpa only [inv_inv] using he'

theorem U_le_centralizer_Z : U ≤ Subgroup.centralizer (Z : Set G) := by
  rw [Z, Subgroup.centralizer_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨curve, hcurve, a, rfl⟩ _ ⟨b, rfl⟩
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hcurve
  rcases hcurve with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact (root_commute_root11 _ a b).symm.eq

theorem Z_le_U : Z ≤ U := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  exact root_mem_U 11 a

theorem Z_le_P : Z ≤ P := Z_le_U.trans (le_sup_left.trans le_sup_left)

private theorem rightConj_mem_Z_torus {z : G} (hz : z ∈ Z) (a b : Fin 7) :
    rightConj z (torus a b) ∈ Z := by
  apply Collection.rightConj_mem_closure_of_generators _ Z (torus a b) ?_ hz
  rintro _ ⟨c, rfl⟩
  change rightConj (root 11 c) (torus a b) ∈ Z
  rw [root_conj_torus]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem H_le_normalizer_Z : H ≤ Subgroup.normalizer (Z : Set G) := by
  intro h hh
  obtain ⟨a,b,rfl⟩ := exists_torus_of_mem_H hh
  rw [Subgroup.mem_normalizer_iff'']
  intro z
  constructor
  · exact fun hz => rightConj_mem_Z_torus hz a b
  · intro hz
    have hi := rightConj_mem_Z_torus hz (indexInv a) (indexInv b)
    change rightConj (rightConj z (torus a b)) (torus (indexInv a) (indexInv b)) ∈ Z at hi
    rw [← torus_inv, rightConj_inv_cancel] at hi
    exact hi

theorem r_mem_centralizer_Z : r ∈ Subgroup.centralizer (Z : Set G) := by
  rw [Z, Subgroup.centralizer_closure]
  rintro _ ⟨a, rfl⟩
  have h : rightConj (root 11 a) r = root 11 a := by
    simpa [RankOne.rIndex] using RankOne.root_conj_r 11 (by decide) (by decide) a
  exact ((rightConj_fixed_iff _ _).mp h).eq

theorem P_le_normalizer_Z : P ≤ Subgroup.normalizer (Z : Set G) := by
  apply sup_le
  · exact sup_le (U_le_centralizer_Z.trans (Subgroup.centralizer_le_normalizer _)) H_le_normalizer_Z
  · apply (Subgroup.closure_le _).mpr
    rintro _ (rfl : _ = r)
    exact Subgroup.centralizer_le_normalizer _ r_mem_centralizer_Z

#print axioms Z_abelian
#print axioms U_le_centralizer_Z
#print axioms P_le_normalizer_Z
end Kourovka.Problem2153.RootSystem

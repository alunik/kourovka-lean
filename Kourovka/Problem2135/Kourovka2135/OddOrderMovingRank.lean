import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.CharP.Two

/-! A nonidentity odd-order action of determinant one in characteristic two has
moving rank at least two. Perfect groups supply determinant one. The group itself
need not be finite, and the representation need not be faithful: nontriviality of
the action is explicit, with a separate faithful-representation corollary.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.OddOrderMovingRank

variable {K V : Type*} [Field K] [CharP K 2]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- A determinant-one automorphism moving at most one dimension in characteristic
two is a transvection, hence has square one. -/
theorem pow_two_eq_one_of_det_eq_one_of_moving_rank_le_one
    (e : V ≃ₗ[K] V) (hdet : LinearEquiv.det e = 1)
    (hrank : Module.finrank K (e.toLinearMap - LinearMap.id).range ≤ 1) :
    e ^ 2 = 1 := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hrank
  have hdet' : LinearMap.det e.toLinearMap = 1 := by
    simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val hdet
  have hfv : f v = 0 := by
    rw [he, LinearMap.transvection.det] at hdet'
    exact add_left_cancel (by simpa only [add_zero] using hdet' : 1 + f v = 1 + 0)
  have happ (x : V) : e x = x + f x • v := by
    exact congrArg (fun T : V →ₗ[K] V => T x) he
  rw [pow_two]
  ext x
  change e (e x) = x
  simp only [happ, map_add, map_smul, smul_eq_mul, hfv, mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

/-- The determinant-one rank bound needs only an odd exponent killing the action. -/
theorem two_le_moving_rank_of_det_eq_one_of_odd_pow
    (e : V ≃ₗ[K] V) (hdet : LinearEquiv.det e = 1)
    (n : ℕ) (hn : Odd n) (hpow : e ^ n = 1) (hne : e ≠ 1) :
    2 ≤ Module.finrank K (e.toLinearMap - LinearMap.id).range := by
  by_contra h
  have hsquare := pow_two_eq_one_of_det_eq_one_of_moving_rank_le_one e hdet
    (show Module.finrank K (e.toLinearMap - LinearMap.id).range ≤ 1 by omega)
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul hpow hn 1
  apply hne
  simpa only [pow_one, pow_mul, hsquare, one_pow] using hm

variable {G : Type*} [Group G]

/-- The canonical automorphism-valued form of the actual representation. -/
def actionEquivHom (ρ : Representation K G V) : G →* (V ≃ₗ[K] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).toMonoidHom.comp ρ.asGroupHom

omit [CharP K 2] [Module.Finite K V] in
@[simp] theorem actionEquivHom_toLinearMap (ρ : Representation K G V) (g : G) :
    (actionEquivHom ρ g).toLinearMap = ρ g := by
  simp [actionEquivHom, Representation.asGroupHom_apply]

omit [CharP K 2] [Module.Finite K V] in
/-- Every determinant character of a perfect group is trivial. -/
theorem det_eq_one_of_perfect [Group.IsPerfect G]
    (σ : G →* (V ≃ₗ[K] V)) (g : G) : LinearEquiv.det (σ g) = 1 := by
  exact Abelianization.commutator_subset_ker (LinearEquiv.det.comp σ)
    (Group.IsPerfect.mem_commutator (g := g))

/-- An odd exponent for a perfect-group element gives the moving-rank bound
whenever its actual action is nontrivial. -/
theorem two_le_moving_rank_of_perfect_of_odd_pow [Group.IsPerfect G]
    (ρ : Representation K G V) (g : G) (n : ℕ) (hn : Odd n)
    (hg : g ^ n = 1) (hne : ρ g ≠ 1) :
    2 ≤ Module.finrank K (ρ g - LinearMap.id).range := by
  have hne' : actionEquivHom ρ g ≠ 1 := by
    intro h
    apply hne
    rw [← actionEquivHom_toLinearMap ρ g, h]
    rfl
  have hpow : actionEquivHom ρ g ^ n = 1 := by
    rw [← map_pow, hg, map_one]
  have h := two_le_moving_rank_of_det_eq_one_of_odd_pow (actionEquivHom ρ g)
    (det_eq_one_of_perfect (actionEquivHom ρ) g) n hn hpow hne'
  change 2 ≤ Module.finrank K ((actionEquivHom ρ g).toLinearMap - LinearMap.id).range at h
  rw [actionEquivHom_toLinearMap] at h
  exact h

/-- Nonidentity odd-order actions of perfect groups move at least two dimensions.
No finiteness or faithfulness assumption on the group is needed. -/
theorem two_le_moving_rank_of_perfect [Group.IsPerfect G]
    (ρ : Representation K G V) (g : G) (hodd : Odd (orderOf g)) (hne : ρ g ≠ 1) :
    2 ≤ Module.finrank K (ρ g - LinearMap.id).range :=
  two_le_moving_rank_of_perfect_of_odd_pow ρ g (orderOf g) hodd
    (pow_orderOf_eq_one g) hne

/-- The sharp statement for arbitrary representations: an odd-order element
acts trivially or moves at least two dimensions. -/
theorem action_eq_one_or_two_le_moving_rank [Group.IsPerfect G]
    (ρ : Representation K G V) (g : G) (hodd : Odd (orderOf g)) :
    ρ g = 1 ∨ 2 ≤ Module.finrank K (ρ g - LinearMap.id).range := by
  by_cases h : ρ g = 1
  · exact Or.inl h
  · exact Or.inr (two_le_moving_rank_of_perfect ρ g hodd h)

/-- Faithfulness turns nontriviality of the group element into nontriviality of
its action, so gives the usual nonidentity-element formulation. -/
theorem two_le_moving_rank_of_perfect_of_injective [Group.IsPerfect G]
    (ρ : Representation K G V) (hρ : Function.Injective ρ)
    (g : G) (hodd : Odd (orderOf g)) (hne : g ≠ 1) :
    2 ≤ Module.finrank K (ρ g - LinearMap.id).range := by
  apply two_le_moving_rank_of_perfect ρ g hodd
  intro h
  apply hne
  exact hρ (by simpa only [map_one] using h)

end Kourovka2135.OddOrderMovingRank

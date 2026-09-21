import Kourovka2135.MinimalCommutatorSurjectivity
import Kourovka2135.CommutatorBilinearMap

/-! Scalar alternating forms obtained from a minimal noncentral kernel. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]

/-- Postcomposition of the commutator pairing with a prime-field functional. -/
def scalarCommutatorForm (hD : commutator G ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (G ⧸ Subgroup.center G)]
    [IsElementaryAbelian p (commutator G)]
    (ell : Additive (commutator G) →ₗ[ZMod p] ZMod p) :
    Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p]
      Additive (G ⧸ Subgroup.center G) →ₗ[ZMod p] ZMod p where
  toFun x := ell.comp (centralCommutatorBilinearMap hD p x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem scalarCommutatorForm_alternating (hD : commutator G ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (G ⧸ Subgroup.center G)]
    [IsElementaryAbelian p (commutator G)]
    (ell : Additive (commutator G) →ₗ[ZMod p] ZMod p)
    (x : Additive (G ⧸ Subgroup.center G)) : scalarCommutatorForm hD p ell x x = 0 := by
  change ell (centralCommutatorBilinearMap hD p x x) = 0
  rw [centralCommutatorBilinearMap_self, map_zero]

theorem minimal_noncentral_commutator_le_internal_center
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    commutator N ≤ Subgroup.center N := by
  have hD := minimal_noncentral_commutator_le_center N hmin
  rw [← Subgroup.map_subtype_commutator] at hD
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp
    (hD (Subgroup.mem_map_of_mem N.subtype hx)) y)

theorem minimal_noncentral_bilinear_apply_surjective
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian p (commutator N)]
    (x : Additive (N ⧸ Subgroup.center N)) (hx : x ≠ 0) :
    Function.Surjective (centralCommutatorBilinearMap
      (minimal_noncentral_commutator_le_internal_center N hmin) p x) := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
  have hac : a ∉ Subgroup.center N := by
    intro hac
    apply hx
    change x.toMul = 1
    rw [← ha]
    exact (QuotientGroup.eq_one_iff _).mpr hac
  intro t
  obtain ⟨b, hb⟩ := exists_paperCommutator_eq_of_minimal_noncentral N hmin a hac t.toMul
  refine ⟨Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) b), ?_⟩
  change centralCommutatorPairingHom _ x.toMul
    (QuotientGroup.mk' (Subgroup.center N) b) = t.toMul
  rw [← ha]
  exact Subtype.ext hb

theorem minimal_noncentral_scalarCommutatorForm_nondegenerate
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian p (commutator N)]
    (ell : Additive (commutator N) →ₗ[ZMod p] ZMod p) (hell : ell ≠ 0)
    {x : Additive (N ⧸ Subgroup.center N)}
    (hx : ∀ y, scalarCommutatorForm
      (minimal_noncentral_commutator_le_internal_center N hmin) p ell x y = 0) : x = 0 := by
  by_contra hxn
  apply hell
  apply LinearMap.ext
  intro t
  obtain ⟨y, rfl⟩ := minimal_noncentral_bilinear_apply_surjective N hmin p x hxn t
  exact hx y

end Kourovka2135

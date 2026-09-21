import Kourovka2135.MinimalSymplecticForm
import Kourovka2135.NormalQuotientRepresentation
import Kourovka2135.RelativeCongruence
import Kourovka2135.LinearDualCorrection
import Mathlib.RepresentationTheory.Intertwining

/-! Invariant scalar commutator forms and self-duality of the actual center
quotient representation of a nonabelian minimal kernel. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (p : ℕ) [Fact p.Prime]
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian p (commutator N)]

theorem minimal_commutatorBilinearMap_invariant (g : G)
    (x y : Additive (N ⧸ Subgroup.center N)) :
    centralCommutatorBilinearMap (minimal_noncentral_commutator_le_internal_center N hmin) p
      (normalQuotientRepresentation N (Subgroup.center N) p g x)
      (normalQuotientRepresentation N (Subgroup.center N) p g y) =
    centralCommutatorBilinearMap (minimal_noncentral_commutator_le_internal_center N hmin) p x y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) y.toMul
  have hxa : x = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) a) := ha.symm
  have hyb : y = Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) b) := hb.symm
  rw [hxa, hyb]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change paperCommutator (MulAut.conjNormal g a) (MulAut.conjNormal g b) =
    paperCommutator a b
  have hm : paperCommutator (MulAut.conjNormal g a) (MulAut.conjNormal g b) =
      MulAut.conjNormal g (paperCommutator a b) := by
    simp only [paperCommutator, map_mul, map_inv]
  rw [hm]
  have hD : (commutator N).map N.subtype ≤ Subgroup.center G := by
    rw [Subgroup.map_subtype_commutator]
    exact minimal_noncentral_commutator_le_center N hmin
  have hc : ((paperCommutator a b : N) : G) ∈ Subgroup.center G :=
    hD (Subgroup.mem_map_of_mem N.subtype (paperCommutator_mem_commutator a b))
  apply Subtype.ext
  change g * ((paperCommutator a b : N) : G) * g⁻¹ = ((paperCommutator a b : N) : G)
  rw [Subgroup.mem_center_iff.mp hc g]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

def minimalScalarCommutatorIntertwiner
    (ell : Module.Dual (ZMod p) (Additive (commutator N))) :
    (normalQuotientRepresentation N (Subgroup.center N) p).IntertwiningMap
      (normalQuotientRepresentation N (Subgroup.center N) p).dual :=
  ⟨scalarCommutatorForm (minimal_noncentral_commutator_le_internal_center N hmin) p ell, by
      intro g
      ext x y
      let ρ := normalQuotientRepresentation N (Subgroup.center N) p
      have he := congrArg ell (minimal_commutatorBilinearMap_invariant N hmin p g x (ρ g⁻¹ y))
      rw [ρ.self_inv_apply] at he
      exact he⟩

theorem minimalScalarCommutatorIntertwiner_injective
    (ell : Module.Dual (ZMod p) (Additive (commutator N))) (hell : ell ≠ 0) :
    Function.Injective (minimalScalarCommutatorIntertwiner N hmin p ell) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro x hx
  change x = 0
  apply minimal_noncentral_scalarCommutatorForm_nondegenerate N hmin p ell hell
  intro y
  exact congrArg (fun f : Module.Dual (ZMod p) (Additive (N ⧸ Subgroup.center N)) => f y) hx

noncomputable def minimalScalarCommutatorEquiv [Finite G]
    (ell : Module.Dual (ZMod p) (Additive (commutator N))) (hell : ell ≠ 0) :
    (normalQuotientRepresentation N (Subgroup.center N) p).Equiv
      (normalQuotientRepresentation N (Subgroup.center N) p).dual :=
  (minimalScalarCommutatorIntertwiner N hmin p ell).ofBijective
    ⟨minimalScalarCommutatorIntertwiner_injective N hmin p ell hell,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ZMod p)
          (V := Additive (N ⧸ Subgroup.center N))).symm).mp
        (minimalScalarCommutatorIntertwiner_injective N hmin p ell hell)⟩

end Kourovka2135

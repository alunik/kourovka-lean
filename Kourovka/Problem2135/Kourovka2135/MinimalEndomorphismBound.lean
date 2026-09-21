import Kourovka2135.MinimalDerivedDimension
import Kourovka2135.QuotientIntertwiners
import Kourovka2135.MinimalKernelPAction

/-! The derived-dimension bound on the actual quotient-group representation
on N/Z(N), after factoring through a normal p-subgroup. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
variable [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
variable [IsElementaryAbelian p (commutator N)]

def minimalCenterRepresentation :
    Representation (ZMod p) (G ⧸ R) (Additive (N ⧸ Subgroup.center N)) :=
  quotientRepresentation (normalQuotientRepresentation N (Subgroup.center N) p) R (by
    intro r x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
    change normalQuotientRepresentation N (Subgroup.center N) p (r : G)
      (Additive.ofMul x.toMul) = Additive.ofMul x.toMul
    rw [← ha]
    exact minimal_centerQuotient_pSubgroup_action (Fact.out : p.Prime) N hN hmin R hR r a)

theorem minimal_derived_finrank_le_quotient_endomorphism_finrank
    (hnonabelian : ¬ IsMulCommutative N) :
    let σ := minimalCenterRepresentation N hN hmin R hR
    Module.finrank (ZMod p) (Additive (commutator N)) ≤
      Module.finrank (ZMod p) (σ.IntertwiningMap σ) := by
  let : Group.IsNilpotent N := hN.isNilpotent
  have he := (quotientEndomorphismEquiv
    (normalQuotientRepresentation N (Subgroup.center N) p) R
    (show ∀ (r : R) x, normalQuotientRepresentation N (Subgroup.center N) p (r : G) x = x from
      by
        intro r x
        obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) x.toMul
        change normalQuotientRepresentation N (Subgroup.center N) p (r : G)
          (Additive.ofMul x.toMul) = Additive.ofMul x.toMul
        rw [← ha]
        exact minimal_centerQuotient_pSubgroup_action (Fact.out : p.Prime) N hN hmin R hR r a)).finrank_eq
  change Module.finrank (ZMod p) (Additive (commutator N)) ≤
    Module.finrank (ZMod p) ((minimalCenterRepresentation N hN hmin R hR).IntertwiningMap
      (minimalCenterRepresentation N hN hmin R hR))
  change Module.finrank (ZMod p)
    ((minimalCenterRepresentation N hN hmin R hR).IntertwiningMap
      (minimalCenterRepresentation N hN hmin R hR)) = _ at he
  rw [he]
  exact minimal_derived_finrank_le_endomorphism_finrank N hmin p hnonabelian

end Kourovka2135

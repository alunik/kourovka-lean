import Kourovka2135.MinimalKernelIrreducibility
import Kourovka2135.NormalPSubgroupRepresentation
import Mathlib.Algebra.Field.ZMod

/-! Normal p-subgroups act trivially on the center quotient of a minimal
noncentral normal p-kernel. This proves the factorization needed before using
representations of the simple radical quotient. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type u} [Group G] [Finite G]

theorem minimal_centerQuotient_pSubgroup_action
    {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (r : R) (x : N) :
    QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal (r : G) x) =
      QuotientGroup.mk' (Subgroup.center N) x := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian hp N hN hmin
  rcases subsingleton_or_nontrivial (N ⧸ Subgroup.center N) with ht | ht
  · let := ht
    exact Subsingleton.elim _ _
  · let := ht
    have hcard : p ∣ Nat.card (N ⧸ Subgroup.center N) :=
      (hN.to_quotient (Subgroup.center N)).card_eq_or_dvd.resolve_left
        (Nat.ne_of_gt Finite.one_lt_card)
    let ρ := normalQuotientRepresentation N (Subgroup.center N) p
    have hirr := minimal_centerQuotient_invariant_submodule_eq_bot_or_top N hmin p
    exact normal_pSubgroup_acts_trivially_of_invariant_submodules
      (k := ZMod p) (V := Additive (N ⧸ Subgroup.center N)) hp ρ hirr hcard R hR r
      (Additive.ofMul (QuotientGroup.mk' (Subgroup.center N) x))

end Kourovka2135

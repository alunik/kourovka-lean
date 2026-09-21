import Kourovka2135.MinimalCenterBound
import Kourovka2135.MinimalSymplecticForm

/-! Vanishing of the relevant first cohomology forces a minimal nonabelian
kernel to have center equal to its derived subgroup. No vanishing result for
a simple-group family is assumed or asserted here. -/

set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable {p : ℕ} [Fact p.Prime]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup p R) (hRΦ : R ≤ frattini G)
variable [IsElementaryAbelian p (N ⧸ commutator N)]

abbrev minimalCenterQuotientRepresentation :=
  (minimalAbelianizationRepresentation N hN hnonabelian hmin R hR hRΦ).quotient
    (centerImageSubmodule N (commutator N) p)
    (fixedSubmoduleInvariant _ _
      (minimalAbelianizationRepresentation_center_fixed N hN hnonabelian hmin R hR hRΦ))

theorem minimal_center_eq_commutator_of_h1_vanishes
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    [Subsingleton (groupCohomology
      (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1)] :
    Subgroup.center N = commutator N := by
  let W := centerImageSubmodule N (commutator N) p
  have hd := minimal_center_excess_finrank_le_h1 N hN hnonabelian hmin R hR hRΦ hnoncentral
  change Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) (groupCohomology
    (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1) at hd
  have hzero : Module.finrank (ZMod p) (groupCohomology
    (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [hzero] at hd
  have hW : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hd)
  apply le_antisymm
  · intro z hz
    have hm : Additive.ofMul (QuotientGroup.mk' (commutator N) z) ∈ W := ⟨z, hz, rfl⟩
    rw [hW] at hm
    apply (QuotientGroup.eq_one_iff _).mp
    exact (Submodule.mem_bot (R := ZMod p)).mp hm
  · let : Group.IsNilpotent N := hN.isNilpotent
    exact minimal_noncentral_commutator_le_internal_center N hmin

end Kourovka2135

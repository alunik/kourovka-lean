import Kourovka2135.MinimalCenterRepresentationEquiv
import Kourovka2135.SpecialGoodSetLifting

/-! Vanishing of the dual first cohomology of the actual N/Z(N)
representation makes a minimal nonabelian 2-kernel special. The existing
special-kernel correction then supplies full commutator fibers and whole
generating-good-set lifting. No vanishing result for a simple-group family is asserted.

The center-quotient elementary-abelian instance is explicit because it
appears in the actual representation. It is available from
`minimal_noncentral_quotient_center_isElementaryAbelian`. The corresponding
abelianization instance needed only by the transport proof is derived locally.
-/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]

/-- Actual dual-H1 vanishing forces the internal center to equal the derived subgroup. -/
theorem minimal_center_eq_commutator_of_actual_dual_h1_vanishes
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hnonabelian : ¬ IsMulCommutative N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [Subsingleton (groupCohomology
      (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1)] :
    Subgroup.center N = commutator N := by
  have hnoncentral : ¬ N ≤ Subgroup.center G := by
    intro h
    apply hnonabelian
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (h b.property) a)⟩⟩
  let : IsElementaryAbelian 2 (N ⧸ commutator N) :=
    minimal_noncentral_abelianization_isElementaryAbelian Nat.prime_two N hN hnoncentral hmin
  let e := (minimalCenterRepresentationDualH1Iso
    N hN hnonabelian hmin R hR hRΦ).toLinearEquiv
  let : Subsingleton (groupCohomology
      (Rep.of (minimalCenterQuotientRepresentation N hN hnonabelian hmin R hR hRΦ).dual) 1) :=
    ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩
  exact minimal_center_eq_commutator_of_h1_vanishes
    N hN hnonabelian hmin R hR hRΦ hnoncentral

/-- The actual dual-H1 premise discharges the specialness assumption in the full fiber theorem. -/
theorem exists_paperCommutator_mul_eq_of_minimal_actual_dual_h1_vanishes
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [Subsingleton (groupCohomology
      (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1)]
    [IsSimpleGroup (G ⧸ R)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  exact exists_paperCommutator_mul_eq_of_special_minimal N hN hmin hnonabelian
    (minimal_center_eq_commutator_of_actual_dual_h1_vanishes
      N hN hnonabelian hmin R hR hRΦ) R hR a b hgen hc t

/-- Whole generating good sets lift when the actual dual first cohomology vanishes. -/
theorem IsGeneratingGoodSet.preimage_quotient_of_minimal_actual_dual_h1_vanishes
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hFrattini : N ≤ frattini G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [Subsingleton (groupCohomology
      (Rep.of (minimalCenterRepresentation N hN hmin R hR).dual) 1)]
    [IsSimpleGroup (G ⧸ R)]
    {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y)
    (hYnontrivial : ∀ t : G, QuotientGroup.mk' N t ∈ Y → QuotientGroup.mk' R t ≠ 1) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  exact IsGeneratingGoodSet.preimage_quotient_of_special_minimal N hN hmin hnonabelian
    (minimal_center_eq_commutator_of_actual_dual_h1_vanishes
      N hN hnonabelian hmin R hR hRΦ) hFrattini R hR hY hYnontrivial

end Kourovka2135

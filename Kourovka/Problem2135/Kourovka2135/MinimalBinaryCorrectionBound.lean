import Kourovka2135.BinaryRepresentationCorrection
import Kourovka2135.MinimalH1VanishFiber
import Kourovka2135.MinimalMovingRankCriterion
import Kourovka2135.MinimalIrreducible
import Kourovka2135.MinimalCenterSelfDual

/-! The finite-representation correction bound supplies every element of
the actual minimal nonabelian binary-kernel commutator fiber. -/

set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]

theorem exists_paperCommutator_mul_eq_of_minimal_binary_bound
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (commutator N)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1)
    (hbound : BinaryRepresentationCorrection.Bound
      (minimalCenterRepresentation N hN hmin R hR)
      (QuotientGroup.mk' R (paperCommutator a b))) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  have hnc : ¬ N ≤ Subgroup.center G := by
    intro h
    exact hnonabelian ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (h y.property) x)⟩⟩
  let : IsElementaryAbelian 2 (N ⧸ commutator N) :=
    minimal_noncentral_abelianization_isElementaryAbelian Nat.prime_two N hN hnc hmin
  rcases hbound with hz | hr
  · let := hz
    exact exists_paperCommutator_mul_eq_of_minimal_actual_dual_h1_vanishes
      N hN hmin hnonabelian R hR hRΦ a b hgen hc t
  · exact exists_paperCommutator_mul_eq_of_minimal_end_h1_rank
      N hN hmin hnonabelian R hR hRΦ a b hgen hr t

end Kourovka2135

import Kourovka2135.MinimalCenterRepresentationEquiv
import Kourovka2135.CorrectionMovingRank

/-! A family-ready sufficient moving-rank criterion expressed entirely on
the actual quotient-group representation on N/Z(N) and its dual cohomology. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]

/-- Endomorphism and dual-cohomology dimensions control every commutator fiber
through the minimal nonabelian normal 2-kernel. -/
theorem exists_paperCommutator_mul_eq_of_minimal_end_h1_rank
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    [IsElementaryAbelian 2 (commutator N)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hrank : let ρ := minimalCenterRepresentation N hN hmin R hR
      2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) +
        2 * Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) ≤
          Module.finrank (ZMod 2)
            (ρ (QuotientGroup.mk' R (paperCommutator a b)) - LinearMap.id).range)
    (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let ρ := minimalCenterRepresentation N hN hmin R hR
  have hderived : Module.finrank (ZMod 2) (Additive (commutator N)) ≤
      Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) :=
    minimal_derived_finrank_le_quotient_endomorphism_finrank N hN hmin R hR hnonabelian
  have hcenter : Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
      Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≤
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) :=
    minimal_abelianization_center_finrank_difference_le_actual_h1
      N hN hnonabelian hmin R hR hRΦ
  apply exists_paperCommutator_mul_eq_of_minimal_moving_rank N hN hmin hnonabelian a b hgen _ t
  calc
    _ ≤ 2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) +
        2 * Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left 2 hderived) (Nat.mul_le_mul_left 2 hcenter)
    _ ≤ _ := hrank

end Kourovka2135

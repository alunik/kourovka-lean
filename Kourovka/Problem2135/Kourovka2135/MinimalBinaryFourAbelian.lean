import Kourovka2135.BinaryFourEndCohomology
import Kourovka2135.MinimalBinaryFourSpecial
import Kourovka2135.MinimalFaithful

/-! A minimal noncentral normal subgroup inside the binary Frattini kernel
over the four-parameter SL2 quotient is abelian. A nonabelian subgroup
would give an actual faithful irreducible coefficient with both vanishing
and nonvanishing second cohomology. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open scoped IsMulCommutative

/-- The four-parameter case has no nonabelian minimal kernel, including the special case. -/
theorem minimal_binary_four_isMulCommutative
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    [IsSimpleGroup (G ⧸ R)] (hNR : N ≤ R) (hRΦ : R ≤ frattini G)
    {F : Type} [Field F] [CharP F 2] [Fintype F]
    (e : SLTwo.SL2 F ≃* (G ⧸ R)) (hcard : Fintype.card F = 2 ^ 2) :
    IsMulCommutative N := by
  by_contra hnonabelian
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  have hfaith : Function.Injective ρ :=
    minimal_center_representation_injective_of_perfect N hN hmin hnonabelian R hR
  have ha : ∃ g, ρ g ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : G ⧸ R)
    refine ⟨g, fun he => hg (hfaith ?_)⟩
    simpa only [map_one] using he
  have hzero := BinaryFourEndCohomology.subsingleton_H2_of_group_equiv ρ e hcard ha
  exact minimal_center_h2_not_subsingleton_of_frattini_conjugation_kernel
    N hN hmin hnonabelian R hR hNR hRΦ hzero

end Kourovka2135

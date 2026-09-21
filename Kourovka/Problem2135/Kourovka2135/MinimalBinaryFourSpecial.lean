import Kourovka2135.MinimalConjugationCoordinates
import Kourovka2135.MinimalBinaryNonNaturalFiber
import Kourovka2135.IsotypicFrattiniVanishing

/-! The actual minimal nonabelian kernel over SL2(4) is special.

Its faithful conjugation kernel is a nonzero semisimple isotypic Frattini
kernel, so actual ordinary H2 cannot vanish. If the minimal subgroup were
nonspecial, its actual H1 would be nonzero, forcing that same H2 to vanish
by the proved binary SL2 theorem at f = 2. All kernel structures, actions,
and cohomological identifications used in this contradiction are derived.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative MonoidAlgebra

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable [IsSimpleGroup (G ⧸ R)] (hNR : N ≤ R) (hRΦ : R ≤ frattini G)

variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

local notation "ρ" => minimalCenterRepresentation N hN hmin R hR

include hnonabelian hNR hRΦ in
/-- The actual conjugation kernel forces nonvanishing of the actual
minimal-center H2, with no cohomological or isotypy premise. -/
theorem minimal_center_h2_not_subsingleton_of_frattini_conjugation_kernel :
    ¬ Subsingleton (groupCohomology (Rep.of ρ) 2) := by
  let : IsElementaryAbelian 2 (MinimalConjugationModule.Kernel N R) :=
    MinimalConjugationModule.kernel_isElementaryAbelian N hN hmin hnonabelian R hR
  let : Nontrivial (MinimalConjugationModule.Kernel N R) :=
    MinimalConjugationModule.kernel_nontrivial N hnonabelian R hNR
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let τ := MinimalConjugationModule.representation N hN hmin hnonabelian R hR
  let S := MinimalConjugationModule.extension N hN hmin hnonabelian R hR
  let : IsSemisimpleModule (ZMod 2)[G ⧸ R] τ.asModule :=
    MinimalConjugationCoordinates.isSemisimpleModule N hN hmin hnonabelian R hR
  exact IsotypicFrattiniVanishing.not_subsingleton_H2 τ ρ S
    (MinimalConjugationModule.compatibleAction N hN hmin hnonabelian R hR)
    (MinimalConjugationCoordinates.isIsotypicOfType N hN hmin hnonabelian R hR)
    (MinimalConjugationModule.extension_range_le_frattini N hN hmin hnonabelian R hR hRΦ)

omit [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)] in
include hN hmin hnonabelian hR hNR hRΦ in
/-- For the actual four-element-field quotient, the minimal nonabelian
normal subgroup has center equal to commutator subgroup. -/
theorem minimal_binary_four_center_eq_commutator
    {F : Type} [Field F] [CharP F 2] [Fintype F]
    (e : SLTwo.SL2 F ≃* (G ⧸ R)) (hcard : Fintype.card F = 2 ^ 2) :
    Subgroup.center N = commutator N := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  by_contra hnonspecial
  have hH1 := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hmin R hR hnonabelian hRΦ hnonspecial
  have hH2 := BinarySLTwoGroupEquivCohomology.subsingleton_H2_of_finrank_H1_ne_zero_at_two
    ρ e hcard hH1
  exact minimal_center_h2_not_subsingleton_of_frattini_conjugation_kernel
    N hN hmin hnonabelian R hR hNR hRΦ hH2

end Kourovka2135

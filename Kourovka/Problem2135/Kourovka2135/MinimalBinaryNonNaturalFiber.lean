import Kourovka2135.BinarySLTwoGroupEquivCohomology
import Kourovka2135.MinimalCenterSelfDual
import Kourovka2135.MinimalH1VanishFiber

/-! Full commutator fibers outside the natural-dimension exception.

For the actual minimal-center representation of a binary SL2 quotient,
proved irreducibility and self-duality turn the family cohomology theorem
into actual dual-H1 vanishing. The existing vanishing-to-specialness theorem
then gives whole fibers and generating-good-set lifting.

The elementary-abelian center-quotient instance is explicit only because it
occurs in the actual representation and its dimension. It is supplied by
`minimal_noncentral_quotient_center_isElementaryAbelian`; the analogous
commutator instance needed only in the proof is derived internally.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

local notation "ρ₀" => minimalCenterRepresentation N hN hmin R hR

/-- A nonspecial actual binary kernel has nonzero H1; this needs no family identification. -/
theorem minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    [Group.IsPerfect G] (hnonabelian : ¬ IsMulCommutative N)
    (hRΦ : R ≤ frattini G) (hnonspecial : Subgroup.center N ≠ commutator N) :
    Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ₀) 1) ≠ 0 := by
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  have : FiniteDimensional (ZMod 2) (groupCohomology (Rep.of ρ₀) 1) :=
    GroupCohomologyFieldExtension.finiteDimensional_groupCohomology ρ₀ 0
  intro hz
  let : Subsingleton (groupCohomology (Rep.of ρ₀) 1) :=
    (Module.finrank_zero_iff (R := ZMod 2)).mp hz
  let d := minimalCenterSelfDualCohomologyIso N hN hmin R hR hnonabelian 1
  let : Subsingleton (groupCohomology (Rep.of (Representation.dual ρ₀)) 1) :=
    d.toLinearEquiv.symm.injective.subsingleton
  exact hnonspecial (minimal_center_eq_commutator_of_actual_dual_h1_vanishes
    N hN hnonabelian hmin R hR hRΦ)

variable {F : Type} [Field F] [CharP F 2] [Fintype F]
variable (e : SLTwo.SL2 F ≃* (G ⧸ R))
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)

include e f hcard hf

/-- The nonnatural numerical condition forces actual dual-H1 vanishing. -/
theorem minimal_binary_dual_h1_subsingleton_of_dimension_ne
    (hnonabelian : ¬ IsMulCommutative N)
    (hdim : Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≠
      2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀)) :
    Subsingleton (groupCohomology (Rep.of (Representation.dual ρ₀)) 1) := by
  let : Representation.IsIrreducible ρ₀ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let : IsElementaryAbelian 2 (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian Nat.prime_two N hN hmin
  let : Subsingleton (groupCohomology (Rep.of ρ₀) 1) :=
    BinarySLTwoGroupEquivCohomology.subsingleton_H1_of_coefficient_ne_two_mul_endDegree
      ρ₀ e f hcard hf hdim
  let d := minimalCenterSelfDualCohomologyIso N hN hmin R hR hnonabelian 1
  exact d.toLinearEquiv.symm.injective.subsingleton

variable [Group.IsPerfect G]

/-- A dimension outside the natural exception forces the actual kernel to be special. -/
theorem minimal_binary_center_eq_commutator_of_dimension_ne
    (hnonabelian : ¬ IsMulCommutative N) (hRΦ : R ≤ frattini G)
    (hdim : Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≠
      2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀)) :
    Subgroup.center N = commutator N := by
  let : Subsingleton (groupCohomology (Rep.of (Representation.dual ρ₀)) 1) :=
    minimal_binary_dual_h1_subsingleton_of_dimension_ne
      N hN hmin R hR e f hcard hf hnonabelian hdim
  exact minimal_center_eq_commutator_of_actual_dual_h1_vanishes
    N hN hnonabelian hmin R hR hRΦ

/-- Any nonspecial actual kernel must lie in the precise natural-dimension exception. -/
theorem minimal_binary_dimension_eq_of_center_ne_commutator
    (hnonabelian : ¬ IsMulCommutative N) (hRΦ : R ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N) :
    Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) =
      2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀) := by
  by_contra hdim
  exact hnonspecial (minimal_binary_center_eq_commutator_of_dimension_ne
    N hN hmin R hR e f hcard hf hnonabelian hRΦ hdim)

/-- The actual structural alternative has no family-classification or cohomology premise. -/
theorem minimal_binary_center_eq_commutator_or_dimension_eq
    (hnonabelian : ¬ IsMulCommutative N) (hRΦ : R ≤ frattini G) :
    Subgroup.center N = commutator N ∨
      Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) =
        2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀) := by
  by_cases hs : Subgroup.center N = commutator N
  · exact Or.inl hs
  · exact Or.inr (minimal_binary_dimension_eq_of_center_ne_commutator
      N hN hmin R hR e f hcard hf hnonabelian hRΦ hs)

/-- Outside the natural-dimension exception, every target in the actual fiber is attained. -/
theorem exists_paperCommutator_mul_eq_of_minimal_binary_dimension_ne
    (hnonabelian : ¬ IsMulCommutative N) (hRΦ : R ≤ frattini G)
    [IsSimpleGroup (G ⧸ R)]
    (hdim : Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≠
      2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀))
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hc : QuotientGroup.mk' R (paperCommutator a b) ≠ 1) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let : Subsingleton (groupCohomology (Rep.of (Representation.dual ρ₀)) 1) :=
    minimal_binary_dual_h1_subsingleton_of_dimension_ne
      N hN hmin R hR e f hcard hf hnonabelian hdim
  exact exists_paperCommutator_mul_eq_of_minimal_actual_dual_h1_vanishes
    N hN hmin hnonabelian R hR hRΦ a b hgen hc t

/-- Whole generating good sets lift outside the natural-dimension exception. -/
theorem IsGeneratingGoodSet.preimage_quotient_of_minimal_binary_dimension_ne
    (hnonabelian : ¬ IsMulCommutative N) (hFrattini : N ≤ frattini G)
    (hRΦ : R ≤ frattini G) [IsSimpleGroup (G ⧸ R)]
    (hdim : Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N)) ≠
      2 * Module.finrank (ZMod 2) (Representation.IntertwiningMap ρ₀ ρ₀))
    {Y : Set (G ⧸ N)} (hY : IsGeneratingGoodSet Y)
    (hYnontrivial : ∀ t : G, QuotientGroup.mk' N t ∈ Y → QuotientGroup.mk' R t ≠ 1) :
    IsGeneratingGoodSet ((QuotientGroup.mk' N) ⁻¹' Y) := by
  let : Subsingleton (groupCohomology (Rep.of (Representation.dual ρ₀)) 1) :=
    minimal_binary_dual_h1_subsingleton_of_dimension_ne
      N hN hmin R hR e f hcard hf hnonabelian hdim
  exact IsGeneratingGoodSet.preimage_quotient_of_minimal_actual_dual_h1_vanishes
    N hN hmin hnonabelian hFrattini R hR hRΦ hY hYnontrivial

end Kourovka2135

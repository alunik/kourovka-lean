import Kourovka2135.BinarySLTwoH1TypeUniqueness
import Kourovka2135.MinimalBinaryNonNaturalFiber
import Kourovka2135.MinimalIrreducibleCharacter

/-! The actual native binary-module identification determines the degree
of each irreducible characteristic-zero kernel representation which is
nontrivial on the derived subgroup. No extraspecial-group or faithfulness
assumption is used: off-center vanishing and orthogonality supply the degree.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
variable (hnonspecial : Subgroup.center N ≠ commutator N)
variable {F : Type} [Field F] [Fintype F] [CharP F 2]
local instance primeAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
variable (e : SLTwo.SL2 F ≃* (G ⧸ R))
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)

include hN hmin hnonabelian hR hRΦ hnonspecial e f hcard hf in
/-- The actual center quotient has the cardinality of the genuine native module. -/
theorem minimal_binary_center_quotient_card :
    Nat.card (N ⧸ Subgroup.center N) = (2 ^ f) ^ 2 := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : Representation.IsIrreducible ρ :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  let : Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
    RepresentationGroupEquiv.isIrreducible_comp ρ e
  have hH1 := minimal_binary_h1_finrank_ne_zero_of_center_ne_commutator
    N hN hmin R hR hnonabelian hRΦ hnonspecial
  have hH1' : Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) 1) ≠ 0 := by
    rwa [RepresentationGroupEquiv.finrank_cohomology_comp ρ e 1]
  let a := BinarySLTwoH1TypeUniqueness.naturalEquiv (ρ.comp e.toMonoidHom) f hcard hf hH1'
  calc
    Nat.card (N ⧸ Subgroup.center N) = Nat.card (Fin 2 → F) :=
      (Nat.card_congr a.toLinearEquiv.toEquiv).symm
    _ = (2 ^ f) ^ 2 := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcard]

include hN hmin hnonabelian hR hRΦ hnonspecial e f hcard hf in
/-- Every actual nonlinear irreducible kernel character has degree 2^f. -/
theorem minimal_binary_nonlinear_character_degree
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1) :
    Module.finrank k V = 2 ^ f := by
  have hs := CenterSupportedCharacterDegree.finrank_sq_eq_card_quotient_center ρ
    (MinimalIrreducibleCharacter.character_eq_zero_of_not_mem_center_of_twoGroup
      N hN hmin ρ hderived)
  rw [minimal_binary_center_quotient_card N hN hmin hnonabelian R hR hRΦ
    hnonspecial e f hcard hf] at hs
  exact Nat.pow_left_injective (by decide : 2 ≠ 0) hs

end Kourovka2135

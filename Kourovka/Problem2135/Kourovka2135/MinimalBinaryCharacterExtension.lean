import Kourovka2135.InvariantBinaryRepresentationExtension
import Kourovka2135.MinimalBinaryCharacterDegree
import Kourovka2135.MinimalCharacterEquivalence

/-! The actual minimal nonspecial binary-kernel representation extends.

All invariance, degree and determinant conditions of the concrete finite
intertwiner-cover construction are discharged from the minimal-kernel
hypotheses. No Schur-multiplier, character-extension, or representation
classification assumption is added.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative

/-- Every actual irreducible representation nontrivial on the derived
subgroup of the terminal nonspecial minimal kernel extends to the whole
group, on its original coefficient space and with determinant one. -/
theorem minimal_binary_nonlinear_character_extends
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N) (hNΦ : N ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* (G ⧸ N))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k N V) [ρ.IsIrreducible]
    (hderived : ∃ d : commutator N, ρ (d : N) ≠ 1) :
    ∃ ρhat : Representation k G V,
      ρhat.comp N.subtype = ρ ∧ ∀ g : G, LinearMap.det (ρhat g) = 1 := by
  have hdim : Module.finrank k V = 2 ^ f :=
    minimal_binary_nonlinear_character_degree N hN hmin hnonabelian
      N hN hNΦ hnonspecial e f hcard (by omega) ρ hderived
  exact InvariantBinaryRepresentationExtension.exists_extension N ρ
    (MinimalCharacterEquivalence.coefficientAut_det_eq_one_of_perfect
      N hN hmin hnonabelian ρ hderived)
    (MinimalCharacterEquivalence.nonempty_equiv_conjNormal
      N hN hmin hnonabelian ρ hderived)
    f hdim F f hcard hf e

end Kourovka2135

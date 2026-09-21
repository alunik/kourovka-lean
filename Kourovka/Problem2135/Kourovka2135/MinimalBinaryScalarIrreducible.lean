import Kourovka2135.MinimalBinaryCharacterDegree
import Kourovka2135.RepresentationIrreducibleSubspace

/-! A representation of the actual minimal binary kernel of the forced
nonlinear degree is irreducible as soon as one derived element acts by
a scalar different from one. The proof finds an actual irreducible
subspace and forces its dimension to be the full dimension.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

open scoped IsMulCommutative MonoidAlgebra

/-- The exact degree theorem forces an actual scalar-central representation
of that degree to be irreducible; no induced-irreducibility theorem is assumed. -/
theorem minimal_binary_isIrreducible_of_scalar_derived_action
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) (hRΦ : R ≤ frattini G)
    (hnonspecial : Subgroup.center N ≠ commutator N)
    {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : SLTwo.SL2 F ≃* (G ⧸ R))
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    {k V : Type} [Field k] [IsAlgClosed k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (σ : Representation k N V) (hdim : Module.finrank k V = 2 ^ f)
    (d : commutator N) (c : k) (hc : c ≠ 1)
    (hscalar : σ (d : N) = c • (1 : Module.End k V)) : σ.IsIrreducible := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; positivity)
  apply RepresentationIrreducibleSubspace.isIrreducible_of_irreducible_finrank_eq σ
  intro W hW
  let : W.toRepresentation.IsIrreducible := hW
  let : Nontrivial W.toRepresentation.asModule :=
    IsSimpleModule.nontrivial k[N] W.toRepresentation.asModule
  let : Nontrivial W.toSubmodule :=
    W.toRepresentation.asModuleEquiv.symm.toEquiv.nontrivial
  have hderived : ∃ x : commutator N, W.toRepresentation (x : N) ≠ 1 :=
    ⟨d, RepresentationIrreducibleSubspace.toRepresentation_ne_one_of_scalar
      W (d : N) c hscalar hc⟩
  exact (minimal_binary_nonlinear_character_degree N hN hmin hnonabelian
    R hR hRΦ hnonspecial e f hcard hf W.toRepresentation hderived).trans hdim.symm

end Kourovka2135

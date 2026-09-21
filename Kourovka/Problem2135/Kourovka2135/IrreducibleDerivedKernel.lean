import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.Dimension.Free

/-! An actual irreducible representation is linear exactly when it kills
its group's derived subgroup. The forward implication factors the actual
action through abelianization; the reverse implication uses scalar
endomorphisms in dimension one. No finite-group or characteristic-zero
hypothesis is needed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IrreducibleDerivedKernel

open scoped IsMulCommutative

section Pullback
variable {k G H V : Type*} [Field k] [Monoid G] [Monoid H]
variable [AddCommGroup V] [Module k V]

/-- Surjective group-parameter pullback identifies the actual invariant subspaces. -/
def subrepresentationCompEquiv (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨h, rfl⟩ := hf g
      exact S.apply_mem_toSubmodule h hv }
  invFun S := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g _ hv := S.apply_mem_toSubmodule (f g) hv }
  left_inv S := Subrepresentation.toSubmodule_injective rfl
  right_inv S := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

/-- Irreducibility descends through a surjective parameter homomorphism. -/
theorem isIrreducible_of_comp_surjective (ρ : Representation k G V) (f : H →* G)
    (hf : Function.Surjective f) [Representation.IsIrreducible (ρ.comp f)] :
    ρ.IsIrreducible :=
  (OrderIso.isSimpleOrder_iff (subrepresentationCompEquiv ρ f hf)).mp inferInstance
end Pullback

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/-- Every degree-one representation kills the actual derived subgroup. -/
theorem trivial_on_commutator_of_finrank_eq_one (hdim : Module.finrank k V = 1) :
    ∀ d : commutator G, ρ (d : G) = 1 := by
  let : IsMulCommutative (Units (Module.End k V)) := ⟨⟨by
    intro a b
    apply Units.ext
    change (a : Module.End k V) * (b : Module.End k V) =
      (b : Module.End k V) * (a : Module.End k V)
    obtain ⟨s, hs, _⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (a : Module.End k V)
    obtain ⟨t, ht, _⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (b : Module.End k V)
    change (a : Module.End k V) = s • (1 : Module.End k V) at hs
    change (b : Module.End k V) = t • (1 : Module.End k V) at ht
    rw [hs, ht]
    simp only [mul_smul_comm, mul_one, smul_smul, mul_comm]⟩⟩
  intro d
  have hd : ρ.asGroupHom (d : G) = 1 :=
    Abelianization.commutator_subset_ker ρ.asGroupHom d.property
  simpa only [Representation.asGroupHom_apply, Units.val_one] using
    congrArg (fun a : Units (Module.End k V) => (a : Module.End k V)) hd

variable [FiniteDimensional k V] [IsAlgClosed k] [ρ.IsIrreducible]

/-- An actual irreducible action trivial on the derived subgroup has degree one. -/
theorem finrank_eq_one_of_trivial_on_commutator
    (hderived : ∀ d : commutator G, ρ (d : G) = 1) : Module.finrank k V = 1 := by
  let : Representation.IsTrivial (ρ.comp (commutator G).subtype) :=
    ⟨fun d => hderived d⟩
  let σ : Representation k (Abelianization G) V := ρ.ofQuotient (commutator G)
  have hcomp : σ.comp (Abelianization.of (G := G)) = ρ := by
    ext g v
    rfl
  let : Representation.IsIrreducible (σ.comp (Abelianization.of (G := G))) :=
    hcomp.symm ▸ inferInstance
  let : σ.IsIrreducible := isIrreducible_of_comp_surjective σ
    (Abelianization.of (G := G)) (QuotientGroup.mk'_surjective (commutator G))
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative σ

/-- The degree-one condition is exactly triviality on the actual derived subgroup. -/
theorem finrank_eq_one_iff_trivial_on_commutator :
    Module.finrank k V = 1 ↔ ∀ d : commutator G, ρ (d : G) = 1 :=
  ⟨trivial_on_commutator_of_finrank_eq_one ρ,
    finrank_eq_one_of_trivial_on_commutator ρ⟩

/-- Actual nonlinearity supplies the nontrivial derived action used by trace vanishing. -/
theorem exists_commutator_action_ne_one (hnonlinear : Module.finrank k V ≠ 1) :
    ∃ d : commutator G, ρ (d : G) ≠ 1 := by
  classical
  exact not_forall.mp fun h => hnonlinear (finrank_eq_one_of_trivial_on_commutator ρ h)

end Kourovka2135.IrreducibleDerivedKernel

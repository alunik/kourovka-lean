import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Actual representation and cohomology transport along a group isomorphism.

Pullback changes only the parameter of the group action. Its invariant
subspaces and commuting endomorphisms are identified on the original carrier.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationGroupEquiv

open CategoryTheory

variable {k G H V : Type u} [Field k] [Group G] [Group H]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (e : H ≃* G)

/-- An actual order equivalence on invariant subspaces under group pullback. -/
def subrepresentationEquiv : Subrepresentation (ρ.comp e.toMonoidHom) ≃o Subrepresentation ρ where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g v hv := by
        have h := S.apply_mem_toSubmodule (e.symm g) hv
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply] using h }
  invFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g _ hv := S.apply_mem_toSubmodule (e g) hv }
  left_inv S := Subrepresentation.toSubmodule_injective rfl
  right_inv S := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

/-- Pullback along an actual group isomorphism preserves irreducibility. -/
theorem isIrreducible_comp [ρ.IsIrreducible] :
    Representation.IsIrreducible (ρ.comp e.toMonoidHom) :=
  (OrderIso.isSimpleOrder_iff (subrepresentationEquiv ρ e)).mpr inferInstance

/-- The actual commuting endomorphisms do not change under group pullback. -/
def endomorphismEquiv :
    Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) ≃ₗ[k]
      ρ.IntertwiningMap ρ where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        have h := f.isIntertwining' (e.symm g)
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply] using h }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := f.isIntertwining' (e g) }
  left_inv f := by ext v; rfl
  right_inv f := by ext v; rfl
  map_add' f h := by ext v; rfl
  map_smul' a f := by ext v; rfl

theorem finrank_endomorphism_comp :
    Module.finrank k
      (Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) =
      Module.finrank k (ρ.IntertwiningMap ρ) :=
  (endomorphismEquiv ρ e).finrank_eq

/-- The group isomorphism and identity coefficient map induce actual cohomology isomorphisms. -/
def cohomologyIso (n : ℕ) :
    groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) n ≅
      groupCohomology (Rep.of ρ) n :=
  groupCohomology.mapIso e (LinearEquiv.refl k V) (fun _ => rfl) n

theorem finrank_cohomology_comp (n : ℕ) :
    Module.finrank k (groupCohomology (Rep.of (ρ.comp e.toMonoidHom)) n) =
      Module.finrank k (groupCohomology (Rep.of ρ) n) :=
  (cohomologyIso ρ e n).toLinearEquiv.finrank_eq

end Kourovka2135.RepresentationGroupEquiv

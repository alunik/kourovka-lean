import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-! A multiplicity-one bound detected by actual natural operators.

If every intertwiner commutes with operators P and Q, restriction to their
actual ranges detects intertwiners into an irreducible target whenever Q is
nonzero. A rank-one source operator therefore bounds the entire intertwiner
space by one. Operators arising from the same group-algebra element satisfy
the required commutation automatically. No representation classification,
semisimplicity, or cohomology value is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MultiplicityOneIntertwining

open scoped MonoidAlgebra

variable {k G V W : Type*} [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (τ : Representation k G W)
variable (P : V →ₗ[k] V) (Q : W →ₗ[k] W)
variable (hcomm : ∀ f : ρ.IntertwiningMap τ,
  f.toLinearMap.comp P = Q.comp f.toLinearMap)

/-- Restrict an intertwiner to the actual ranges of a commuting operator pair. -/
def rangeRestriction : (ρ.IntertwiningMap τ) →ₗ[k]
    (LinearMap.range P →ₗ[k] LinearMap.range Q) where
  toFun f :=
    { toFun v := ⟨f v.val, by
        obtain ⟨x, hx⟩ := v.property
        refine ⟨f x, ?_⟩
        have h := LinearMap.congr_fun (hcomm f) x
        change f (P x) = Q (f x) at h
        rw [hx] at h
        exact h.symm⟩
      map_add' v w := Subtype.ext (map_add f v.val w.val)
      map_smul' c v := Subtype.ext (map_smul f c v.val) }
  map_add' f g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rfl

@[simp] theorem rangeRestriction_apply (f : ρ.IntertwiningMap τ)
    (v : LinearMap.range P) :
    (rangeRestriction ρ τ P Q hcomm f v).val = f v.val := rfl

/-- A surjective intertwiner maps the first operator range onto the second. -/
theorem rangeRestriction_surjective (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) :
    Function.Surjective (rangeRestriction ρ τ P Q hcomm f) := by
  intro w
  obtain ⟨y, hy⟩ := w.property
  obtain ⟨v, hv⟩ := hf y
  refine ⟨⟨P v, ⟨v, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change f (P v) = w.val
  have h := LinearMap.congr_fun (hcomm f) v
  change f (P v) = Q (f v) at h
  rw [hv, hy] at h
  exact h

variable [τ.IsIrreducible]

/-- A nonzero target operator makes range restriction injective on intertwiners. -/
theorem rangeRestriction_injective (hQ : Q ≠ 0) :
    Function.Injective (rangeRestriction ρ τ P Q hcomm) := by
  apply (LinearMap.ker_eq_bot (f := rangeRestriction ρ τ P Q hcomm)).mp
  apply bot_unique
  intro f hf
  change f = 0
  by_contra hnonzero
  have hsurj : Function.Surjective f :=
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hnonzero
  apply hQ
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  have hz : rangeRestriction ρ τ P Q hcomm f = 0 := hf
  have hp := congrArg
    (fun l : LinearMap.range P →ₗ[k] LinearMap.range Q =>
      (l ⟨P v, ⟨v, rfl⟩⟩).val) hz
  change f (P v) = 0 at hp
  have h := LinearMap.congr_fun (hcomm f) v
  change f (P v) = Q (f v) at h
  exact h.symm.trans hp

variable [FiniteDimensional k V] [FiniteDimensional k W]

include hcomm

/-- The operator ranges bound the entire intertwiner space. -/
theorem finrank_le_product (hQ : Q ≠ 0) :
    Module.finrank k (ρ.IntertwiningMap τ) ≤
      Module.finrank k (LinearMap.range P) * Module.finrank k (LinearMap.range Q) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := rangeRestriction ρ τ P Q hcomm)
    (rangeRestriction_injective ρ τ P Q hcomm hQ)
  simpa only [Module.finrank_linearMap] using h

/-- Two rank-one ranges give a multiplicity-one bound. -/
theorem finrank_le_one (hQ : Q ≠ 0)
    (hPdim : Module.finrank k (LinearMap.range P) ≤ 1)
    (hQdim : Module.finrank k (LinearMap.range Q) ≤ 1) :
    Module.finrank k (ρ.IntertwiningMap τ) ≤ 1 := by
  have h := finrank_le_product ρ τ P Q hcomm hQ
  exact h.trans (by simpa using Nat.mul_le_mul hPdim hQdim)

/-- Only source multiplicity one is needed: any nonzero intertwiner forces
the target operator range to have no larger dimension. -/
theorem finrank_le_one_of_source_rank (hQ : Q ≠ 0)
    (hPdim : Module.finrank k (LinearMap.range P) ≤ 1) :
    Module.finrank k (ρ.IntertwiningMap τ) ≤ 1 := by
  classical
  by_cases hzero : ∀ f : ρ.IntertwiningMap τ, f = 0
  · let : Subsingleton (ρ.IntertwiningMap τ) :=
      ⟨fun f g => (hzero f).trans (hzero g).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le 1
  · obtain ⟨f, hf⟩ := not_forall.mp hzero
    have hsurj : Function.Surjective f :=
      (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (f := rangeRestriction ρ τ P Q hcomm f)
      (rangeRestriction_surjective ρ τ P Q hcomm f hsurj)
    exact finrank_le_one ρ τ P Q hcomm hQ hPdim (hdim.trans hPdim)

end Kourovka2135.MultiplicityOneIntertwining

namespace Kourovka2135.MultiplicityOneIntertwining

open scoped MonoidAlgebra

variable {k G V W : Type*} [Field k] [Monoid G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (τ : Representation k G W)

/-- The same group-algebra element gives a natural operator on every module. -/
theorem intertwining_asAlgebraHom (a : k[G]) (f : ρ.IntertwiningMap τ) :
    f.toLinearMap.comp (ρ.asAlgebraHom a) = (τ.asAlgebraHom a).comp f.toLinearMap := by
  apply LinearMap.ext
  intro v
  have h := (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ f).map_smul
    a (ρ.asModuleEquiv.symm v)
  change f (ρ.asAlgebraHom a v) = τ.asAlgebraHom a (f v) at h
  exact h

/-- A genuine rank-one group-algebra operator on the source detects at most
one copy of an irreducible target on which the same element acts nontrivially. -/
theorem finrank_le_one_of_groupAlgebra
    [τ.IsIrreducible] [FiniteDimensional k V] [FiniteDimensional k W]
    (a : k[G]) (hQ : τ.asAlgebraHom a ≠ 0)
    (hPdim : Module.finrank k (LinearMap.range (ρ.asAlgebraHom a)) ≤ 1) :
    Module.finrank k (ρ.IntertwiningMap τ) ≤ 1 :=
  finrank_le_one_of_source_rank ρ τ (ρ.asAlgebraHom a) (τ.asAlgebraHom a)
    (intertwining_asAlgebraHom ρ τ a) hQ hPdim

end Kourovka2135.MultiplicityOneIntertwining

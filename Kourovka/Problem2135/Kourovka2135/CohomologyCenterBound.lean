import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! The injective connecting map and dimension inequality used after
dualizing a minimal-kernel module extension. All exactness and invariant
space hypotheses are explicit; no family cohomology value is assumed. -/

set_option autoImplicit false
universe u
namespace Kourovka2135.GroupCohomology
open CategoryTheory CategoryTheory.Limits
variable {k G : Type u} [Field k] [Group G]

instance finite_h1 (A : Rep k G) [Finite G] [Finite A] :
    Finite (groupCohomology A 1) :=
  Finite.of_surjective (groupCohomology.H1π A)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

theorem h0_isZero_of_invariants_eq_bot (A : Rep k G)
    (hA : A.ρ.invariants = ⊥) : IsZero (groupCohomology A 0) := by
  have hs : Subsingleton A.ρ.invariants := by
    rw [hA]
    infer_instance
  let := hs
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of k A.ρ.invariants)).of_iso
    (groupCohomology.H0Iso A)

theorem connecting_injective_of_no_invariants
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hB : X.X₂.ρ.invariants = ⊥) :
    Function.Injective (groupCohomology.δ hX 0 1 rfl).hom := by
  have hm : Mono (groupCohomology.δ hX 0 1 rfl) :=
    groupCohomology.mono_δ_of_isZero hX 0 (h0_isZero_of_invariants_eq_bot X.X₂ hB)
  exact (ModuleCat.mono_iff_injective _).mp hm

theorem trivial_quotient_finrank_le_h1
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hB : X.X₂.ρ.invariants = ⊥) [X.X₃.ρ.IsTrivial]
    [FiniteDimensional k (groupCohomology X.X₁ 1)] :
    Module.finrank k X.X₃ ≤ Module.finrank k (groupCohomology X.X₁ 1) := by
  let f := (groupCohomology.H0IsoOfIsTrivial X.X₃).inv ≫
    groupCohomology.δ hX 0 1 rfl
  have hf : Function.Injective f.hom :=
    (connecting_injective_of_no_invariants hX hB).comp
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact LinearMap.finrank_le_finrank_of_injective hf

end Kourovka2135.GroupCohomology

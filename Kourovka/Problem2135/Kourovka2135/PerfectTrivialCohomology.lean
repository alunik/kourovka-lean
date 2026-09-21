import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The trivial simple module contributes zero first cohomology for a
perfect group, over any field. This uses the actual H1-to-homomorphisms
isomorphism, without a characteristic or group-order hypothesis. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PerfectTrivialCohomology

variable {K G V : Type u} [Field K] [Group G]
variable [AddCommGroup V] [Module K V]

/-- The scalar trivial representation is an actual irreducible representation. -/
theorem trivial_isIrreducible : (Representation.trivial K G K).IsIrreducible := by
  let ρ := Representation.trivial K G K
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  apply is_simple_module_of_finrank_eq_one (K := K)
  exact ρ.asModuleEquiv.finrank_eq.trans (Module.finrank_self K)

variable [Group.IsPerfect G]

/-- Every homomorphism from a perfect group to an additive commutative group vanishes. -/
theorem additiveHom_eq_zero (f : Additive G →+ V) : f = 0 := by
  apply AddMonoidHom.ext
  intro g
  have h := Abelianization.commutator_subset_ker f.toMultiplicativeRight
    (Group.IsPerfect.mem_commutator (g := g.toMul))
  exact congrArg Multiplicative.toAdd h

instance additiveHom_subsingleton : Subsingleton (Additive G →+ V) :=
  ⟨fun f h => (additiveHom_eq_zero f).trans (additiveHom_eq_zero h).symm⟩

/-- Actual first cohomology vanishes, rather than merely having numerical rank zero. -/
theorem subsingleton_H1 :
    Subsingleton (groupCohomology (Rep.of (Representation.trivial K G V)) 1) :=
  (groupCohomology.H1IsoOfIsTrivial (Rep.trivial K G V)).toLinearEquiv.injective.subsingleton

theorem finrank_H1_eq_zero :
    Module.finrank K (groupCohomology (Rep.of (Representation.trivial K G V)) 1) = 0 := by
  let : Subsingleton (groupCohomology (Rep.of (Representation.trivial K G V)) 1) :=
    subsingleton_H1
  exact Module.finrank_zero_of_subsingleton

end Kourovka2135.PerfectTrivialCohomology

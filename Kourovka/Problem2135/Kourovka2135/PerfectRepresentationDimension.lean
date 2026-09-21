import Kourovka2135.OneDimensionalCharacter
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-! A one-dimensional representation of a perfect group is trivial over any
field. The actual determinant homomorphism kills the commutator subgroup;
every endomorphism in dimension one is scalar, and its determinant is that
scalar. No irreducibility, semisimplicity, algebraic closure or finiteness
of the group is required. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PerfectRepresentationDimension

variable {E G V : Type*} [Field E] [Group G] [Group.IsPerfect G]
variable [AddCommGroup V] [Module E V]
variable (ρ : Representation E G V)

/-- In dimension one, perfectness forces every actual coefficient operator to be the identity. -/
theorem apply_eq_one_of_finrank_eq_one (hdim : Module.finrank E V = 1) (g : G) :
    ρ g = 1 := by
  let χ : G →* Eˣ := OneDimensionalCharacter.characterHom ρ
  have hχ : χ g = 1 :=
    Abelianization.commutator_subset_ker χ (Group.IsPerfect.mem_commutator (g := g))
  have hdet : LinearMap.det (ρ g) = 1 := by
    exact congrArg (fun u : Eˣ => (u : E)) hχ
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ g)
  change ρ g = c • (1 : Module.End E V) at hc
  have hc1 : c = 1 := by
    simpa only [hc, LinearMap.det_smul, hdim, pow_one, map_one, mul_one] using hdet
  simpa only [hc1, one_smul] using hc

/-- The actual representation homomorphism is trivial, not just its ordinary character. -/
theorem eq_one_of_finrank_eq_one (hdim : Module.finrank E V = 1) : ρ = 1 := by
  apply MonoidHom.ext
  intro g
  exact apply_eq_one_of_finrank_eq_one ρ hdim g

/-- Any witnessed nonidentity action excludes dimension one over the actual coefficient field. -/
theorem finrank_ne_one_of_nontrivial_action (h : ∃ g : G, ρ g ≠ 1) :
    Module.finrank E V ≠ 1 := by
  intro hdim
  obtain ⟨g, hg⟩ := h
  exact hg (apply_eq_one_of_finrank_eq_one ρ hdim g)

/-- A nontrivial representation likewise cannot have scalar dimension one. -/
theorem finrank_ne_one_of_ne_one (h : ρ ≠ 1) : Module.finrank E V ≠ 1 :=
  fun hdim => h (eq_one_of_finrank_eq_one ρ hdim)

end Kourovka2135.PerfectRepresentationDimension

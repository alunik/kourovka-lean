import Kourovka2135.PerfectTrivialCohomology
import Mathlib.RepresentationTheory.Subrepresentation

/-! A simple coefficient with a global fixed vector has trivial action.
Consequently a nonzero actual H1 class over a perfect group forces the global
fixed space to vanish. These are proved implications, not extra module
classification hypotheses. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.PerfectIrreducibleCohomology

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

theorem invariants_eq_bot_or_trivial : ρ.invariants = ⊥ ∨ ∀ g, ρ g = 1 := by
  let S : Subrepresentation ρ :=
    { toSubmodule := ρ.invariants
      apply_mem_toSubmodule := fun g v hv => by
        change ρ g v ∈ ρ.invariants
        rw [hv g]
        exact hv }
  rcases eq_bot_or_eq_top S with hS | hS
  · exact Or.inl (congrArg Subrepresentation.toSubmodule hS)
  · right
    intro g
    apply LinearMap.ext
    intro v
    have hv : v ∈ S := by rw [hS]; trivial
    exact hv g

omit [ρ.IsIrreducible] in
theorem subsingleton_H1_of_trivial [Group.IsPerfect G] (htriv : ∀ g, ρ g = 1) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have he : ρ = Representation.trivial k G V := by
    apply MonoidHom.ext
    intro g
    exact htriv g
  rw [he]
  exact PerfectTrivialCohomology.subsingleton_H1

theorem invariants_eq_bot_of_nontrivial_H1 [Group.IsPerfect G]
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] : ρ.invariants = ⊥ := by
  rcases invariants_eq_bot_or_trivial ρ with h | h
  · exact h
  · let : Subsingleton (groupCohomology (Rep.of ρ) 1) := subsingleton_H1_of_trivial ρ h
    obtain ⟨z, hz⟩ := exists_ne (0 : groupCohomology (Rep.of ρ) 1)
    exact False.elim (hz (Subsingleton.elim z 0))

end Kourovka2135.PerfectIrreducibleCohomology

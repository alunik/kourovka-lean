import Kourovka2135.PSL27BinaryHeartDecomposition
import Kourovka2135.OddPSLTwoCohomologySupport

/-! Actual first-cohomology support for binary PSL2(7) modules.

The genuine Borel fixed-space and H1 vanishings identify ordinary H1 with
maps out of the actual projective permutation heart. Its proved two simple
three-dimensional summands force every nontrivial simple coefficient with
nonzero H1 to be one of these actual summands. In particular an even
coefficient dimension forces H1 to vanish. No module classification or
algebraic closure hypothesis is used.
-/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PSL27CohomologySupport
open PSL27BinaryHeartCoordinates PSL27BinaryHeartDecomposition
abbrev k := ZMod 2

variable {V : Type} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

/-- A simple representation with nontrivial action has no global fixed vectors. -/
theorem invariants_eq_bot_of_nontrivial_action (hact : ¬ ∀ g : G, ρ g = 1) :
    ρ.invariants = ⊥ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := ρ.invariants
      apply_mem_toSubmodule := fun g v hv => by
        change ρ g v ∈ ρ.invariants
        rw [hv g]
        exact hv }
  rcases eq_bot_or_eq_top S with hS | hS
  · exact congrArg Subrepresentation.toSubmodule hS
  · apply False.elim
    apply hact
    intro g
    apply LinearMap.ext
    intro v
    have hv : v ∈ S := by rw [hS]; trivial
    exact hv g

/-- Restricting a nonzero heart map to one actual simple summand is nonzero. -/
theorem exists_component_equiv_of_heart_map
    (f : heartRepresentation.IntertwiningMap ρ) (hf : f ≠ 0) :
    ∃ b : Bool, Nonempty (ρ.Equiv (component b)) := by
  let d := f.comp heartDecomposition.symm.toIntertwiningMap
  have hd : d ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := heartDecomposition.symm.surjective v
    exact congrArg (fun t : ((component false).prod (component true)).IntertwiningMap ρ => t w) h
  let d₀ := d.comp (Representation.IntertwiningMap.inl k (component false) (component true))
  let d₁ := d.comp (Representation.IntertwiningMap.inr k (component false) (component true))
  by_cases h₀ : d₀ = 0
  · have h₁ : d₁ ≠ 0 := by
      intro h₁
      apply hd
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hz₀ := congrArg (fun t : (component false).IntertwiningMap ρ => t v.1) h₀
      have hz₁ := congrArg (fun t : (component true).IntertwiningMap ρ => t v.2) h₁
      change d (v.1, 0) = 0 at hz₀
      change d (0, v.2) = 0 at hz₁
      change d v = 0
      have hv : v = (v.1, 0) + (0, v.2) := by ext <;> simp
      rw [hv, map_add, hz₀, hz₁, add_zero]
    let : (component true).IsIrreducible := isIrreducible true
    exact ⟨true, ⟨(d₁.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero d₁).resolve_right h₁)).symm⟩⟩
  · let : (component false).IsIrreducible := isIrreducible false
    exact ⟨false, ⟨(d₀.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero d₀).resolve_right h₀)).symm⟩⟩

variable [FiniteDimensional k V]

/-- The actual ordinary H1/heart-Hom equivalence over the prime coefficient field. -/
def cohomologyHeartEquiv (hglobal : ρ.invariants = ⊥) :
    groupCohomology (Rep.of ρ) 1 ≃ₗ[k] heartRepresentation.IntertwiningMap ρ :=
  OddPSLTwoCohomologySupport.cohomologyHeartEquiv F k odd_card ρ hglobal

/-- Nonzero H1 produces an actual equivalence to one of the two constructed summands. -/
theorem exists_component_equiv_of_H1_nontrivial (hglobal : ρ.invariants = ⊥)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] :
    ∃ b : Bool, Nonempty (ρ.Equiv (component b)) := by
  obtain ⟨f, hf⟩ := OddPSLTwoCohomologySupport.exists_nonzero_heart_intertwiner
    F k odd_card ρ hglobal
  exact exists_component_equiv_of_heart_map ρ f hf

/-- The nonzero-cohomology support has actual coefficient dimension three. -/
theorem finrank_eq_three_of_H1_nontrivial (hglobal : ρ.invariants = ⊥)
    [Nontrivial (groupCohomology (Rep.of ρ) 1)] : Module.finrank k V = 3 := by
  obtain ⟨b, ⟨e⟩⟩ := exists_component_equiv_of_H1_nontrivial ρ hglobal
  rw [e.toLinearEquiv.finrank_eq]
  simp [V3]

/-- An even-dimensional nontrivial simple coefficient has zero actual H1. -/
theorem subsingleton_H1_of_even_finrank (hglobal : ρ.invariants = ⊥)
    (heven : Even (Module.finrank k V)) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  apply not_nontrivial_iff_subsingleton.mp
  intro hn
  let := hn
  have hdim := finrank_eq_three_of_H1_nontrivial ρ hglobal
  rw [hdim] at heven
  exact (by decide : ¬ Even 3) heven

/-- Equivalent endpoint stated with genuine nontriviality of the action. -/
theorem subsingleton_H1_of_even_finrank_of_nontrivial_action
    (hact : ¬ ∀ g : G, ρ g = 1) (heven : Even (Module.finrank k V)) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) :=
  subsingleton_H1_of_even_finrank ρ (invariants_eq_bot_of_nontrivial_action ρ hact) heven

theorem finrank_H1_eq_zero_of_even_finrank (hglobal : ρ.invariants = ⊥)
    (heven : Even (Module.finrank k V)) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) = 0 := by
  let := subsingleton_H1_of_even_finrank ρ hglobal heven
  exact Module.finrank_zero_of_subsingleton

end Kourovka2135.PSL27CohomologySupport

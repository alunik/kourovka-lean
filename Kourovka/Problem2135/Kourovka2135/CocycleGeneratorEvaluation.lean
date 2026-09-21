import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! One-cocycles are determined by their generator values. Verified positive
word relations give actual linear constraints on these values. These are
necessary constraints, so no finite-presentation assumption is required.
All formulas use the left-action convention z(gh)=rho(g)z(h)+z(g). -/

set_option autoImplicit false
noncomputable section
universe u v w x

namespace Kourovka2135.CocycleGeneratorEvaluation

open groupCohomology

variable {k G : Type u} {V : Type v} {I : Type w} {J : Type x} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) (gens : I → G)

/-- The actual linear evaluation map on a chosen family of generators. -/
def evaluation : cocycles₁ (Rep.of ρ) →ₗ[k] (I → V) where
  toFun z i := z (gens i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The zero set of an actual cocycle is a subgroup. -/
def zeroSubgroup (z : cocycles₁ (Rep.of ρ)) : Subgroup G where
  carrier := {g | z g = 0}
  one_mem' := cocycles₁_map_one z
  mul_mem' := by
    intro a b ha hb
    change z (a * b) = 0
    rw [(mem_cocycles₁_iff z).mp z.property, ha, hb, map_zero, add_zero]
  inv_mem' := by
    intro g hg
    change z g⁻¹ = 0
    have h := cocycles₁_map_inv z g⁻¹
    rw [inv_inv, show z g = 0 from hg, map_zero] at h
    exact neg_eq_zero.mp h.symm

/-- Vanishing on actual generators implies vanishing on the whole group. -/
theorem eq_zero_of_evaluation_eq_zero
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (z : cocycles₁ (Rep.of ρ)) (hz : evaluation ρ gens z = 0) : z = 0 := by
  have hle : Subgroup.closure (Set.range gens) ≤ zeroSubgroup ρ z := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact congrFun hz i
  rw [hgen] at hle
  apply cocycles₁_ext
  intro g
  exact hle (show g ∈ (⊤ : Subgroup G) from trivial)

theorem evaluation_injective (hgen : Subgroup.closure (Set.range gens) = ⊤) :
    Function.Injective (evaluation ρ gens) := by
  intro z w h
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluation_eq_zero ρ gens hgen (z - w)
  rw [map_sub, h, sub_self]

/-- Positive words suffice for the torsion relations in the finite certificates. -/
def wordValue : List I → G
  | [] => 1
  | i :: word => gens i * wordValue word

/-- The actual cocycle-value operator attached to a positive word. -/
def wordDerivative : List I → (I → V) →ₗ[k] V
  | [] => 0
  | i :: word => (ρ (gens i)).comp (wordDerivative word) + LinearMap.proj i

/-- Evaluating the derivative on generator values recovers the actual cocycle. -/
theorem wordDerivative_evaluation (word : List I) (z : cocycles₁ (Rep.of ρ)) :
    wordDerivative ρ gens word (evaluation ρ gens z) = z (wordValue gens word) := by
  induction word with
  | nil => exact (cocycles₁_map_one z).symm
  | cons i word ih =>
      change ρ (gens i) (wordDerivative ρ gens word (evaluation ρ gens z)) + z (gens i) =
        z (gens i * wordValue gens word)
      rw [ih]
      exact ((mem_cocycles₁_iff z).mp z.property _ _).symm

/-- Stack any finite or infinite family of necessary word constraints. -/
def constraints (words : J → List I) : (I → V) →ₗ[k] (J → V) :=
  LinearMap.pi (fun j => wordDerivative ρ gens (words j))

theorem constraints_evaluation_eq_zero (words : J → List I)
    (hwords : ∀ j, wordValue gens (words j) = 1) (z : cocycles₁ (Rep.of ρ)) :
    constraints ρ gens words (evaluation ρ gens z) = 0 := by
  funext j
  change wordDerivative ρ gens (words j) (evaluation ρ gens z) = 0
  rw [wordDerivative_evaluation, hwords j, cocycles₁_map_one]

/-- The actual injection into the certified constraint kernel. -/
def evaluationKernel (words : J → List I)
    (hwords : ∀ j, wordValue gens (words j) = 1) :
    cocycles₁ (Rep.of ρ) →ₗ[k] LinearMap.ker (constraints ρ gens words) :=
  (evaluation ρ gens).codRestrict _ (constraints_evaluation_eq_zero ρ gens words hwords)

theorem evaluationKernel_injective (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (words : J → List I) (hwords : ∀ j, wordValue gens (words j) = 1) :
    Function.Injective (evaluationKernel ρ gens words hwords) := by
  intro z w h
  apply evaluation_injective ρ gens hgen
  exact congrArg Subtype.val h

/-- Rank certificates for the small constraint matrix bound all actual one-cocycles. -/
theorem finrank_cocycles_le_kernel [Fintype I] [FiniteDimensional k V]
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (words : J → List I) (hwords : ∀ j, wordValue gens (words j) = 1) :
    Module.finrank k (cocycles₁ (Rep.of ρ)) ≤
      Module.finrank k (LinearMap.ker (constraints ρ gens words)) :=
  LinearMap.finrank_le_finrank_of_injective
    (evaluationKernel_injective ρ gens hgen words hwords)

end Kourovka2135.CocycleGeneratorEvaluation

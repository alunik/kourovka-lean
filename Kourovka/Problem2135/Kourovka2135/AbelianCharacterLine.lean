import Kourovka2135.RepresentationIrreducibleSubspace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RepresentationTheory.Invariants

/-! An actual character line in a finite-dimensional representation of an
abelian group over an algebraically closed field. An irreducible subspace
has dimension one, and a chosen linear coordinate constructs the character.
Neither finiteness of the group nor Maschke's theorem is needed. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.AbelianCharacterLine

variable {k U V W : Type u} [Field k] [Group U]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

theorem action_basis (τ : Representation k U W) (e : k ≃ₗ[k] W) (g : U) :
    τ g (e 1) = e.symm (τ g (e 1)) • e 1 := by
  rw [← map_smul, smul_eq_mul, mul_one, e.apply_symm_apply]

/-- Evaluate the conjugated one-dimensional action at its basis vector. -/
def scalarHom (τ : Representation k U W) (e : k ≃ₗ[k] W) : U →* k where
  toFun g := e.symm (τ g (e 1))
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, Module.End.mul_apply, action_basis τ e h, map_smul, map_smul]
    simp only [map_smul, e.symm_apply_apply, smul_eq_mul, mul_one]
    exact mul_comm _ _

variable (ρ : Representation k U V) [IsAlgClosed k] [FiniteDimensional k V]
variable [Nontrivial V] [IsMulCommutative U]

/-- The coefficient vector and character are constructed in the actual module. -/
theorem exists_character_line :
    ∃ (χ : U →* kˣ) (v : V), v ≠ 0 ∧ ∀ g : U, ρ g v = (χ g : k) • v := by
  obtain ⟨S, _, hS⟩ := RepresentationIrreducibleSubspace.exists_irreducible_subrepresentation ρ
  let : S.toRepresentation.IsIrreducible := hS
  have hd := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative S.toRepresentation
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hd
  let χ : U →* kˣ := (scalarHom S.toRepresentation e).toHomUnits
  refine ⟨χ, (e 1 : V), ?_, ?_⟩
  · intro hv
    have he : e (1 : k) = 0 := Subtype.ext hv
    have h1 : (1 : k) = 0 := e.injective (he.trans (e.map_zero).symm)
    exact one_ne_zero h1
  · intro g
    exact congrArg Subtype.val (action_basis S.toRepresentation e g)

/-- If no vector is globally fixed, a character line has nontrivial character. -/
theorem exists_nontrivial_character_line (hfixed : ρ.invariants = ⊥) :
    ∃ (χ : U →* kˣ) (v : V), v ≠ 0 ∧
      (∀ g : U, ρ g v = (χ g : k) • v) ∧ ∃ g : U, χ g ≠ 1 := by
  classical
  obtain ⟨χ, v, hv, he⟩ := exists_character_line ρ
  refine ⟨χ, v, hv, he, ?_⟩
  by_contra hn
  push Not at hn
  have hi : v ∈ ρ.invariants := by
    intro g
    simpa only [hn g, Units.val_one, one_smul] using he g
  rw [hfixed] at hi
  exact hv hi

end Kourovka2135.AbelianCharacterLine

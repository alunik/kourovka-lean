import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual invariant complements from Maschke's theorem. The complement is
constructed in the actual group-algebra module and pulled back to an actual
subrepresentation. Addition identifies the product of the two actual invariant
subspaces with the original representation, giving ordinary character and
finite-dimensional rank additivity. No complement is assumed in the existence
endpoint, and no character-completeness theorem is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationInvariantComplement

open scoped MonoidAlgebra

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {ρ : Representation k G V}

/-- Complementarity in the invariant-subspace lattice is actual scalar-space complementarity. -/
theorem isCompl_toSubmodule (W U : Subrepresentation ρ) (h : IsCompl W U) :
    IsCompl W.toSubmodule U.toSubmodule :=
  IsCompl.of_eq
    (congrArg (fun X : Subrepresentation ρ => X.toSubmodule) h.inf_eq_bot)
    (congrArg (fun X : Subrepresentation ρ => X.toSubmodule) h.sup_eq_top)

variable (ρ)

/-- Maschke supplies an actual invariant complement; it is not an endpoint assumption. -/
theorem exists_isCompl [Finite G] [NeZero (Nat.card G : k)] (W : Subrepresentation ρ) :
    ∃ U : Subrepresentation ρ, IsCompl W.toSubmodule U.toSubmodule := by
  obtain ⟨Q, hQ⟩ := MonoidAlgebra.Submodule.exists_isCompl W.asSubmodule
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h : IsCompl W (e.symm Q) := e.symm.isCompl hQ
  exact ⟨e.symm Q, isCompl_toSubmodule W (e.symm Q) h⟩

/-- Addition of the actual complementary invariant subspaces intertwines the actual actions. -/
def prodEquiv (W U : Subrepresentation ρ) (h : IsCompl W.toSubmodule U.toSubmodule) :
    Representation.Equiv (Representation.prod W.toRepresentation U.toRepresentation) ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl W.toSubmodule U.toSubmodule h)
    (fun g => by
      apply LinearMap.ext
      intro x
      change ρ g (x.1 : V) + ρ g (x.2 : V) = ρ g ((x.1 : V) + (x.2 : V))
      exact (map_add (ρ g) (x.1 : V) (x.2 : V)).symm)

@[simp] theorem prodEquiv_apply (W U : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule U.toSubmodule) (x : W.toSubmodule × U.toSubmodule) :
    prodEquiv ρ W U h x = (x.1 : V) + (x.2 : V) := rfl

variable [FiniteDimensional k V]

/-- Ordinary characters add on the actual invariant decomposition. -/
theorem character_eq_add (W U : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule U.toSubmodule) (g : G) :
    ρ.character g = W.toRepresentation.character g + U.toRepresentation.character g := by
  have heq := Representation.char_iso (prodEquiv ρ W U h)
  calc
    ρ.character g = (Representation.prod W.toRepresentation U.toRepresentation).character g :=
      (congrFun heq g).symm
    _ = W.toRepresentation.character g + U.toRepresentation.character g :=
      LinearMap.trace_prodMap' (W.toRepresentation g) (U.toRepresentation g)

/-- The actual underlying scalar dimensions add. -/
theorem finrank_eq_add (W U : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule U.toSubmodule) :
    Module.finrank k V = Module.finrank k W.toSubmodule + Module.finrank k U.toSubmodule :=
  (Submodule.finrank_add_eq_of_isCompl h).symm

/-- Removing a nonzero actual invariant subspace strictly decreases the remaining dimension. -/
theorem finrank_right_lt (W U : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule U.toSubmodule) (hW : W ≠ ⊥) :
    Module.finrank k U.toSubmodule < Module.finrank k V := by
  have hpos : 0 < Module.finrank k W.toSubmodule := Nat.pos_of_ne_zero (fun hz =>
    hW (Subrepresentation.toSubmodule_injective (Submodule.finrank_eq_zero.mp hz)))
  rw [finrank_eq_add ρ W U h]
  exact Nat.lt_add_of_pos_left hpos

/-- The actual complement, ordinary-character identity, and dimension identity in one endpoint. -/
theorem exists_complement_character_finrank [Finite G] [NeZero (Nat.card G : k)]
    (W : Subrepresentation ρ) :
    ∃ U : Subrepresentation ρ, IsCompl W.toSubmodule U.toSubmodule ∧
      (∀ g : G, ρ.character g =
        W.toRepresentation.character g + U.toRepresentation.character g) ∧
      Module.finrank k V = Module.finrank k W.toSubmodule + Module.finrank k U.toSubmodule := by
  obtain ⟨U, h⟩ := exists_isCompl ρ W
  exact ⟨U, h, character_eq_add ρ W U h, finrank_eq_add ρ W U h⟩

end Kourovka2135.RepresentationInvariantComplement

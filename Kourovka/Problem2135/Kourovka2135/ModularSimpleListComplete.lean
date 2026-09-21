import Kourovka2135.BinaryCharacterOddProjection
import Mathlib.Data.Fintype.Option

/-! A list reaching the proved odd-class bound contains every absolutely
simple representation. This is a cardinality consequence of actual modular
character independence, rather than an assumed classification theorem. -/

set_option autoImplicit false
noncomputable section
universe u v w x y

namespace Kourovka2135.ModularSimpleListComplete

variable {k G : Type u} [Field k] [IsAlgClosed k] [CharP k 2] [Group G] [Finite G]
variable {I : Type w} {J : Type x} [Fintype I] [Fintype J]
variable {V : I → Type v} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable [∀ i, Module.Finite k (V i)]
variable (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
variable {W : Type v} [AddCommGroup W] [Module k W] [Module.Finite k W]
variable (σ : Representation k G W) [σ.IsIrreducible]

/-- Adjoin the proposed missing representation to the finite list. -/
abbrev augmentedSpace : Option I → Type v := fun i => i.elim W V

instance augmentedAddCommGroup (i : Option I) :
    AddCommGroup (augmentedSpace (V := V) (W := W) i) := by
  cases i with
  | none => exact inferInstanceAs (AddCommGroup W)
  | some i => exact inferInstanceAs (AddCommGroup (V i))

instance augmentedModule (i : Option I) :
    Module k (augmentedSpace (V := V) (W := W) i) := by
  cases i with
  | none => exact inferInstanceAs (Module k W)
  | some i => exact inferInstanceAs (Module k (V i))

instance augmentedFinite (i : Option I) :
    Module.Finite k (augmentedSpace (V := V) (W := W) i) := by
  cases i with
  | none => exact inferInstanceAs (Module.Finite k W)
  | some i => exact inferInstanceAs (Module.Finite k (V i))

def augmentedRepresentation :
    ∀ i : Option I, Representation k G (augmentedSpace (V := V) (W := W) i)
  | none => σ
  | some i => ρ i

instance augmentedIrreducible (i : Option I) :
    (augmentedRepresentation ρ σ i).IsIrreducible := by
  cases i with
  | none => exact inferInstanceAs σ.IsIrreducible
  | some i => exact inferInstanceAs (ρ i).IsIrreducible

/-- The actual odd-conjugacy bound certifies completeness once its size is attained. -/
theorem exists_equiv_of_card_eq
    (hneq : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))
    (hcard : Nat.card G ∣ 11232) (c : J → G)
    (hcover : ∀ g : G, Odd (orderOf g) → ∃ j : J, IsConj (c j) g)
    (hsize : Fintype.card I = Fintype.card J) :
    ∃ i : I, Nonempty ((ρ i).Equiv σ) := by
  classical
  by_contra hmissing
  have he : Pairwise fun i j =>
      ¬ Nonempty ((augmentedRepresentation ρ σ i).Equiv
        (augmentedRepresentation ρ σ j)) := by
    intro i j hij hE
    cases i with
    | none =>
        cases j with
        | none => exact hij rfl
        | some j =>
            obtain ⟨e⟩ := hE
            exact hmissing ⟨j, ⟨e.symm⟩⟩
    | some i =>
        cases j with
        | none => exact hmissing ⟨i, hE⟩
        | some j => exact hneq (fun h => hij (congrArg some h)) hE
  have hbound := BinaryCharacterOddProjection.card_le_of_odd_conjugacy_cover_of_card_dvd
    (augmentedRepresentation ρ σ) he hcard c hcover
  rw [Fintype.card_option, hsize] at hbound
  omega

end Kourovka2135.ModularSimpleListComplete

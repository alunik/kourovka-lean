import Kourovka2135.OddPSLTwoCohomologySupport
import Kourovka2135.AbelianCharacterLine

/-! An actual nonzero H1 class forces a nontrivial root character to occur.
The implication passes through a genuine surjection from the permutation
heart, so it does not assume root-fixed vanishing for every simple module. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoCohomologyWeight
open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart

variable (F k : Type u) [Field F] [Fintype F] [Field k] [CharP k 2]
variable (hodd : Odd (Fintype.card F))
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (Q F) V) [ρ.IsIrreducible] [FiniteDimensional k V]
variable (hglobal : ρ.invariants = ⊥)
variable [Nontrivial (groupCohomology (Rep.of ρ) 1)]

include hodd hglobal

theorem unipotent_invariants_eq_bot :
    Representation.invariants (ρ.comp (unipotent F).subtype) = ⊥ := by
  classical
  let : Fintype (unipotent F) := Fintype.ofFinite _
  obtain ⟨f, _, hf⟩ :=
    OddPSLTwoCohomologySupport.exists_nonzero_surjective_heart_intertwiner F k hodd ρ hglobal
  let fu : Representation.IntertwiningMap
      ((heartRepresentation F k hodd).comp (unipotent F).subtype)
      (ρ.comp (unipotent F).subtype) :=
    ⟨f.toLinearMap, fun g => f.isIntertwining' g⟩
  exact CoprimeInvariantLifting.invariants_eq_bot_of_surjective
    ((heartRepresentation F k hodd).comp (unipotent F).subtype)
    (ρ.comp (unipotent F).subtype) (card_unipotent_cast_ne_zero F k hodd)
    fu hf (heart_unipotent_invariants_eq_bot F k hodd)

theorem root_invariants_eq_bot :
    Representation.invariants (ρ.comp (unipotentHom F)) = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  have hu : v ∈ Representation.invariants (ρ.comp (unipotent F).subtype) := by
    rintro ⟨g, t, rfl⟩
    exact hv t
  rw [unipotent_invariants_eq_bot F k hodd ρ hglobal] at hu
  exact hu

/-- The character and eigenvector are extracted from the actual root action. -/
theorem exists_nontrivial_character [IsAlgClosed k] :
    ∃ (χ : Multiplicative F →* kˣ) (v : V), χ ≠ 1 ∧ v ≠ 0 ∧
      ∀ t : Multiplicative F, ρ (unipotentHom F t) v = (χ t : k) • v := by
  let : IsMulCommutative (Multiplicative F) := ⟨⟨fun a b => mul_comm a b⟩⟩
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k (Q F)) ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨χ, v, hv, he, t, ht⟩ :=
    AbelianCharacterLine.exists_nontrivial_character_line (ρ.comp (unipotentHom F))
      (root_invariants_eq_bot F k hodd ρ hglobal)
  refine ⟨χ, v, ?_, hv, he⟩
  intro hz
  rw [hz] at ht
  exact ht rfl

end Kourovka2135.OddPSLTwoCohomologyWeight

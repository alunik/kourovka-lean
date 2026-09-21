import Kourovka2135.OddPSLTwoBorel
import Kourovka2135.NormalCyclicCocycleVanishing
import Kourovka2135.PermutationHeartCohomologyBound

/-! A characteristic-two first-cohomology bound for actual odd PSL2.

The root subgroup and Borel are the genuine subgroups of the projective
matrix group. The projective permutation heart, averaging over the odd
root subgroup, and a single character projector supply the bound. No
irreducible-module classification or cohomology value is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoFirstCohomology

open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart OddPSLTwoBorel

variable (F k : Type u) [Field F] [Fintype F] [Field k] [CharP k 2]
variable (hodd : Odd (Fintype.card F))
variable {V : Type u} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (Q F) V) [ρ.IsIrreducible]

include hodd in
/-- Every nontrivial simple module has no fixed vector under the actual Borel. -/
theorem borel_invariants_eq_bot (hglobal : ρ.invariants = ⊥) :
    Representation.invariants (ρ.comp (borel F).subtype) = ⊥ := by
  classical
  let : Fintype (unipotent F) := Fintype.ofFinite _
  exact PermutationHeartCohomology.stabilizer_invariants_eq_bot
    ρ (card_points_cast_zero F k hodd) none
    (fun x => MulAction.exists_smul_eq (Q F) none x) hglobal
    (unipotent F) (unipotent_le_stabilizer F)
    (card_unipotent_cast_ne_zero F k hodd)
    (heart_unipotent_invariants_eq_bot F k hodd)

include hodd in
/-- The cyclic torus quotient need not have odd order: normal-root averaging
and vanishing of Borel fixed vectors already force actual H1 to vanish. -/
theorem subsingleton_borel_H1 [FiniteDimensional k V]
    (hglobal : ρ.invariants = ⊥) :
    Subsingleton (groupCohomology (Rep.of (ρ.comp (borel F).subtype)) 1) := by
  classical
  let : Fintype (unipotentInBorel F) := Fintype.ofFinite _
  have hcard : (Fintype.card (unipotentInBorel F) : k) ≠ 0 := by
    have he : Fintype.card (unipotentInBorel F) = Fintype.card F := by
      simpa only [Nat.card_eq_fintype_card] using card_unipotentInBorel F
    rw [he, card_field_cast F k hodd]
    exact one_ne_zero
  obtain ⟨r, hr⟩ := exists_torus_generator F
  exact NormalCyclicCocycleVanishing.subsingleton_H1
    (ρ.comp (borel F).subtype) (unipotentInBorel F) (torusHom F r)
    hcard hr (borel_invariants_eq_bot F k hodd ρ hglobal)

include hodd in
/-- Over an algebraically closed binary coefficient field, every nontrivial
finite-dimensional irreducible representation of actual odd PSL2 has H1
dimension at most one. -/
theorem finrank_H1_le_one [IsAlgClosed k] [FiniteDimensional k V]
    (hglobal : ρ.invariants = ⊥) :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤ 1 := by
  classical
  let : Fintype (unipotent F) := Fintype.ofFinite _
  let : IsMulCommutative (unipotent F) :=
    Subgroup.range_isMulCommutative (unipotentHom F)
  exact PermutationHeartCohomologyBound.finrank_H1_le_one
    ρ (card_points_cast_zero F k hodd) (unipotent F) none (some (0 : F))
    hglobal (card_unipotent_cast_ne_zero F k hodd)
    (unipotent_le_stabilizer F) (by simp) (affine_transitive F)
    (fun x => MulAction.exists_smul_eq (Q F) none x)
    (heart_unipotent_invariants_eq_bot F k hodd)
    (subsingleton_borel_H1 F k hodd ρ hglobal)

end Kourovka2135.OddPSLTwoFirstCohomology

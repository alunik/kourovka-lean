import Kourovka2135.FrattiniConjugation
import Kourovka2135.HallAdjustment
import Kourovka2135.PrimeToPValues
import Kourovka2135.LeafSection

/-!
# Generating the quotient action by centralizing single values

Focal generation supplies prime-to-p single values. Hall adjustment changes
each by a conjugation from P, which leaves its Frattini quotient action intact.
The set used here contains all eligible centralizing values, avoiding choices.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

def centralPrimeValues (s : OuterWord) (p : ℕ) (x : G) : Set G :=
  {b | b ∈ s.values G ∧ ¬ p ∣ orderOf b ∧ Commute b x}

theorem action_mem_closure_centralPrimeValues [Finite G]
    (p : ℕ) (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) {x : G}
    (hxp : ¬ p ∣ orderOf x) (s : OuterWord) (X : Set G)
    (hX : ∀ a ∈ X, a ∈ s.values G ∧ ¬ p ∣ orderOf a ∧ paperCommutator x a ∈ P)
    (hxgen : x ∈ Subgroup.closure X) :
    frattiniConj P x ∈ Subgroup.closure (frattiniConj P '' centralPrimeValues s p x) := by
  let N := Subgroup.closure (frattiniConj P '' centralPrimeValues s p x)
  have hle : Subgroup.closure X ≤ N.comap (frattiniConj P) := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    obtain ⟨hav, hap, hxa⟩ := hX a ha
    obtain ⟨u, hu, hcomm⟩ := Hall.exists_conj_commute_of_commutator_mem_pSubgroup
      hp hsolv P hP hxp hap hxa
    apply Subgroup.subset_closure
    refine ⟨u⁻¹ * a * u, ?_, frattiniConj_conjugate_eq p hp P hP hu a⟩
    refine ⟨s.conj_mem_values hav u, ?_, hcomm.symm⟩
    have heq : orderOf (u⁻¹ * a * u) = orderOf a := by
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj u⁻¹).orderOf_eq a
    rwa [heq]
  exact hle hxgen

theorem left_branch_action_generated_by_centralPrimeValues [Finite G]
    (p : ℕ) (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (α β r : OuterWord) (hα : α.verbalSubgroup G ≤ r.verbalSubgroup G)
    {x : G} (hx : x ∈ (OuterWord.bracket α β).values G)
    (hxp : ¬ p ∣ orderOf x)
    (hxr : ∀ a ∈ r.verbalSubgroup G, paperCommutator x a ∈ P) :
    frattiniConj P x ∈ Subgroup.closure (frattiniConj P '' centralPrimeValues α p x) := by
  apply action_mem_closure_centralPrimeValues p hp hsolv P hP hxp α
    {a | a ∈ α.values G ∧ ¬ p ∣ orderOf a}
  · intro a ha
    exact ⟨ha.1, ha.2, hxr a (hα (α.mem_verbalSubgroup_of_mem_values ha.1))⟩
  · exact α.mem_primeToPValueSubgroup p hp hsolv
      (OuterWord.verbalSubgroup_bracket_le_left α β
        ((OuterWord.bracket α β).mem_verbalSubgroup_of_mem_values hx)) hxp

theorem constituent_action_generated_by_centralPrimeValues [Finite G]
    (p : ℕ) (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (α β r : OuterWord) (hα : α.verbalSubgroup G ≤ r.verbalSubgroup G)
    {x : G} (hx : x ∈ (OuterWord.bracket α β).values G)
    (hxp : ¬ p ∣ orderOf x)
    (hxr : ∀ a ∈ r.verbalSubgroup G, paperCommutator x a ∈ P)
    (s : OuterWord) (hs : OuterWord.Constituent s β) :
    frattiniConj P x ∈ Subgroup.closure (frattiniConj P '' centralPrimeValues s p x) := by
  let W : Set OuterWord := s.leafInsertions r
  let X : Set G := {a | ∃ v ∈ W, a ∈ v.values G ∧ ¬ p ∣ orderOf a}
  have hle : (OuterWord.bracket α β).verbalSubgroup G ≤ s.leafSectionSubgroup r G := by
    rw [OuterWord.verbalSubgroup_bracket]
    apply (Subgroup.commutator_mono hα (OuterWord.verbalSubgroup_le_of_constituent hs)).trans
    rw [Subgroup.commutator_comm]
    exact s.commutator_verbalSubgroup_le_leafSection r
  have hxT : x ∈ ⨆ v ∈ W, v.verbalSubgroup G :=
    hle ((OuterWord.bracket α β).mem_verbalSubgroup_of_mem_values hx)
  have hxgen : x ∈ Subgroup.closure X :=
    OuterWord.mem_familyPrimeToPValueSubgroup W p hp hsolv hxT hxp
  apply action_mem_closure_centralPrimeValues p hp hsolv P hP hxp s X ?_ hxgen
  rintro a ⟨v, hv, hav, hap⟩
  have hh := OuterWord.leafInsertion_value_mem hv hav
  exact ⟨hh.1, hap, hxr a hh.2⟩

end Kourovka2135

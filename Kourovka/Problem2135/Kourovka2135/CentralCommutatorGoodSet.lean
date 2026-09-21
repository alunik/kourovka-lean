import Kourovka2135.GoodSetLifting
import Kourovka2135.CentralWordValues
import Kourovka2135.CentralDoubleCoverUniqueness

/-! Generating good sets in actual perfect central extensions.

The lift consists of commutators of pairs whose images generate the quotient
and belong to the original good set. Centrality makes those commutators
independent of the chosen lifts. Perfectness makes every lifted generating
pair generate the cover. No multiplier, kernel-cardinality, finiteness, or
surjectivity-of-the-commutator-map assertion is assumed. This construction
does not assert that the full inverse image is good or preserve element orders.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135.CentralCommutatorGoodSet

variable {E : Type u} {S : Type v} [Group E] [Group S]

/-- The actual commutator lift of a generating good set. -/
def commutatorLift (π : E →* S) (B : Set S) : Set E :=
  {t | ∃ a b : E, π a ∈ B ∧ π b ∈ B ∧
    Subgroup.closure ({π a, π b} : Set S) = ⊤ ∧
    paperCommutator a b = t ∧ π t ∈ B}

/-- Every original good-set element has an actual commutator lift. -/
theorem exists_mem_commutatorLift (π : E →* S) (hπ : Function.Surjective π)
    {B : Set S} (hB : IsGeneratingGoodSet B) {s : S} (hs : s ∈ B) :
    ∃ t ∈ commutatorLift π B, π t = s := by
  obtain ⟨x, hx, y, hy, hxy, hgen⟩ := hB s hs
  obtain ⟨a, ha⟩ := hπ x
  obtain ⟨b, hb⟩ := hπ y
  have hc : π (paperCommutator a b) = s := by
    simpa only [paperCommutator, map_mul, map_inv, ha, hb] using hxy
  refine ⟨paperCommutator a b, ?_, hc⟩
  refine ⟨a, b, ?_, ?_, ?_, rfl, ?_⟩
  · rwa [ha]
  · rwa [hb]
  · rw [ha, hb]
    exact hgen
  · rwa [hc]

/-- The lift maps exactly onto the original set. -/
theorem image_commutatorLift (π : E →* S) (hπ : Function.Surjective π)
    {B : Set S} (hB : IsGeneratingGoodSet B) : π '' commutatorLift π B = B := by
  apply Set.Subset.antisymm
  · rintro s ⟨t, ⟨_, _, _, _, _, _, ht⟩, rfl⟩
    exact ht
  · intro s hs
    exact exists_mem_commutatorLift π hπ hB hs

/-- Generation in the quotient lifts through a central kernel when the
cover is perfect. -/
theorem closure_pair_eq_top [Group.IsPerfect E] (π : E →* S)
    (hc : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set S) = ⊤) :
    Subgroup.closure ({a, b} : Set E) = ⊤ := by
  let H := Subgroup.closure ({a, b} : Set E)
  have hm : H.map π = ⊤ := by
    change (Subgroup.closure ({a, b} : Set E)).map π = ⊤
    rw [MonoidHom.map_closure, Set.image_pair, hgen]
  have hs : H ⊔ π.ker = ⊤ := by
    have he := congrArg (Subgroup.comap π) hm
    simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using he
  exact CentralDoubleCoverUniqueness.eq_top_of_sup_central H π.ker hs hc

/-- The actual commutator lift is a generating good set. -/
theorem isGeneratingGoodSet_commutatorLift [Group.IsPerfect E]
    (π : E →* S) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E)
    {B : Set S} (hB : IsGeneratingGoodSet B) :
    IsGeneratingGoodSet (commutatorLift π B) := by
  rintro t ⟨a, b, ha, hb, hgen, hab, _⟩
  obtain ⟨a', ha', hea⟩ := exists_mem_commutatorLift π hπ hB ha
  obtain ⟨b', hb', heb⟩ := exists_mem_commutatorLift π hπ hB hb
  refine ⟨a', ha', b', hb', ?_, ?_⟩
  · exact (paperCommutator_eq_of_central_kernel π hc hea heb).trans hab
  · apply closure_pair_eq_top π hc
    rw [hea, heb]
    exact hgen

/-- A perfect central cover has a genuine generating good set with exactly
the prescribed good-set image. -/
theorem exists_generating_good_set_over [Group.IsPerfect E]
    (π : E →* S) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E)
    {B : Set S} (hB : IsGeneratingGoodSet B) :
    ∃ C : Set E, IsGeneratingGoodSet C ∧ π '' C = B :=
  ⟨commutatorLift π B, isGeneratingGoodSet_commutatorLift π hπ hc hB,
    image_commutatorLift π hπ hB⟩

end Kourovka2135.CentralCommutatorGoodSet

import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.CompatibleFamilies

/-!
# Support-size strata for witness families

Compatible families are grouped by the number of distinct prescribed source
vertices.  On each stratum the permutation contribution is constant.
-/

namespace Kourovka213

variable {P Q : BoundedPartition n}

/-- A family of `k` witnesses which is realizable and uses exactly `r`
distinct source vertices. -/
noncomputable def compatibleWitnessFamiliesBySupport
    (P Q : BoundedPartition n) (k r : ℕ) :
    Finset (Finset (CollisionWitness P Q)) := by
  classical
  exact (witnessFamilies P Q k).filter fun S =>
    (holdingPermutationsOfFamily S).Nonempty ∧
      (witnessFamilySources S).card = r

@[simp]
theorem mem_compatibleWitnessFamiliesBySupport
    {S : Finset (CollisionWitness P Q)} :
    S ∈ compatibleWitnessFamiliesBySupport P Q k r ↔
      S.card = k ∧ (holdingPermutationsOfFamily S).Nonempty ∧
        (witnessFamilySources S).card = r := by
  classical
  simp [compatibleWitnessFamiliesBySupport, witnessFamilies]

/-- A `k`-witness family uses at most `2k` distinct source vertices. -/
theorem card_witnessFamilySources_le_two_mul_card
    (S : Finset (CollisionWitness P Q)) :
    (witnessFamilySources S).card ≤ 2 * S.card := by
  classical
  unfold witnessFamilySources
  calc
    (Finset.univ.image (witnessFamilySource S)).card ≤
        (Finset.univ : Finset (S × Bool)).card := Finset.card_image_le
    _ = 2 * S.card := by simp [mul_comm]

/-- All compatible families in one support stratum make the same factorial
contribution. -/
theorem sum_compatible_family_cards_by_support_eq
    (P Q : BoundedPartition n) (k r : ℕ) :
    (∑ S ∈ compatibleWitnessFamiliesBySupport P Q k r,
        (holdingPermutationsOfFamily S).card) =
      (compatibleWitnessFamiliesBySupport P Q k r).card *
        (n - r).factorial := by
  classical
  calc
    (∑ S ∈ compatibleWitnessFamiliesBySupport P Q k r,
        (holdingPermutationsOfFamily S).card) =
        ∑ _S ∈ compatibleWitnessFamiliesBySupport P Q k r,
          (n - r).factorial := by
      apply Finset.sum_congr rfl
      intro S hS
      have hm := mem_compatibleWitnessFamiliesBySupport.mp hS
      rw [card_holdingPermutationsOfFamily_of_nonempty S hm.2.1, hm.2.2]
    _ = (compatibleWitnessFamiliesBySupport P Q k r).card *
        (n - r).factorial := by simp

/-- A compatible family has a unique source-support stratum in the range
`0, ..., 2k`. -/
theorem exists_unique_support_of_compatible
    {S : Finset (CollisionWitness P Q)} (hcard : S.card = k)
    (hcompat : (holdingPermutationsOfFamily S).Nonempty) :
    ∃! r : ℕ, r ∈ Finset.range (2 * k + 1) ∧
      S ∈ compatibleWitnessFamiliesBySupport P Q k r := by
  let r := (witnessFamilySources S).card
  have hr : r ≤ 2 * k := by
    dsimp [r]
    simpa [hcard] using card_witnessFamilySources_le_two_mul_card S
  refine ⟨r, ⟨Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩
  · exact mem_compatibleWitnessFamiliesBySupport.mpr
      ⟨hcard, hcompat, rfl⟩
  · intro s hs
    exact (mem_compatibleWitnessFamiliesBySupport.mp hs.2).2.2.symm

private theorem card_holding_eq_support_sum
    (S : Finset (CollisionWitness P Q)) (hcard : S.card = k) :
    (holdingPermutationsOfFamily S).card =
      ∑ r ∈ Finset.range (2 * k + 1),
        if (holdingPermutationsOfFamily S).Nonempty ∧
            (witnessFamilySources S).card = r then
          (n - r).factorial
        else 0 := by
  classical
  by_cases hcompat : (holdingPermutationsOfFamily S).Nonempty
  · let r := (witnessFamilySources S).card
    have hr : r ∈ Finset.range (2 * k + 1) := by
      rw [Finset.mem_range]
      have hle := card_witnessFamilySources_le_two_mul_card S
      dsimp [r]
      omega
    rw [card_holdingPermutationsOfFamily_of_nonempty S hcompat]
    symm
    refine (Finset.sum_eq_single r ?_ ?_).trans ?_
    · intro s _hs hsr
      simp only [hcompat, true_and, ite_eq_right_iff]
      intro hrs
      exact (hsr hrs.symm).elim
    · exact fun hnot => (hnot hr).elim
    · simp [r, hcompat]
  · have hempty : (holdingPermutationsOfFamily S).card = 0 :=
      Finset.not_nonempty_iff_eq_empty.mp hcompat ▸ rfl
    rw [hempty]
    simp [hcompat]

/-- Exact support-size decomposition of every collision binomial moment.  It
includes all compatible overlaps; incompatible families contribute zero. -/
theorem collisionBinomialMomentNat_eq_sum_support_strata
    (P Q : BoundedPartition n) (k : ℕ) :
    collisionBinomialMomentNat P Q k =
      ∑ r ∈ Finset.range (2 * k + 1),
        (compatibleWitnessFamiliesBySupport P Q k r).card *
          (n - r).factorial := by
  classical
  rw [collisionBinomialMomentNat_eq_sum_family_cards]
  calc
    (∑ S ∈ witnessFamilies P Q k,
        (holdingPermutationsOfFamily S).card) =
        ∑ S ∈ witnessFamilies P Q k,
          ∑ r ∈ Finset.range (2 * k + 1),
            if (holdingPermutationsOfFamily S).Nonempty ∧
                (witnessFamilySources S).card = r then
              (n - r).factorial
            else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      exact card_holding_eq_support_sum S
        (by simpa [witnessFamilies] using hS)
    _ = ∑ r ∈ Finset.range (2 * k + 1),
          ∑ S ∈ witnessFamilies P Q k,
            if (holdingPermutationsOfFamily S).Nonempty ∧
                (witnessFamilySources S).card = r then
              (n - r).factorial
            else 0 := by
      exact Finset.sum_comm
    _ = ∑ r ∈ Finset.range (2 * k + 1),
        (compatibleWitnessFamiliesBySupport P Q k r).card *
          (n - r).factorial := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [← Finset.sum_filter]
      change (∑ _S ∈ compatibleWitnessFamiliesBySupport P Q k r,
          (n - r).factorial) = _
      simp

/-- The top support stratum is exactly the vertex-disjoint stratum. -/
theorem compatibleWitnessFamiliesBySupport_two_mul_eq_disjoint
    (P Q : BoundedPartition n) (k : ℕ) :
    compatibleWitnessFamiliesBySupport P Q k (2 * k) =
      disjointWitnessFamilies P Q k := by
  classical
  ext S
  constructor
  · intro hS
    have hm := mem_compatibleWitnessFamiliesBySupport.mp hS
    obtain ⟨sigma, hsigmaMem⟩ := hm.2.1
    have hsigma : WitnessFamilyHolds S sigma := by
      simpa [holdingPermutationsOfFamily] using hsigmaMem
    have hsourceCard :
        (Finset.univ.image (witnessFamilySource S)).card =
          (Finset.univ : Finset (S × Bool)).card := by
      calc
        (Finset.univ.image (witnessFamilySource S)).card = 2 * k := by
          simpa [witnessFamilySources] using hm.2.2
        _ = (Finset.univ : Finset (S × Bool)).card := by
          simp [hm.1, mul_comm]
    have hsourceInjOn : Set.InjOn (witnessFamilySource S)
        (Finset.univ : Finset (S × Bool)) :=
      Finset.card_image_iff.mp hsourceCard
    have hsource : Function.Injective (witnessFamilySource S) := by
      intro i j hij
      exact hsourceInjOn (Finset.mem_univ i) (Finset.mem_univ j) hij
    have horiented :=
      (witnessFamilyHolds_iff_forall_oriented S sigma).mp hsigma
    have htarget : Function.Injective (witnessFamilyTarget S) := by
      intro i j hij
      apply hsource
      apply sigma.injective
      calc
        sigma (witnessFamilySource S i) = witnessFamilyTarget S i := horiented i
        _ = witnessFamilyTarget S j := hij
        _ = sigma (witnessFamilySource S j) := (horiented j).symm
    exact mem_disjointWitnessFamilies.mpr ⟨hm.1, hsource, htarget⟩
  · intro hS
    have hm := mem_disjointWitnessFamilies.mp hS
    have hcompat : (holdingPermutationsOfFamily S).Nonempty := by
      rw [← Finset.card_pos]
      rw [card_holdingPermutationsOfFamily_of_vertexDisjoint S hm.2]
      exact Nat.factorial_pos _
    have hsourceCard : (witnessFamilySources S).card = 2 * k := by
      unfold witnessFamilySources
      rw [Finset.card_image_iff.mpr hm.2.1.injOn]
      simp [hm.1, mul_comm]
    exact mem_compatibleWitnessFamiliesBySupport.mpr
      ⟨hm.1, hcompat, hsourceCard⟩

/-- A nonempty witness family cannot have empty source support. -/
theorem compatibleWitnessFamiliesBySupport_zero_eq_empty
    (P Q : BoundedPartition n) (k : ℕ) (hk : 0 < k) :
    compatibleWitnessFamiliesBySupport P Q k 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hm := mem_compatibleWitnessFamiliesBySupport.mp hS
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := hSnonempty
  have hsourceNonempty : (witnessFamilySources S).Nonempty := by
    refine ⟨w.prescribedSource false, ?_⟩
    exact (mem_witnessFamilySources S _).mpr ⟨(⟨w, hw⟩, false), rfl⟩
  have hpos := Finset.card_pos.mpr hsourceNonempty
  omega

end Kourovka213

import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.PartialBijectionCount
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.SubsetExpansion

/-!
# Vertex-disjoint collision-witness families

A collision witness prescribes two values of a permutation.  A family is
vertex-disjoint when all prescribed sources, and separately all prescribed
targets, are distinct.  Such a `k`-family has exactly `(n-2k)!` realizing
permutations.
-/

namespace Kourovka213

namespace CollisionWitness

/-- Source selected by one of the two orientations of a witness. -/
def prescribedSource {P Q : BoundedPartition n} (w : CollisionWitness P Q) :
    Bool → Fin n
  | false => w.left.fst
  | true => w.left.snd

/-- Target prescribed for the selected source. -/
def prescribedTarget {P Q : BoundedPartition n} (w : CollisionWitness P Q) :
    Bool → Fin n
  | false => if w.flipped then w.right.snd else w.right.fst
  | true => if w.flipped then w.right.fst else w.right.snd

theorem holds_iff_forall_orientation {P Q : BoundedPartition n}
    (w : CollisionWitness P Q) (sigma : Sym n) :
    w.Holds sigma ↔
      ∀ b : Bool, sigma (w.prescribedSource b) = w.prescribedTarget b := by
  cases hflip : w.flipped <;>
    simp [Holds, prescribedSource, prescribedTarget, hflip, Bool.forall_bool]

end CollisionWitness

section Family

variable {P Q : BoundedPartition n}

/-- The indexed list of sources prescribed by a witness family. -/
def witnessFamilySource (S : Finset (CollisionWitness P Q)) : S × Bool → Fin n :=
  fun i => i.1.1.prescribedSource i.2

/-- The indexed list of targets prescribed by a witness family. -/
def witnessFamilyTarget (S : Finset (CollisionWitness P Q)) : S × Bool → Fin n :=
  fun i => i.1.1.prescribedTarget i.2

/-- No two oriented witnesses use the same source or the same target. -/
def WitnessFamilyVertexDisjoint (S : Finset (CollisionWitness P Q)) : Prop :=
  Function.Injective (witnessFamilySource S) ∧
    Function.Injective (witnessFamilyTarget S)

theorem witnessFamilyHolds_iff_forall_oriented
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n) :
    WitnessFamilyHolds S sigma ↔
      ∀ i : S × Bool,
        sigma (witnessFamilySource S i) = witnessFamilyTarget S i := by
  constructor
  · intro h i
    exact (CollisionWitness.holds_iff_forall_orientation i.1.1 sigma).mp
      (h i.1.1 i.1.2) i.2
  · intro h w hw
    rw [CollisionWitness.holds_iff_forall_orientation]
    intro b
    exact h (⟨w, hw⟩, b)

/-- A vertex-disjoint `k`-family prescribes `2k` distinct values, so the
remaining points may be bijected arbitrarily. -/
theorem card_holdingPermutationsOfFamily_of_vertexDisjoint
    (S : Finset (CollisionWitness P Q)) (hS : WitnessFamilyVertexDisjoint S) :
    (holdingPermutationsOfFamily S).card = (n - 2 * S.card).factorial := by
  classical
  let f := witnessFamilySource S
  let g := witnessFamilyTarget S
  have hcount := card_perm_extending_injective_pair f g hS.1 hS.2
  rw [holdingPermutationsOfFamily]
  have hfilter :
      (Finset.univ.filter (WitnessFamilyHolds S) : Finset (Sym n)) =
        Finset.univ.filter (fun sigma => ∀ i : S × Bool, sigma (f i) = g i) := by
    ext sigma
    simp [f, g, witnessFamilyHolds_iff_forall_oriented]
  rw [hfilter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hcount]
  simp [Fintype.card_prod, mul_comm]

/-- Vertex-disjoint `k`-element witness families. -/
noncomputable def disjointWitnessFamilies (P Q : BoundedPartition n) (k : ℕ) :
    Finset (Finset (CollisionWitness P Q)) := by
  classical
  exact (witnessFamilies P Q k).filter WitnessFamilyVertexDisjoint

@[simp]
theorem mem_disjointWitnessFamilies {P Q : BoundedPartition n} {k : ℕ}
    {S : Finset (CollisionWitness P Q)} :
    S ∈ disjointWitnessFamilies P Q k ↔
      S.card = k ∧ WitnessFamilyVertexDisjoint S := by
  classical
  simp [disjointWitnessFamilies]

/-- Exact contribution of vertex-disjoint families to the unnormalized
binomial moment. -/
theorem sum_disjoint_family_cards_eq (P Q : BoundedPartition n) (k : ℕ) :
    (∑ S ∈ disjointWitnessFamilies P Q k,
        (holdingPermutationsOfFamily S).card) =
      (disjointWitnessFamilies P Q k).card * (n - 2 * k).factorial := by
  classical
  calc
    (∑ S ∈ disjointWitnessFamilies P Q k,
        (holdingPermutationsOfFamily S).card) =
        ∑ _S ∈ disjointWitnessFamilies P Q k, (n - 2 * k).factorial := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [card_holdingPermutationsOfFamily_of_vertexDisjoint S
        (mem_disjointWitnessFamilies.mp hS).2,
        (mem_disjointWitnessFamilies.mp hS).1]
    _ = (disjointWitnessFamilies P Q k).card * (n - 2 * k).factorial := by
      simp

/-- Non-vertex-disjoint `k`-element witness families. -/
noncomputable def overlappingWitnessFamilies (P Q : BoundedPartition n) (k : ℕ) :
    Finset (Finset (CollisionWitness P Q)) := by
  classical
  exact (witnessFamilies P Q k).filter fun S => ¬WitnessFamilyVertexDisjoint S

/-- Total incidence contribution of the overlapping witness families. -/
noncomputable def overlappingFamilyContribution
    (P Q : BoundedPartition n) (k : ℕ) : ℕ :=
  ∑ S ∈ overlappingWitnessFamilies P Q k, (holdingPermutationsOfFamily S).card

/-- Exact main-term/error decomposition of every collision binomial moment. -/
theorem collisionBinomialMomentNat_eq_disjoint_add_overlap
    (P Q : BoundedPartition n) (k : ℕ) :
    collisionBinomialMomentNat P Q k =
      (disjointWitnessFamilies P Q k).card * (n - 2 * k).factorial +
        overlappingFamilyContribution P Q k := by
  classical
  rw [collisionBinomialMomentNat_eq_sum_family_cards,
    ← sum_disjoint_family_cards_eq]
  unfold overlappingFamilyContribution
  unfold disjointWitnessFamilies overlappingWitnessFamilies
  exact (Finset.sum_filter_add_sum_filter_not
    (s := witnessFamilies P Q k)
    (p := WitnessFamilyVertexDisjoint)
    (f := fun S => (holdingPermutationsOfFamily S).card)).symm

/-- A family cannot be realized by more than all `n!` permutations. -/
theorem card_holdingPermutationsOfFamily_le_factorial
    (S : Finset (CollisionWitness P Q)) :
    (holdingPermutationsOfFamily S).card ≤ n.factorial := by
  classical
  calc
    (holdingPermutationsOfFamily S).card ≤ (Finset.univ : Finset (Sym n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = n.factorial := by simp [card_sym]

/-- Crude but exact reduction of the error term to counting overlapping
witness families.  The model-specific local-degree estimate is applied to the
right-hand side. -/
theorem overlappingFamilyContribution_le
    (P Q : BoundedPartition n) (k : ℕ) :
    overlappingFamilyContribution P Q k ≤
      (overlappingWitnessFamilies P Q k).card * n.factorial := by
  classical
  unfold overlappingFamilyContribution
  calc
    (∑ S ∈ overlappingWitnessFamilies P Q k,
        (holdingPermutationsOfFamily S).card) ≤
        ∑ _S ∈ overlappingWitnessFamilies P Q k, n.factorial := by
      apply Finset.sum_le_sum
      intro S _hS
      exact card_holdingPermutationsOfFamily_le_factorial S
    _ = (overlappingWitnessFamilies P Q k).card * n.factorial := by simp

end Family

end Kourovka213

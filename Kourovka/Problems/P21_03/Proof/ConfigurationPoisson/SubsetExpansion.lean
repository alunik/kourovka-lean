import Kourovka.Problems.P21_03.Proof.YoungConfigurationCount
import Kourovka.Problems.P21_03.Proof.Bonferroni
import Mathlib.Data.Fintype.Powerset

/-!
# Collision binomial moments as witness-family incidences

The `k`th binomial moment counts `k`-element sets of simultaneously held
collision witnesses.  This file proves that double-counting identity exactly;
no asymptotic estimate is used here.
-/

open scoped BigOperators

namespace Kourovka213

namespace CollisionWitness

/-- The witnesses held by a fixed permutation. -/
noncomputable def heldWitnesses (P Q : BoundedPartition n) (sigma : Sym n) :
    Finset (CollisionWitness P Q) := by
  classical
  exact Finset.univ.filter fun w => w.Holds sigma

@[simp]
theorem mem_heldWitnesses {P Q : BoundedPartition n} {sigma : Sym n}
    {w : CollisionWitness P Q} :
    w ∈ heldWitnesses P Q sigma ↔ w.Holds sigma := by
  classical
  simp [heldWitnesses]

theorem card_heldWitnesses (P Q : BoundedPartition n) (sigma : Sym n) :
    (heldWitnesses P Q sigma).card = collisionCount P Q sigma := by
  rfl

end CollisionWitness

/-- A finite family of witnesses all holds in `sigma`. -/
def WitnessFamilyHolds {P Q : BoundedPartition n}
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n) : Prop :=
  ∀ w ∈ S, w.Holds sigma

noncomputable instance {P Q : BoundedPartition n} (S : Finset (CollisionWitness P Q))
    (sigma : Sym n) : Decidable (WitnessFamilyHolds S sigma) := by
  classical
  unfold WitnessFamilyHolds
  infer_instance

/-- All `k`-element families of collision witnesses. -/
noncomputable def witnessFamilies (P Q : BoundedPartition n) (k : ℕ) :
    Finset (Finset (CollisionWitness P Q)) := by
  classical
  exact Finset.univ.powersetCard k

@[simp]
theorem mem_witnessFamilies {P Q : BoundedPartition n} {k : ℕ}
    {S : Finset (CollisionWitness P Q)} :
    S ∈ witnessFamilies P Q k ↔ S.card = k := by
  classical
  simp [witnessFamilies]

/-- Permutations simultaneously realizing every witness in a family. -/
noncomputable def holdingPermutationsOfFamily {P Q : BoundedPartition n}
    (S : Finset (CollisionWitness P Q)) : Finset (Sym n) := by
  classical
  exact Finset.univ.filter (WitnessFamilyHolds S)

@[simp]
theorem mem_holdingPermutationsOfFamily {P Q : BoundedPartition n}
    {S : Finset (CollisionWitness P Q)} {sigma : Sym n} :
    sigma ∈ holdingPermutationsOfFamily S ↔ WitnessFamilyHolds S sigma := by
  classical
  simp [holdingPermutationsOfFamily]

theorem subset_heldWitnesses_iff {P Q : BoundedPartition n}
    {S : Finset (CollisionWitness P Q)} {sigma : Sym n} :
    S ⊆ CollisionWitness.heldWitnesses P Q sigma ↔ WitnessFamilyHolds S sigma := by
  classical
  simp only [WitnessFamilyHolds, Finset.subset_iff]
  exact forall_congr' fun w => by
    rw [CollisionWitness.mem_heldWitnesses]

/-- Pointwise form of the binomial-moment double count. -/
theorem choose_collisionCount_eq_sum_witnessFamilies (P Q : BoundedPartition n)
    (sigma : Sym n) (k : ℕ) :
    (collisionCount P Q sigma).choose k =
      ∑ S ∈ witnessFamilies P Q k, if WitnessFamilyHolds S sigma then 1 else 0 := by
  classical
  rw [← CollisionWitness.card_heldWitnesses P Q sigma,
    ← Finset.card_powersetCard]
  rw [← Finset.card_filter]
  congr 1
  ext S
  simp [witnessFamilies, subset_heldWitnesses_iff, and_comm]

/-- Natural-valued version of the collision binomial moment. -/
noncomputable def collisionBinomialMomentNat (P Q : BoundedPartition n) (k : ℕ) : ℕ :=
  ∑ sigma : Sym n, (collisionCount P Q sigma).choose k

/-- Exact expansion of the `k`th binomial moment as a sum over witness families. -/
theorem collisionBinomialMomentNat_eq_sum_family_cards
    (P Q : BoundedPartition n) (k : ℕ) :
    collisionBinomialMomentNat P Q k =
      ∑ S ∈ witnessFamilies P Q k, (holdingPermutationsOfFamily S).card := by
  classical
  calc
    collisionBinomialMomentNat P Q k =
        ∑ sigma : Sym n, ∑ S ∈ witnessFamilies P Q k,
          if WitnessFamilyHolds S sigma then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      exact choose_collisionCount_eq_sum_witnessFamilies P Q sigma k
    _ = ∑ S ∈ witnessFamilies P Q k, ∑ sigma : Sym n,
          if WitnessFamilyHolds S sigma then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ witnessFamilies P Q k, (holdingPermutationsOfFamily S).card := by
      apply Finset.sum_congr rfl
      intro S _hS
      rw [holdingPermutationsOfFamily, Finset.card_filter]

/-- The integer-valued moment already used by `Bonferroni` is the cast of the
natural incidence count. -/
theorem binomialMoment_collisionCount_eq_natCast
    (P Q : BoundedPartition n) (k : ℕ) :
    binomialMoment (collisionCount P Q) k = collisionBinomialMomentNat P Q k := by
  classical
  simp [binomialMoment, collisionBinomialMomentNat]

end Kourovka213

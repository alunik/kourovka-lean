import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.TupleOverlapBound

/-!
# Polynomial bound for overlapping collision-witness families

This file transfers the ordered-tuple union bound to unordered witness
families.  The resulting explicit bound has degree `2k-1` in `n`, one degree
smaller than the `2k`-scale main term.
-/

namespace Kourovka213

section Enumeration

variable {W : Type*} [Fintype W] [DecidableEq W]

private noncomputable def familyEquiv (S : Finset W) (hS : S.card = k) :
    Fin k ≃ S :=
  Fintype.equivOfCardEq (by simpa using hS.symm)

/-- A canonical (noncomputable) enumeration of a `k`-element finset. -/
private noncomputable def familyTuple (S : Finset W) (hS : S.card = k) :
    Fin k → W :=
  fun i => (familyEquiv S hS i).1

private theorem familyTuple_mem (S : Finset W) (hS : S.card = k) (i : Fin k) :
    familyTuple S hS i ∈ S :=
  (familyEquiv S hS i).2

private theorem familyTuple_surjective_onto (S : Finset W) (hS : S.card = k)
    {w : W} (hw : w ∈ S) : ∃ i, familyTuple S hS i = w := by
  obtain ⟨i, hi⟩ := (familyEquiv S hS).surjective ⟨w, hw⟩
  exact ⟨i, congrArg Subtype.val hi⟩

private theorem image_familyTuple (S : Finset W) (hS : S.card = k) :
    Finset.univ.image (familyTuple S hS) = S := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    exact familyTuple_mem S hS i
  · intro hw
    obtain ⟨i, rfl⟩ := familyTuple_surjective_onto S hS hw
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

end Enumeration

section WitnessFamilies

variable {P Q : BoundedPartition n}

private noncomputable def familyTupleSource
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool → Fin n :=
  fun a => (familyTuple S hS a.1).prescribedSource a.2

private noncomputable def familyTupleTarget
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool → Fin n :=
  fun a => (familyTuple S hS a.1).prescribedTarget a.2

private noncomputable def familyOrientationEquiv
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Fin k × Bool ≃ S × Bool :=
  (familyEquiv S hS).prodCongr (Equiv.refl Bool)

private theorem injective_comp_equiv_iff {A B C : Type*}
    (e : A ≃ B) (f : B → C) :
    Function.Injective (f ∘ e) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hpre : e.symm x = e.symm y := h (by simpa using hxy)
    simpa using congrArg e hpre
  · intro h
    exact h.comp e.injective

private theorem familyTupleSource_injective_iff
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Function.Injective (familyTupleSource S hS) ↔
      Function.Injective (witnessFamilySource S) := by
  change Function.Injective
      (witnessFamilySource S ∘ familyOrientationEquiv S hS) ↔
    Function.Injective (witnessFamilySource S)
  exact injective_comp_equiv_iff (familyOrientationEquiv S hS) (witnessFamilySource S)

private theorem familyTupleTarget_injective_iff
    (S : Finset (CollisionWitness P Q)) (hS : S.card = k) :
    Function.Injective (familyTupleTarget S hS) ↔
      Function.Injective (witnessFamilyTarget S) := by
  change Function.Injective
      (witnessFamilyTarget S ∘ familyOrientationEquiv S hS) ↔
    Function.Injective (witnessFamilyTarget S)
  exact injective_comp_equiv_iff (familyOrientationEquiv S hS) (witnessFamilyTarget S)

/-- Ordered witness tuples with a repeated source or a repeated target. -/
noncomputable def overlappingWitnessTuples
    (P Q : BoundedPartition n) (k : ℕ) : Finset (Fin k → CollisionWitness P Q) := by
  classical
  exact endpointOverlappingTuples (I := Fin k)
        (fun w b => w.prescribedSource b) ∪
      endpointOverlappingTuples (I := Fin k)
        (fun w b => w.prescribedTarget b)

private noncomputable def overlappingFamilyEmbedding
    (P Q : BoundedPartition n) (k : ℕ) :
    ↥(overlappingWitnessFamilies P Q k) ↪ ↥(overlappingWitnessTuples P Q k) where
  toFun S := by
    have hmem := S.2
    have hm : S.1.card = k ∧ ¬WitnessFamilyVertexDisjoint S.1 := by
      simpa [overlappingWitnessFamilies, witnessFamilies] using hmem
    have hcard : S.1.card = k := hm.1
    refine ⟨familyTuple S.1 hcard, ?_⟩
    have hnot : ¬WitnessFamilyVertexDisjoint S.1 := hm.2
    simp only [overlappingWitnessTuples, Finset.mem_union, endpointOverlappingTuples,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hgood
    rw [not_or] at hgood
    exact hnot ⟨(familyTupleSource_injective_iff S.1 hcard).mp
        (not_not.mp hgood.1),
      (familyTupleTarget_injective_iff S.1 hcard).mp (not_not.mp hgood.2)⟩
  inj' := by
    classical
    intro S T h
    apply Subtype.ext
    have hS : S.1.card = k :=
      (by simpa [overlappingWitnessFamilies, witnessFamilies] using S.2 :
        S.1.card = k ∧ ¬WitnessFamilyVertexDisjoint S.1).1
    have hT : T.1.card = k :=
      (by simpa [overlappingWitnessFamilies, witnessFamilies] using T.2 :
        T.1.card = k ∧ ¬WitnessFamilyVertexDisjoint T.1).1
    have hfun : familyTuple S.1 hS = familyTuple T.1 hT :=
      congrArg Subtype.val h
    calc
      S.1 = Finset.univ.image (familyTuple S.1 hS) := (image_familyTuple S.1 hS).symm
      _ = Finset.univ.image (familyTuple T.1 hT) := by rw [hfun]
      _ = T.1 := image_familyTuple T.1 hT

/-- Overlapping unordered families inject into overlapping ordered tuples. -/
theorem card_overlappingWitnessFamilies_le_tuples
    (P Q : BoundedPartition n) (k : ℕ) :
    (overlappingWitnessFamilies P Q k).card ≤
      (overlappingWitnessTuples P Q k).card := by
  simpa using Fintype.card_le_of_injective
    (overlappingFamilyEmbedding P Q k) (overlappingFamilyEmbedding P Q k).injective

private theorem prescribedSource_false_ne_true (w : CollisionWitness P Q) :
    w.prescribedSource false ≠ w.prescribedSource true := by
  simpa [CollisionWitness.prescribedSource] using ne_of_lt w.left.fst_lt_snd

private theorem prescribedTarget_false_ne_true (w : CollisionWitness P Q) :
    w.prescribedTarget false ≠ w.prescribedTarget true := by
  cases h : w.flipped <;>
    simp [CollisionWitness.prescribedTarget, h, ne_of_lt w.right.fst_lt_snd,
      (ne_of_lt w.right.fst_lt_snd).symm]

/-- Explicit `O_k(n^(2k-1))` bound for overlapping witness families. -/
theorem card_overlappingWitnessFamilies_le_polynomial
    (P Q : BoundedPartition n) (k : ℕ) :
    (overlappingWitnessFamilies P Q k).card ≤
      2 * (2 * k) ^ 2 * ((9 * n ^ 2) ^ (k - 1) * (18 * n)) := by
  classical
  let B := Fintype.card (CollisionWitness P Q)
  let R := (2 * k) ^ 2 * (B ^ (k - 1) * (18 * n))
  have hsource :
      (endpointOverlappingTuples (I := Fin k)
        (fun w : CollisionWitness P Q => fun b => w.prescribedSource b)).card ≤ R := by
    unfold R B
    simpa only [Fintype.card_fin] using
      card_endpointOverlappingTuples_le (I := Fin k)
        (fun w : CollisionWitness P Q => fun b => w.prescribedSource b)
        prescribedSource_false_ne_true (18 * n)
        (fun b x => (CollisionWitness.card_prescribedSource_fiber_le P Q b x).trans
          (by omega))
  have htarget :
      (endpointOverlappingTuples (I := Fin k)
        (fun w : CollisionWitness P Q => fun b => w.prescribedTarget b)).card ≤ R := by
    unfold R B
    simpa only [Fintype.card_fin] using
      card_endpointOverlappingTuples_le (I := Fin k)
        (fun w : CollisionWitness P Q => fun b => w.prescribedTarget b)
        prescribedTarget_false_ne_true (18 * n)
        (CollisionWitness.card_prescribedTarget_fiber_le P Q)
  have htuple : (overlappingWitnessTuples P Q k).card ≤ 2 * R := by
    unfold overlappingWitnessTuples
    calc
      _ ≤ (endpointOverlappingTuples (I := Fin k)
            (fun w : CollisionWitness P Q => fun b => w.prescribedSource b)).card +
          (endpointOverlappingTuples (I := Fin k)
            (fun w : CollisionWitness P Q => fun b => w.prescribedTarget b)).card :=
        Finset.card_union_le _ _
      _ ≤ R + R := Nat.add_le_add hsource htarget
      _ = 2 * R := by omega
  have hB : B ≤ 9 * n ^ 2 := CollisionWitness.card_le_nine_mul_sq P Q
  have hpow : B ^ (k - 1) ≤ (9 * n ^ 2) ^ (k - 1) := Nat.pow_le_pow_left hB _
  have hinner : B ^ (k - 1) * (18 * n) ≤
      (9 * n ^ 2) ^ (k - 1) * (18 * n) :=
    Nat.mul_le_mul_right (18 * n) hpow
  calc
    (overlappingWitnessFamilies P Q k).card ≤
        (overlappingWitnessTuples P Q k).card :=
      card_overlappingWitnessFamilies_le_tuples P Q k
    _ ≤ 2 * R := htuple
    _ ≤ 2 * (2 * k) ^ 2 * ((9 * n ^ 2) ^ (k - 1) * (18 * n)) := by
      unfold R
      calc
        2 * ((2 * k) ^ 2 * (B ^ (k - 1) * (18 * n))) ≤
            2 * ((2 * k) ^ 2 * ((9 * n ^ 2) ^ (k - 1) * (18 * n))) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left ((2 * k) ^ 2) hinner)
        _ = 2 * (2 * k) ^ 2 * ((9 * n ^ 2) ^ (k - 1) * (18 * n)) := by
          ring

end WitnessFamilies

end Kourovka213

import Kourovka.Problems.P21_03.Proof.Basic

/-!
# The bounded Young-subgroup configuration model

A partition is encoded by a labelling function; equal labels mean equal blocks.  Empty
labels are harmless.  This representation avoids quotienting by a set-partition type and
is particularly convenient for the random-conjugator model.
-/

namespace Kourovka213

/-- A partition of `Fin n`, all of whose blocks have cardinality at most four. -/
structure BoundedPartition (n : ℕ) where
  block : Fin n → Fin n
  card_fiber_le_four : ∀ i, Fintype.card {x // block x = i} ≤ 4

namespace BoundedPartition

/-- A canonically ordered pair of distinct points in one block. -/
structure PairIn (P : BoundedPartition n) where
  fst : Fin n
  snd : Fin n
  fst_lt_snd : fst < snd
  same_block : P.block fst = P.block snd

instance (P : BoundedPartition n) : Finite P.PairIn :=
  Finite.of_injective (fun p => (p.fst, p.snd)) fun p q h => by
    cases p
    cases q
    simp_all
noncomputable instance (P : BoundedPartition n) : Fintype P.PairIn := Fintype.ofFinite _

end BoundedPartition

/-- A prospective double edge between a left within-block pair and a right within-block pair.
The Boolean records one of the two bijections between the pairs. -/
structure CollisionWitness (P Q : BoundedPartition n) where
  left : P.PairIn
  right : Q.PairIn
  flipped : Bool

instance (P Q : BoundedPartition n) : Finite (CollisionWitness P Q) :=
  Finite.of_injective (fun w => ((w.left, w.right), w.flipped)) fun p q h => by
    cases p
    cases q
    simp_all
noncomputable instance (P Q : BoundedPartition n) : Fintype (CollisionWitness P Q) :=
  Fintype.ofFinite _

namespace CollisionWitness

/-- The two prescribed images of a collision witness occur in `sigma`. -/
def Holds {P Q : BoundedPartition n} (w : CollisionWitness P Q) (sigma : Sym n) : Prop :=
  if w.flipped then
    sigma w.left.fst = w.right.snd ∧ sigma w.left.snd = w.right.fst
  else
    sigma w.left.fst = w.right.fst ∧ sigma w.left.snd = w.right.snd

instance {P Q : BoundedPartition n} (w : CollisionWitness P Q) (sigma : Sym n) :
    Decidable (w.Holds sigma) := by
  unfold Holds
  infer_instance

end CollisionWitness

/-- Number of unordered same-cell point-pairs in the table defined by `P`, `Q`, and `sigma`. -/
noncomputable def collisionCount (P Q : BoundedPartition n) (sigma : Sym n) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : CollisionWitness P Q => w.Holds sigma).card

/-- Every intersection of a `P`-block with the inverse image of a `Q`-block has size at most one. -/
def IsSimple (P Q : BoundedPartition n) (sigma : Sym n) : Prop :=
  ∀ ⦃a b : Fin n⦄, a ≠ b → P.block a = P.block b →
    Q.block (sigma a) ≠ Q.block (sigma b)

theorem isSimple_iff_collisionCount_eq_zero (P Q : BoundedPartition n) (sigma : Sym n) :
    IsSimple P Q sigma ↔ collisionCount P Q sigma = 0 := by
  classical
  constructor
  · intro hs
    rw [collisionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w _ hw
    have hne : w.left.fst ≠ w.left.snd := ne_of_lt w.left.fst_lt_snd
    have hsep := hs hne w.left.same_block
    cases hflip : w.flipped with
    | false =>
        have hw' : sigma w.left.fst = w.right.fst ∧
            sigma w.left.snd = w.right.snd := by
          simpa [CollisionWitness.Holds, hflip] using hw
        exact hsep (by simpa [hw'.1, hw'.2] using w.right.same_block)
    | true =>
        have hw' : sigma w.left.fst = w.right.snd ∧
            sigma w.left.snd = w.right.fst := by
          simpa [CollisionWitness.Holds, hflip] using hw
        exact hsep (by simpa [hw'.1, hw'.2] using w.right.same_block.symm)
  · intro hzero a b hab hsab
    intro hqab
    have himage : sigma a ≠ sigma b := fun h => hab (sigma.injective h)
    have contradict_with (w : CollisionWitness P Q) (hw : w.Holds sigma) : False := by
      have hwmem : w ∈ Finset.univ.filter fun u : CollisionWitness P Q => u.Holds sigma := by
        simp [hw]
      have hpos : 0 < collisionCount P Q sigma := by
        rw [collisionCount]
        exact Finset.card_pos.mpr ⟨w, hwmem⟩
      omega
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · rcases lt_or_gt_of_ne himage with himagelt | himagegt
      · let w : CollisionWitness P Q :=
          { left := ⟨a, b, hablt, hsab⟩
            right := ⟨sigma a, sigma b, himagelt, hqab⟩
            flipped := false }
        exact contradict_with w (by simp [w, CollisionWitness.Holds])
      · let w : CollisionWitness P Q :=
          { left := ⟨a, b, hablt, hsab⟩
            right := ⟨sigma b, sigma a, himagegt, hqab.symm⟩
            flipped := true }
        exact contradict_with w (by simp [w, CollisionWitness.Holds])
    · have himage' : sigma b ≠ sigma a := himage.symm
      rcases lt_or_gt_of_ne himage' with himagelt | himagegt
      · let w : CollisionWitness P Q :=
          { left := ⟨b, a, hbalt, hsab.symm⟩
            right := ⟨sigma b, sigma a, himagelt, hqab.symm⟩
            flipped := false }
        exact contradict_with w (by simp [w, CollisionWitness.Holds])
      · let w : CollisionWitness P Q :=
          { left := ⟨b, a, hbalt, hsab.symm⟩
            right := ⟨sigma a, sigma b, himagegt, hqab⟩
            flipped := true }
        exact contradict_with w (by simp [w, CollisionWitness.Holds])

end Kourovka213

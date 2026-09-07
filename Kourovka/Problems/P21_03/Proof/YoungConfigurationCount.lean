import Kourovka.Problems.P21_03.Proof.YoungConfiguration
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fintype

/-!
# Exact counts in the bounded Young-subgroup configuration model

This file contains only finite cardinality arguments.  In particular, it does not use a
probability space: the first moment is the exact incidence count divided by `n !`.
-/

namespace Kourovka213

namespace BoundedPartition

/-- A directed pair of distinct points in one block. -/
structure OrderedPairIn (P : BoundedPartition n) where
  fst : Fin n
  snd : Fin n
  fst_ne_snd : fst ≠ snd
  same_block : P.block fst = P.block snd

instance (P : BoundedPartition n) : Finite P.OrderedPairIn :=
  Finite.of_injective (fun p => (p.fst, p.snd)) fun p q h => by
    cases p
    cases q
    simp_all

noncomputable instance (P : BoundedPartition n) : Fintype P.OrderedPairIn :=
  Fintype.ofFinite _

/-- Giving an orientation bit to an unordered same-block pair produces every directed pair
exactly once. -/
def pairInProdBoolEquivOrderedPairIn (P : BoundedPartition n) :
    P.PairIn × Bool ≃ P.OrderedPairIn where
  toFun p := match p.2 with
    | false => ⟨p.1.fst, p.1.snd, ne_of_lt p.1.fst_lt_snd, p.1.same_block⟩
    | true => ⟨p.1.snd, p.1.fst, (ne_of_lt p.1.fst_lt_snd).symm, p.1.same_block.symm⟩
  invFun p := if h : p.fst < p.snd then
      (⟨p.fst, p.snd, h, p.same_block⟩, false)
    else
      (⟨p.snd, p.fst, (lt_or_gt_of_ne p.fst_ne_snd).resolve_left h,
        p.same_block.symm⟩, true)
  left_inv p := by
    rcases p with ⟨p, b⟩
    cases b
    · simp [ne_of_lt p.fst_lt_snd, p.fst_lt_snd]
    · simp [ne_of_lt p.fst_lt_snd, p.fst_lt_snd,
        (not_lt_of_ge p.fst_lt_snd.le)]
  right_inv p := by
    rcases lt_or_gt_of_ne p.fst_ne_snd with h | h
    · simp [h]
    · simp [h, not_lt_of_ge h.le]

/-- A directed pair can be viewed as its first point followed by a choice of a distinct
second point in the same block. -/
def orderedPairInEquivSigma (P : BoundedPartition n) :
    P.OrderedPairIn ≃ Σ x : Fin n, {y : Fin n // y ≠ x ∧ P.block y = P.block x} where
  toFun p := ⟨p.fst, ⟨p.snd, p.fst_ne_snd.symm, p.same_block.symm⟩⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1.symm, p.2.2.2.symm⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

private theorem card_second_choices_le_three (P : BoundedPartition n) (x : Fin n) :
    Fintype.card {y : Fin n // y ≠ x ∧ P.block y = P.block x} ≤ 3 := by
  let f : {y : Fin n // y ≠ x ∧ P.block y = P.block x} →
      {y : Fin n // P.block y = P.block x} := fun y => ⟨y, y.2.2⟩
  have hf : Function.Injective f := fun y z h => by
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val h
  have hns : ¬ Function.Surjective f := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨x, rfl⟩
    exact y.2.1 (congrArg Subtype.val hy)
  have hlt := Fintype.card_lt_of_injective_not_surjective f hf hns
  have hle := P.card_fiber_le_four (P.block x)
  omega

private theorem card_orderedPairIn_le_three_mul (P : BoundedPartition n) :
    Fintype.card P.OrderedPairIn ≤ 3 * n := by
  rw [Fintype.card_congr (orderedPairInEquivSigma P), Fintype.card_sigma]
  calc
    (∑ x : Fin n, Fintype.card {y : Fin n // y ≠ x ∧ P.block y = P.block x}) ≤
        ∑ _x : Fin n, 3 := by
      apply Finset.sum_le_sum
      intro x _
      exact card_second_choices_le_three P x
    _ = 3 * n := by simp [mul_comm]

/-- A partition with blocks of size at most four has at most `3n/2` within-block pairs.
The integral form avoids any rounding convention. -/
theorem two_mul_card_pairIn_le_three_mul (P : BoundedPartition n) :
    2 * Fintype.card P.PairIn ≤ 3 * n := by
  have heq := Fintype.card_congr (pairInProdBoolEquivOrderedPairIn P)
  simp only [Fintype.card_prod, Fintype.card_bool] at heq
  calc
    2 * Fintype.card P.PairIn = Fintype.card P.OrderedPairIn := by
      simpa [mul_comm] using heq
    _ ≤ 3 * n := card_orderedPairIn_le_three_mul P

end BoundedPartition

namespace CollisionWitness

/-- Forgetting the field names identifies a collision witness with two pairs and a bit. -/
def equivPairPairBool (P Q : BoundedPartition n) :
    CollisionWitness P Q ≃ (P.PairIn × Q.PairIn) × Bool where
  toFun w := ((w.left, w.right), w.flipped)
  invFun w := ⟨w.1.1, w.1.2, w.2⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- There are exactly two orientations for every left/right pair choice. -/
theorem card_eq_two_mul (P Q : BoundedPartition n) :
    Fintype.card (CollisionWitness P Q) =
      2 * Fintype.card P.PairIn * Fintype.card Q.PairIn := by
  rw [Fintype.card_congr (equivPairPairBool P Q)]
  simp [Fintype.card_prod]
  ac_rfl

end CollisionWitness

section TwoPointCompletion

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem subtypeCongr_apply_of_mem {p q : α → Prop}
    [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : α) (hx : p x) : Equiv.subtypeCongr e f x = e ⟨x, hx⟩ := by
  simp [Equiv.subtypeCongr, hx]

private theorem subtypeCongr_apply_of_not_mem {p q : α → Prop}
    [DecidablePred p] [DecidablePred q]
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : α) (hx : ¬p x) : Equiv.subtypeCongr e f x = f ⟨x, hx⟩ := by
  simp [Equiv.subtypeCongr, hx]

/-- The prescribed equivalence between two labelled two-point subsets. -/
private def prescribedPairEquiv {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    {x : α // x = a ∨ x = b} ≃ {x : α // x = c ∨ x = d} where
  toFun x := if h : x.1 = a then ⟨c, Or.inl rfl⟩ else ⟨d, Or.inr rfl⟩
  invFun x := if h : x.1 = c then ⟨a, Or.inl rfl⟩ else ⟨b, Or.inr rfl⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    rcases hx with rfl | rfl <;>
      simp [hab, hab.symm, hcd, hcd.symm]
  right_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    rcases hx with rfl | rfl <;>
      simp [hab, hab.symm, hcd, hcd.symm]

@[simp]
private theorem prescribedPairEquiv_apply_left {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    prescribedPairEquiv hab hcd ⟨a, Or.inl rfl⟩ = ⟨c, Or.inl rfl⟩ := by
  simp [prescribedPairEquiv, hab, hab.symm, hcd, hcd.symm]

@[simp]
private theorem prescribedPairEquiv_apply_right {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    prescribedPairEquiv hab hcd ⟨b, Or.inr rfl⟩ = ⟨d, Or.inr rfl⟩ := by
  simp [prescribedPairEquiv, hab, hab.symm, hcd, hcd.symm]

private theorem pair_mem_iff_image_mem {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d)
    (σ : Equiv.Perm α) (hσ : σ a = c ∧ σ b = d) (x : α) :
    (x = a ∨ x = b) ↔ (σ x = c ∨ σ x = d) := by
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hσ.1
    · exact Or.inr hσ.2
  · rintro (hx | hx)
    · exact Or.inl (σ.injective (hx.trans hσ.1.symm))
    · exact Or.inr (σ.injective (hx.trans hσ.2.symm))

/-- Completing a prescribed bijection on two points is equivalent to choosing an arbitrary
bijection of the complements. -/
private noncomputable def twoPointCompletionEquiv {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    {σ : Equiv.Perm α // σ a = c ∧ σ b = d} ≃
      ({x : α // ¬(x = a ∨ x = b)} ≃ {x : α // ¬(x = c ∨ x = d)}) where
  toFun σ := σ.1.subtypeEquiv fun x => not_congr (pair_mem_iff_image_mem hab hcd σ.1 σ.2 x)
  invFun f :=
    ⟨Equiv.subtypeCongr (prescribedPairEquiv hab hcd) f, by
      constructor
      · calc
          Equiv.subtypeCongr (prescribedPairEquiv hab hcd) f a =
              prescribedPairEquiv hab hcd ⟨a, Or.inl rfl⟩ :=
            subtypeCongr_apply_of_mem (p := fun x => x = a ∨ x = b)
              (q := fun x => x = c ∨ x = d) _ _ _ (Or.inl rfl)
          _ = c := by
            exact congrArg Subtype.val (prescribedPairEquiv_apply_left hab hcd)
      · calc
          Equiv.subtypeCongr (prescribedPairEquiv hab hcd) f b =
              prescribedPairEquiv hab hcd ⟨b, Or.inr rfl⟩ :=
            subtypeCongr_apply_of_mem (p := fun x => x = a ∨ x = b)
              (q := fun x => x = c ∨ x = d) _ _ _ (Or.inr rfl)
          _ = d := by
            exact congrArg Subtype.val (prescribedPairEquiv_apply_right hab hcd)⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x = a ∨ x = b
    · calc
        Equiv.subtypeCongr (prescribedPairEquiv hab hcd) _ x =
            prescribedPairEquiv hab hcd ⟨x, hx⟩ :=
          subtypeCongr_apply_of_mem (p := fun x => x = a ∨ x = b)
            (q := fun x => x = c ∨ x = d) _ _ _ hx
        _ = σ.1 x := by
          rcases hx with rfl | rfl
          · simpa using σ.2.1.symm
          · simpa using σ.2.2.symm
    · refine (subtypeCongr_apply_of_not_mem
        (p := fun x => x = a ∨ x = b) (q := fun x => x = c ∨ x = d)
        (prescribedPairEquiv hab hcd)
        (σ.1.subtypeEquiv fun x =>
          not_congr (pair_mem_iff_image_mem hab hcd σ.1 σ.2 x)) x hx).trans ?_
      rfl
  right_inv f := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    calc
      Equiv.subtypeCongr (prescribedPairEquiv hab hcd) f x.1 = f ⟨x.1, x.2⟩ :=
        subtypeCongr_apply_of_not_mem (p := fun x => x = a ∨ x = b)
          (q := fun x => x = c ∨ x = d) _ _ _ x.2
      _ = f x := rfl

private theorem card_pair_subtype {a b : α} (hab : a ≠ b) :
    Fintype.card {x : α // x = a ∨ x = b} = 2 := by
  rw [Fintype.card_subtype]
  have hfinset : (Finset.univ.filter fun x : α => x = a ∨ x = b) = {a, b} := by
    ext x
    simp [eq_comm]
  rw [hfinset]
  simp [hab]

private theorem card_pair_complement {a b : α} (hab : a ≠ b) :
    Fintype.card {x : α // ¬(x = a ∨ x = b)} = Fintype.card α - 2 := by
  rw [Fintype.card_subtype_compl, card_pair_subtype hab]

/-- Exact number of permutations realizing two prescribed, distinct images. -/
theorem card_perm_apply_two {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    Fintype.card {σ : Equiv.Perm α // σ a = c ∧ σ b = d} =
      (Fintype.card α - 2).factorial := by
  rw [Fintype.card_congr (twoPointCompletionEquiv hab hcd)]
  calc
    Fintype.card ({x : α // ¬(x = a ∨ x = b)} ≃ {x : α // ¬(x = c ∨ x = d)}) =
        (Fintype.card {x : α // ¬(x = a ∨ x = b)}).factorial :=
      Fintype.card_equiv ((prescribedPairEquiv hab hcd).toCompl)
    _ = (Fintype.card α - 2).factorial := by rw [card_pair_complement hab]

end TwoPointCompletion

namespace CollisionWitness

/-- The finite set of permutations realizing a witness. -/
noncomputable def holdingPermutations {P Q : BoundedPartition n} (w : CollisionWitness P Q) :
    Finset (Sym n) := by
  classical
  exact Finset.univ.filter w.Holds

/-- Every collision witness fixes two distinct images and hence is realized by exactly
`(n - 2)!` permutations. -/
theorem card_holdingPermutations {P Q : BoundedPartition n} (w : CollisionWitness P Q) :
    w.holdingPermutations.card = (n - 2).factorial := by
  classical
  rw [holdingPermutations, ← Fintype.card_subtype]
  cases hflip : w.flipped with
  | false =>
    simpa [holdingPermutations, Holds, hflip] using
      (card_perm_apply_two (ne_of_lt w.left.fst_lt_snd)
        (ne_of_lt w.right.fst_lt_snd))
  | true =>
    simpa [holdingPermutations, Holds, hflip] using
      (card_perm_apply_two (ne_of_lt w.left.fst_lt_snd)
        (ne_of_lt w.right.fst_lt_snd).symm)

end CollisionWitness

/-- Total number of incidences `(sigma, witness held by sigma)`. -/
noncomputable def collisionFirstMomentNat (P Q : BoundedPartition n) : ℕ :=
  ∑ σ : Sym n, collisionCount P Q σ

theorem collisionFirstMomentNat_eq (P Q : BoundedPartition n) :
    collisionFirstMomentNat P Q =
      Fintype.card (CollisionWitness P Q) * (n - 2).factorial := by
  classical
  calc
    collisionFirstMomentNat P Q =
        ∑ σ : Sym n, ∑ w : CollisionWitness P Q, if w.Holds σ then 1 else 0 := by
      simp only [collisionFirstMomentNat, collisionCount, Finset.card_filter]
    _ = ∑ w : CollisionWitness P Q, ∑ σ : Sym n, if w.Holds σ then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ w : CollisionWitness P Q, w.holdingPermutations.card := by
      apply Finset.sum_congr rfl
      intro w _
      rw [CollisionWitness.holdingPermutations, Finset.card_filter]
    _ = Fintype.card (CollisionWitness P Q) * (n - 2).factorial := by
      simp [CollisionWitness.card_holdingPermutations]

/-- The exact first moment of the collision count under the uniform distribution on `S_n`. -/
noncomputable def collisionMean (P Q : BoundedPartition n) : ℝ :=
  collisionFirstMomentNat P Q / Fintype.card (Sym n)

private theorem factorial_eq_mul_mul_factorial_sub_two {n : ℕ} (hn : 2 ≤ n) :
    n.factorial = n * (n - 1) * (n - 2).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [show 2 + m = m + 2 by omega]
  simp [Nat.factorial_succ, Nat.mul_assoc]

/-- Exact mean in terms of the two within-block pair counts. -/
theorem collisionMean_eq (P Q : BoundedPartition n) (hn : 2 ≤ n) :
    collisionMean P Q =
      (2 * Fintype.card P.PairIn * Fintype.card Q.PairIn : ℝ) /
        ((n : ℝ) * (n - 1)) := by
  rw [collisionMean, collisionFirstMomentNat_eq, CollisionWitness.card_eq_two_mul,
    card_sym, factorial_eq_mul_mul_factorial_sub_two hn]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  norm_num only [Nat.cast_one]
  have hfac : (0 : ℝ) < ((n - 2).factorial : ℕ) := by positivity
  field_simp

/-- Uniform upper bound on the collision mean for block sizes at most four. -/
theorem collisionMean_le (P Q : BoundedPartition n) (hn : 2 ≤ n) :
    collisionMean P Q ≤ (9 / 2 : ℝ) * n / (n - 1) := by
  rw [collisionMean_eq P Q hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast (show 1 < n by omega))
  have hP : (2 : ℝ) * Fintype.card P.PairIn ≤ 3 * n := by
    exact_mod_cast P.two_mul_card_pairIn_le_three_mul
  have hQ : (2 : ℝ) * Fintype.card Q.PairIn ≤ 3 * n := by
    exact_mod_cast Q.two_mul_card_pairIn_le_three_mul
  have hP0 : (0 : ℝ) ≤ Fintype.card P.PairIn := by positivity
  have hQ0 : (0 : ℝ) ≤ Fintype.card Q.PairIn := by positivity
  have hmul :
      ((2 : ℝ) * Fintype.card P.PairIn) * (2 * Fintype.card Q.PairIn) ≤
        (3 * n) * (3 * n) :=
    mul_le_mul hP hQ (by positivity) (by positivity)
  have hnum :
      (2 * Fintype.card P.PairIn * Fintype.card Q.PairIn : ℝ) ≤
        (9 / 2 : ℝ) * n * n := by
    nlinarith
  calc
    (2 * Fintype.card P.PairIn * Fintype.card Q.PairIn : ℝ) / (n * (n - 1)) ≤
        ((9 / 2 : ℝ) * n * n) / (n * (n - 1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (9 / 2 : ℝ) * n / (n - 1) := by field_simp

end Kourovka213

import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.DisjointFamilies

/-!
# Local endpoint degrees of collision witnesses

For a bounded partition, a point has at most three partners in its block.  It
follows that a fixed oriented source endpoint belongs to at most `9n`
collision witnesses.  These local degree bounds are the combinatorial input to
the overlap estimate.
-/

namespace Kourovka213

namespace BoundedPartition

/-- Other points in the block containing `x`. -/
def OtherInBlock (P : BoundedPartition n) (x : Fin n) :=
  {y : Fin n // y ≠ x ∧ P.block y = P.block x}

instance (P : BoundedPartition n) (x : Fin n) : Finite (P.OtherInBlock x) := by
  unfold OtherInBlock
  infer_instance

noncomputable instance (P : BoundedPartition n) (x : Fin n) :
    Fintype (P.OtherInBlock x) := Fintype.ofFinite _

theorem card_otherInBlock_le_three (P : BoundedPartition n) (x : Fin n) :
    Fintype.card (P.OtherInBlock x) ≤ 3 := by
  let f : P.OtherInBlock x → {y : Fin n // P.block y = P.block x} :=
    fun y => ⟨y.1, y.2.2⟩
  have hf : Function.Injective f := fun y z h => by
    apply Subtype.ext
    exact congrArg (fun u : {y : Fin n // P.block y = P.block x} => u.1) h
  have hns : ¬Function.Surjective f := by
    intro hs
    obtain ⟨y, hy⟩ := hs ⟨x, rfl⟩
    exact y.2.1 (congrArg Subtype.val hy)
  have hlt := Fintype.card_lt_of_injective_not_surjective f hf hns
  have hle := P.card_fiber_le_four (P.block x)
  omega

end BoundedPartition

namespace CollisionWitness

private def sourceFiberEmbeddingFalse (P Q : BoundedPartition n) (x : Fin n) :
    {w : CollisionWitness P Q // w.prescribedSource false = x} ↪
      (P.OtherInBlock x × Q.PairIn) × Bool where
  toFun w :=
    ((⟨w.1.left.snd,
      by
        have hx : w.1.left.fst = x := by simpa [prescribedSource] using w.2
        constructor
        · intro h
          exact (ne_of_lt w.1.left.fst_lt_snd) (hx.trans h.symm)
        · exact w.1.left.same_block.symm.trans (congrArg P.block hx)⟩,
      w.1.right), w.1.flipped)
  inj' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    apply Subtype.ext
    have huf : u.left.fst = x := by simpa [prescribedSource] using hu
    have hvf : v.left.fst = x := by simpa [prescribedSource] using hv
    rcases u with ⟨ul, ur, ub⟩
    rcases v with ⟨vl, vr, vb⟩
    have hpartner : ul.snd = vl.snd :=
      congrArg (fun z => z.1.1.1) h
    have hright : ur = vr := congrArg (fun z => z.1.2) h
    have hbool : ub = vb := congrArg Prod.snd h
    have hleft : ul = vl := by
      cases ul
      cases vl
      simp_all
    cases hleft
    cases hright
    cases hbool
    rfl

private def sourceFiberEmbeddingTrue (P Q : BoundedPartition n) (x : Fin n) :
    {w : CollisionWitness P Q // w.prescribedSource true = x} ↪
      (P.OtherInBlock x × Q.PairIn) × Bool where
  toFun w :=
    ((⟨w.1.left.fst,
      by
        have hx : w.1.left.snd = x := by simpa [prescribedSource] using w.2
        constructor
        · intro h
          exact (ne_of_lt w.1.left.fst_lt_snd) (h.trans hx.symm)
        · exact w.1.left.same_block.trans (congrArg P.block hx)⟩,
      w.1.right), w.1.flipped)
  inj' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    apply Subtype.ext
    have hus : u.left.snd = x := by simpa [prescribedSource] using hu
    have hvs : v.left.snd = x := by simpa [prescribedSource] using hv
    rcases u with ⟨ul, ur, ub⟩
    rcases v with ⟨vl, vr, vb⟩
    have hpartner : ul.fst = vl.fst :=
      congrArg (fun z => z.1.1.1) h
    have hright : ur = vr := congrArg (fun z => z.1.2) h
    have hbool : ub = vb := congrArg Prod.snd h
    have hleft : ul = vl := by
      cases ul
      cases vl
      simp_all
    cases hleft
    cases hright
    cases hbool
    rfl

/-- At a fixed orientation, at most `9n` witnesses use a specified source
point. -/
theorem card_prescribedSource_fiber_le (P Q : BoundedPartition n)
    (b : Bool) (x : Fin n) :
    Fintype.card {w : CollisionWitness P Q // w.prescribedSource b = x} ≤ 9 * n := by
  have hother := P.card_otherInBlock_le_three x
  have hpairs := Q.two_mul_card_pairIn_le_three_mul
  cases b with
  | false =>
      have hinj := Fintype.card_le_of_injective
        (sourceFiberEmbeddingFalse P Q x)
        (sourceFiberEmbeddingFalse P Q x).injective
      simp only [Fintype.card_prod, Fintype.card_bool] at hinj
      have hmul :
          Fintype.card (P.OtherInBlock x) * Fintype.card Q.PairIn * 2 ≤
            3 * Fintype.card Q.PairIn * 2 := by
        exact Nat.mul_le_mul_right 2
          (Nat.mul_le_mul_right (Fintype.card Q.PairIn) hother)
      omega
  | true =>
      have hinj := Fintype.card_le_of_injective
        (sourceFiberEmbeddingTrue P Q x)
        (sourceFiberEmbeddingTrue P Q x).injective
      simp only [Fintype.card_prod, Fintype.card_bool] at hinj
      have hmul :
          Fintype.card (P.OtherInBlock x) * Fintype.card Q.PairIn * 2 ≤
            3 * Fintype.card Q.PairIn * 2 := by
        exact Nat.mul_le_mul_right 2
          (Nat.mul_le_mul_right (Fintype.card Q.PairIn) hother)
      omega

/-- Reverse the roles of the two partitions in a collision witness. -/
def transposeEquiv (P Q : BoundedPartition n) :
    CollisionWitness P Q ≃ CollisionWitness Q P where
  toFun w := ⟨w.right, w.left, w.flipped⟩
  invFun w := ⟨w.right, w.left, w.flipped⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- Orientation at which the transposed witness has the original prescribed
target as its source. -/
def targetSourceOrientation {P Q : BoundedPartition n}
    (w : CollisionWitness P Q) (b : Bool) : Bool :=
  if w.flipped then !b else b

theorem prescribedSource_transposeEquiv_targetSourceOrientation
    {P Q : BoundedPartition n} (w : CollisionWitness P Q) (b : Bool) :
    ((transposeEquiv P Q) w).prescribedSource (targetSourceOrientation w b) =
      w.prescribedTarget b := by
  cases b <;> cases h : w.flipped <;>
    simp [transposeEquiv, targetSourceOrientation, prescribedSource, prescribedTarget, h]

private def targetFiberEmbedding (P Q : BoundedPartition n) (b : Bool) (x : Fin n) :
    {w : CollisionWitness P Q // w.prescribedTarget b = x} ↪
      Σ c : Bool,
        {u : CollisionWitness Q P // u.prescribedSource c = x} where
  toFun w :=
    ⟨targetSourceOrientation w.1 b,
      ⟨(transposeEquiv P Q) w.1,
        (prescribedSource_transposeEquiv_targetSourceOrientation w.1 b).trans w.2⟩⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply (transposeEquiv P Q).injective
    exact congrArg (fun z => z.2.1) h

/-- At a fixed orientation, at most `18n` witnesses use a specified target
point.  (The harmless factor two records which source orientation appears
after transposing the witness.) -/
theorem card_prescribedTarget_fiber_le (P Q : BoundedPartition n)
    (b : Bool) (x : Fin n) :
    Fintype.card {w : CollisionWitness P Q // w.prescribedTarget b = x} ≤ 18 * n := by
  have hinj := Fintype.card_le_of_injective
    (targetFiberEmbedding P Q b x) (targetFiberEmbedding P Q b x).injective
  have hcod :
      Fintype.card (Σ c : Bool,
        {u : CollisionWitness Q P // u.prescribedSource c = x}) ≤ 18 * n := by
    rw [Fintype.card_sigma]
    calc
      (∑ c : Bool,
          Fintype.card {u : CollisionWitness Q P // u.prescribedSource c = x}) ≤
          ∑ _c : Bool, 9 * n := by
        apply Finset.sum_le_sum
        intro c _hc
        exact card_prescribedSource_fiber_le Q P c x
      _ = 18 * n := by simp; omega
  exact hinj.trans hcod

/-- Quadratic bound for the total witness set. -/
theorem card_le_nine_mul_sq (P Q : BoundedPartition n) :
    Fintype.card (CollisionWitness P Q) ≤ 9 * n ^ 2 := by
  rw [card_eq_two_mul]
  have hP := P.two_mul_card_pairIn_le_three_mul
  have hQ := Q.two_mul_card_pairIn_le_three_mul
  have hQ' : Fintype.card Q.PairIn ≤ 3 * n := by omega
  calc
    2 * Fintype.card P.PairIn * Fintype.card Q.PairIn ≤
        (2 * Fintype.card P.PairIn) * (3 * n) :=
      Nat.mul_le_mul_left _ hQ'
    _ ≤ (3 * n) * (3 * n) := Nat.mul_le_mul_right _ hP
    _ = 9 * n ^ 2 := by ring

end CollisionWitness

end Kourovka213

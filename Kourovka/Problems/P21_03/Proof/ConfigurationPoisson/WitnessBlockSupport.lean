import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.BlockMapCount
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.SupportStrata

/-!
# Occupied partition blocks of a witness family

Every occupied block contains the two distinct endpoints of one witness.  Thus
twice the number of occupied blocks is at most the endpoint-support size.
-/

namespace Kourovka213

section GenericEndpoints

variable {I X L : Type*}
variable [Fintype I] [DecidableEq I]
variable [Fintype X] [DecidableEq X]
variable [Fintype L] [DecidableEq L]

/-- Distinct values used by an endpoint map. -/
def endpointSupport (f : I × Bool → X) : Finset X :=
  Finset.univ.image f

private theorem exists_orientedRepresentative
    (block : X → L) (f : I × Bool → X)
    (a : usedBlockLabels block f) :
    ∃ z : I × Bool, block (f z) = a.1 := by
  simpa [usedBlockLabels] using a.2

private noncomputable def orientedRepresentative
    (block : X → L) (f : I × Bool → X)
    (a : usedBlockLabels block f) : I × Bool :=
  Classical.choose (exists_orientedRepresentative block f a)

private theorem block_orientedRepresentative
    (block : X → L) (f : I × Bool → X)
  (a : usedBlockLabels block f) :
    block (f (orientedRepresentative block f a)) = a.1 := by
  exact Classical.choose_spec (exists_orientedRepresentative block f a)

private noncomputable def representativeIndex
    (block : X → L) (f : I × Bool → X)
    (a : usedBlockLabels block f) : I :=
  (orientedRepresentative block f a).1

private theorem block_representativeIndex
    (block : X → L) (f : I × Bool → X)
    (hsame : ∀ i, block (f (i, false)) = block (f (i, true)))
    (a : usedBlockLabels block f) (b : Bool) :
    block (f (representativeIndex block f a, b)) = a.1 := by
  have hrep := block_orientedRepresentative block f a
  cases hc : orientedRepresentative block f a with
  | mk i c =>
      unfold representativeIndex
      rw [hc]
      rw [hc] at hrep
      cases c <;> cases b
      · exact hrep
      · exact (hsame i).symm.trans hrep
      · exact (hsame i).trans hrep
      · exact hrep

noncomputable def usedBlocksBoolEmbedding
    (block : X → L) (f : I × Bool → X)
    (hne : ∀ i, f (i, false) ≠ f (i, true))
    (hsame : ∀ i, block (f (i, false)) = block (f (i, true))) :
    usedBlockLabels block f × Bool ↪ endpointSupport f where
  toFun a := ⟨f (representativeIndex block f a.1, a.2), by
    exact Finset.mem_image.mpr
      ⟨(representativeIndex block f a.1, a.2), Finset.mem_univ _, rfl⟩⟩
  inj' := by
    intro a c h
    have hvalue := congrArg Subtype.val h
    change f (representativeIndex block f a.1, a.2) =
      f (representativeIndex block f c.1, c.2) at hvalue
    have hblock := congrArg (fun x : endpointSupport f => block x.1) h
    have hlabel : a.1 = c.1 := by
      apply Subtype.ext
      simpa only [block_representativeIndex block f hsame] using hblock
    have hrepIndex : representativeIndex block f a.1 =
        representativeIndex block f c.1 :=
      congrArg (representativeIndex block f) hlabel
    apply Prod.ext hlabel
    cases ha : a.2 <;> cases hc : c.2
    · rfl
    · rw [← hrepIndex] at hvalue
      exact (hne (representativeIndex block f a.1)
        (by simpa [ha, hc] using hvalue)).elim
    · exact (hne (representativeIndex block f a.1)
        (by rw [← hrepIndex] at hvalue
            simpa [ha, hc] using hvalue.symm)).elim
    · rfl

/-- Each occupied label accounts for at least two distinct endpoint values. -/
theorem two_mul_card_usedBlockLabels_le_endpointSupport
    (block : X → L) (f : I × Bool → X)
    (hne : ∀ i, f (i, false) ≠ f (i, true))
    (hsame : ∀ i, block (f (i, false)) = block (f (i, true))) :
    2 * (usedBlockLabels block f).card ≤ (endpointSupport f).card := by
  have hcard := Fintype.card_le_of_injective
    (usedBlocksBoolEmbedding block f hne hsame)
    (usedBlocksBoolEmbedding block f hne hsame).injective
  simpa [Fintype.card_prod, mul_comm] using hcard

end GenericEndpoints

section WitnessEndpoints

variable {P Q : BoundedPartition n}

/-- `P`-blocks occupied by the source endpoints of a witness family. -/
def witnessFamilySourceBlocks (S : Finset (CollisionWitness P Q)) : Finset (Fin n) :=
  usedBlockLabels P.block (witnessFamilySource S)

/-- `Q`-blocks occupied by the target endpoints of a witness family. -/
def witnessFamilyTargetBlocks (S : Finset (CollisionWitness P Q)) : Finset (Fin n) :=
  usedBlockLabels Q.block (witnessFamilyTarget S)

private theorem source_endpoints_ne (S : Finset (CollisionWitness P Q)) (i : S) :
    witnessFamilySource S (i, false) ≠ witnessFamilySource S (i, true) := by
  simpa [witnessFamilySource, CollisionWitness.prescribedSource] using
    ne_of_lt i.1.left.fst_lt_snd

private theorem source_endpoints_same_block
    (S : Finset (CollisionWitness P Q)) (i : S) :
    P.block (witnessFamilySource S (i, false)) =
      P.block (witnessFamilySource S (i, true)) := by
  simpa [witnessFamilySource, CollisionWitness.prescribedSource] using
    i.1.left.same_block

private theorem pairIn_eq_of_endpoints_eq (u v : P.PairIn)
    (hfst : u.fst = v.fst) (hsnd : u.snd = v.snd) : u = v := by
  cases u
  cases v
  simp_all

private theorem target_endpoints_ne (S : Finset (CollisionWitness P Q)) (i : S) :
    witnessFamilyTarget S (i, false) ≠ witnessFamilyTarget S (i, true) := by
  cases h : i.1.flipped <;>
    simp [witnessFamilyTarget, CollisionWitness.prescribedTarget, h,
      ne_of_lt i.1.right.fst_lt_snd, (ne_of_lt i.1.right.fst_lt_snd).symm]

private theorem target_endpoints_same_block
    (S : Finset (CollisionWitness P Q)) (i : S) :
    Q.block (witnessFamilyTarget S (i, false)) =
      Q.block (witnessFamilyTarget S (i, true)) := by
  cases h : i.1.flipped
  · simpa [witnessFamilyTarget, CollisionWitness.prescribedTarget, h] using
      i.1.right.same_block
  · simpa [witnessFamilyTarget, CollisionWitness.prescribedTarget, h] using
      i.1.right.same_block.symm

theorem two_mul_card_sourceBlocks_le_sources
    (S : Finset (CollisionWitness P Q)) :
    2 * (witnessFamilySourceBlocks S).card ≤
      (witnessFamilySources S).card := by
  classical
  simpa [witnessFamilySourceBlocks, witnessFamilySources, endpointSupport] using
    two_mul_card_usedBlockLabels_le_endpointSupport P.block
      (witnessFamilySource S) (source_endpoints_ne S)
      (source_endpoints_same_block S)

theorem two_mul_card_targetBlocks_le_targets
    (S : Finset (CollisionWitness P Q)) :
    2 * (witnessFamilyTargetBlocks S).card ≤
      (witnessFamilyTargets S).card := by
  classical
  simpa [witnessFamilyTargetBlocks, witnessFamilyTargets, endpointSupport] using
    two_mul_card_usedBlockLabels_le_endpointSupport Q.block
      (witnessFamilyTarget S) (target_endpoints_ne S)
      (target_endpoints_same_block S)

/-- The occupied source block containing the left pair of a family member. -/
def sourceBlockOfMember (S : Finset (CollisionWitness P Q)) (w : S) :
    witnessFamilySourceBlocks S :=
  ⟨P.block w.1.left.fst, by
    exact Finset.mem_image.mpr ⟨(w, false), Finset.mem_univ _, rfl⟩⟩

private def sourceEndpointInSupport
    (S : Finset (CollisionWitness P Q)) (w : S) (b : Bool) :
    endpointSupport (witnessFamilySource S) :=
  ⟨witnessFamilySource S (w, b),
    Finset.mem_image.mpr ⟨(w, b), Finset.mem_univ _, rfl⟩⟩

/-- If a compatible `k`-family has fewer than `2k` source vertices, its
occupied source-block count has a strict factor-two deficit. -/
theorem two_mul_card_sourceBlocks_lt_of_compatible
    (S : Finset (CollisionWitness P Q)) (sigma : Sym n)
    (hsigma : WitnessFamilyHolds S sigma) (hcard : S.card = k)
    (hsupport : (witnessFamilySources S).card < 2 * k) :
    2 * (witnessFamilySourceBlocks S).card <
      (witnessFamilySources S).card := by
  classical
  have hle := two_mul_card_sourceBlocks_le_sources S
  apply lt_of_le_of_ne hle
  intro heq
  let e := usedBlocksBoolEmbedding P.block (witnessFamilySource S)
    (source_endpoints_ne S) (source_endpoints_same_block S)
  have heCard : Fintype.card (witnessFamilySourceBlocks S × Bool) =
      Fintype.card (endpointSupport (witnessFamilySource S)) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe]
    rw [mul_comm]
    simpa [witnessFamilySources, endpointSupport] using heq
  have heSurj : Function.Surjective e :=
    ((Fintype.bijective_iff_injective_and_card e).mpr
      ⟨e.injective, heCard⟩).2
  have left_eq_representative (w : S) :
      w.1.left =
        (representativeIndex P.block (witnessFamilySource S)
          (sourceBlockOfMember S w)).1.left := by
    obtain ⟨a0, ha0⟩ := heSurj (sourceEndpointInSupport S w false)
    obtain ⟨a1, ha1⟩ := heSurj (sourceEndpointInSupport S w true)
    have hlabel0 : a0.1 = sourceBlockOfMember S w := by
      apply Subtype.ext
      have hb := congrArg
        (fun x : endpointSupport (witnessFamilySource S) => P.block x.1) ha0
      change P.block (witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S) a0.1, a0.2)) =
        P.block (witnessFamilySource S (w, false)) at hb
      calc
        a0.1.1 = P.block (witnessFamilySource S
            (representativeIndex P.block (witnessFamilySource S) a0.1, a0.2)) :=
          (block_representativeIndex P.block (witnessFamilySource S)
            (source_endpoints_same_block S) a0.1 a0.2).symm
        _ = P.block (witnessFamilySource S (w, false)) := hb
        _ = P.block w.1.left.fst := rfl
    have hlabel1 : a1.1 = sourceBlockOfMember S w := by
      apply Subtype.ext
      have hb := congrArg
        (fun x : endpointSupport (witnessFamilySource S) => P.block x.1) ha1
      change P.block (witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S) a1.1, a1.2)) =
        P.block (witnessFamilySource S (w, true)) at hb
      calc
        a1.1.1 = P.block (witnessFamilySource S
            (representativeIndex P.block (witnessFamilySource S) a1.1, a1.2)) :=
          (block_representativeIndex P.block (witnessFamilySource S)
            (source_endpoints_same_block S) a1.1 a1.2).symm
        _ = P.block (witnessFamilySource S (w, true)) := hb
        _ = P.block w.1.left.fst := w.1.left.same_block.symm
    have hv0 := congrArg Subtype.val ha0
    have hv1 := congrArg Subtype.val ha1
    change witnessFamilySource S
        (representativeIndex P.block (witnessFamilySource S) a0.1, a0.2) =
      witnessFamilySource S (w, false) at hv0
    change witnessFamilySource S
        (representativeIndex P.block (witnessFamilySource S) a1.1, a1.2) =
      witnessFamilySource S (w, true) at hv1
    rw [hlabel0] at hv0
    rw [hlabel1] at hv1
    cases h0 : a0.2 <;> cases h1 : a1.2
    · exfalso
      have hv0' : witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S)
            (sourceBlockOfMember S w), false) =
          witnessFamilySource S (w, false) := by simpa [h0] using hv0
      have hv1' : witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S)
            (sourceBlockOfMember S w), false) =
          witnessFamilySource S (w, true) := by simpa [h1] using hv1
      exact (source_endpoints_ne S w)
        (hv0'.symm.trans hv1')
    · exact pairIn_eq_of_endpoints_eq _ _
        (by simpa [h0, h1, witnessFamilySource,
          CollisionWitness.prescribedSource] using hv0.symm)
        (by simpa [h0, h1, witnessFamilySource,
          CollisionWitness.prescribedSource] using hv1.symm)
    · exfalso
      have hfirst := w.1.left.fst_lt_snd
      have hsecond := (representativeIndex P.block (witnessFamilySource S)
        (sourceBlockOfMember S w)).1.left.fst_lt_snd
      simp only [witnessFamilySource, CollisionWitness.prescribedSource, h0, h1] at hv0 hv1
      omega
    · exfalso
      have hv0' : witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S)
            (sourceBlockOfMember S w), true) =
          witnessFamilySource S (w, false) := by simpa [h0] using hv0
      have hv1' : witnessFamilySource S
          (representativeIndex P.block (witnessFamilySource S)
            (sourceBlockOfMember S w), true) =
          witnessFamilySource S (w, true) := by simpa [h1] using hv1
      exact (source_endpoints_ne S w)
        (hv0'.symm.trans hv1')
  have hblockInjective : Function.Injective (sourceBlockOfMember S) := by
    intro w v hwv
    have hrep := congrArg
      (representativeIndex P.block (witnessFamilySource S)) hwv
    have hleftrep := congrArg (fun z : S => z.1.left) hrep
    apply Subtype.ext
    apply CollisionWitness.eq_of_left_eq_of_holds
      ((left_eq_representative w).trans
        (hleftrep.trans (left_eq_representative v).symm))
      (hsigma w.1 w.2) (hsigma v.1 v.2)
  have hk_le_blocks : k ≤ (witnessFamilySourceBlocks S).card := by
    have hc := Fintype.card_le_of_injective (sourceBlockOfMember S) hblockInjective
    simpa [hcard] using hc
  omega

end WitnessEndpoints

end Kourovka213

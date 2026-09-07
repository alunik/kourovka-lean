import Kourovka.Problems.P21_03.Proof.WeightedCanonicalLLL
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.EndpointDegree

/-!
# Canonical core events for two bounded partitions

A collision witness is a two-edge canonical partial matching.  This file
identifies avoidance of all such events with simplicity of the corresponding
Young-configuration table, and proves the two local degree estimates used by
the conditioned canonical-event bounds.
-/

namespace Kourovka213

namespace CollisionWitness

variable {n : Nat} {P Q : BoundedPartition n}

noncomputable instance (P Q : BoundedPartition n) :
    DecidableEq (CollisionWitness P Q) := Classical.decEq _

private theorem prescribedSource_injective (w : CollisionWitness P Q) :
    Function.Injective w.prescribedSource := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact False.elim ((ne_of_lt w.left.fst_lt_snd) h)
  · exact False.elim ((ne_of_lt w.left.fst_lt_snd) h.symm)
  · rfl

private theorem prescribedTarget_injective (w : CollisionWitness P Q) :
    Function.Injective w.prescribedTarget := by
  intro b c h
  cases b <;> cases c
  · rfl
  · cases hf : w.flipped <;>
      simp only [prescribedTarget, hf, ↓reduceIte] at h
    · exact False.elim ((ne_of_lt w.right.fst_lt_snd) h)
    · exact False.elim ((ne_of_lt w.right.fst_lt_snd) h.symm)
  · cases hf : w.flipped <;>
      simp only [prescribedTarget, hf, ↓reduceIte] at h
    · exact False.elim ((ne_of_lt w.right.fst_lt_snd) h.symm)
    · exact False.elim ((ne_of_lt w.right.fst_lt_snd) h)
  · rfl

/-- The two-edge canonical matching encoded by a collision witness. -/
def canonicalMatching (w : CollisionWitness P Q) :
    CanonicalPartialMatching (Fin n) where
  size := 2
  source := finTwoEquiv.toEmbedding.trans
    ⟨w.prescribedSource, prescribedSource_injective w⟩
  target := finTwoEquiv.toEmbedding.trans
    ⟨w.prescribedTarget, prescribedTarget_injective w⟩

@[simp]
theorem canonicalMatching_size (w : CollisionWitness P Q) :
    w.canonicalMatching.size = 2 := rfl

@[simp]
theorem canonicalMatching_source (w : CollisionWitness P Q) (k : Fin 2) :
    w.canonicalMatching.source k = w.prescribedSource (finTwoEquiv k) := rfl

@[simp]
theorem canonicalMatching_target (w : CollisionWitness P Q) (k : Fin 2) :
    w.canonicalMatching.target k = w.prescribedTarget (finTwoEquiv k) := rfl

theorem canonicalMatching_holds_iff (w : CollisionWitness P Q)
    (sigma : Sym n) :
    w.canonicalMatching.Holds sigma ↔ w.Holds sigma := by
  rw [holds_iff_forall_orientation]
  constructor
  · intro h b
    have hb := h (finTwoEquiv.symm b)
    change sigma (w.prescribedSource (finTwoEquiv (finTwoEquiv.symm b))) =
      w.prescribedTarget (finTwoEquiv (finTwoEquiv.symm b)) at hb
    simpa using hb
  · intro h k
    change sigma (w.prescribedSource (finTwoEquiv k)) =
      w.prescribedTarget (finTwoEquiv k)
    exact h (finTwoEquiv k)

@[simp]
theorem mem_canonicalMatching_event (w : CollisionWitness P Q)
    (sigma : Sym n) :
    sigma ∈ w.canonicalMatching.event ↔ w.Holds sigma := by
  rw [CanonicalPartialMatching.mem_event, canonicalMatching_holds_iff]

end CollisionWitness

/-- The canonical two-point core-event family attached to two bounded
partitions. -/
def coreCanonicalFamily (P Q : BoundedPartition n) :
    CollisionWitness P Q → CanonicalPartialMatching (Fin n) :=
  CollisionWitness.canonicalMatching

@[simp]
theorem coreCanonicalFamily_size (P Q : BoundedPartition n)
    (w : CollisionWitness P Q) :
    (coreCanonicalFamily P Q w).size = 2 := rfl

/-- Avoiding every canonical collision event is exactly the simplicity
condition. -/
theorem mem_avoid_coreCanonicalFamily_iff_isSimple
    (P Q : BoundedPartition n) (sigma : Sym n) :
    sigma ∈ avoidEvents (fun w => (coreCanonicalFamily P Q w).event) Finset.univ ↔
      IsSimple P Q sigma := by
  classical
  rw [mem_avoidEvents, isSimple_iff_collisionCount_eq_zero]
  simp only [Finset.mem_univ, true_implies, CanonicalPartialMatching.mem_event]
  rw [collisionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies]
  constructor
  · intro h w hw
    exact h w ((CollisionWitness.canonicalMatching_holds_iff w sigma).mpr hw)
  · intro h w hw
    exact h ((CollisionWitness.canonicalMatching_holds_iff w sigma).mp hw)

/-- The finite set of permutations producing a simple table. -/
noncomputable def simplePermutations (P Q : BoundedPartition n) :
    Finset (Sym n) := by
  classical
  exact Finset.univ.filter (IsSimple P Q)

/-- Finset form of the identification of the core-conditioned sample space
with the simple permutations. -/
theorem avoid_coreCanonicalFamily_eq_simplePermutations
    (P Q : BoundedPartition n) :
    avoidEvents (fun w => (coreCanonicalFamily P Q w).event) Finset.univ =
      simplePermutations P Q := by
  classical
  ext sigma
  rw [mem_avoid_coreCanonicalFamily_iff_isSimple]
  simp [simplePermutations]

namespace BoundedPartition.PairIn

variable {n : Nat} {P : BoundedPartition n}

noncomputable instance (P : BoundedPartition n) : DecidableEq P.PairIn :=
  Classical.decEq _

/-- A within-block pair is incident with a point when the point is one of its
two endpoints. -/
def Incident (u : P.PairIn) (x : Fin n) : Prop :=
  u.fst = x ∨ u.snd = x

noncomputable instance (u : P.PairIn) (x : Fin n) : Decidable (u.Incident x) :=
  by classical infer_instance

/-- Two within-block pairs share an endpoint. -/
def Shares (u v : P.PairIn) : Prop :=
  ∃ x, u.Incident x ∧ v.Incident x

noncomputable instance (u v : P.PairIn) : Decidable (u.Shares v) :=
  by classical infer_instance

theorem incident_fst (u : P.PairIn) : u.Incident u.fst := Or.inl rfl

theorem incident_snd (u : P.PairIn) : u.Incident u.snd := Or.inr rfl

theorem shares_refl (u : P.PairIn) : u.Shares u :=
  ⟨u.fst, u.incident_fst, u.incident_fst⟩

theorem shares_symm {u v : P.PairIn} (h : u.Shares v) : v.Shares u := by
  rcases h with ⟨x, hu, hv⟩
  exact ⟨x, hv, hu⟩

theorem shares_iff_incident_fst_or_snd (u v : P.PairIn) :
    u.Shares v ↔ v.Incident u.fst ∨ v.Incident u.snd := by
  constructor
  · rintro ⟨x, hu, hv⟩
    rcases hu with h | h
    · exact Or.inl (h ▸ hv)
    · exact Or.inr (h ▸ hv)
  · rintro (h | h)
    · exact ⟨u.fst, u.incident_fst, h⟩
    · exact ⟨u.snd, u.incident_snd, h⟩

private def incidentOtherEmbedding (P : BoundedPartition n) (x : Fin n) :
    {u : P.PairIn // u.Incident x} ↪ P.OtherInBlock x where
  toFun u := if h : u.1.fst = x then
      ⟨u.1.snd, by
        constructor
        · intro hs
          exact (ne_of_lt u.1.fst_lt_snd) (h.trans hs.symm)
        · exact u.1.same_block.symm.trans (congrArg P.block h)⟩
    else
      ⟨u.1.fst, by
        have hs : u.1.snd = x := u.2.resolve_left h
        constructor
        · exact h
        · exact u.1.same_block.trans (congrArg P.block hs)⟩
  inj' := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    apply Subtype.ext
    by_cases huf : u.fst = x
    · by_cases hvf : v.fst = x
      · have hsnd : u.snd = v.snd := by
          simpa [huf, hvf] using congrArg Subtype.val huv
        cases u
        cases v
        simp_all
      · have hvs : v.snd = x := hv.resolve_left hvf
        have hcross : u.snd = v.fst := by
          simpa [huf, hvf] using congrArg Subtype.val huv
        have hu_lt : x < u.snd := huf ▸ u.fst_lt_snd
        have hv_lt : v.fst < x := hvs ▸ v.fst_lt_snd
        omega
    · have hus : u.snd = x := hu.resolve_left huf
      by_cases hvf : v.fst = x
      · have hcross : u.fst = v.snd := by
          simpa [huf, hvf] using congrArg Subtype.val huv
        have hu_lt : u.fst < x := hus ▸ u.fst_lt_snd
        have hv_lt : x < v.snd := hvf ▸ v.fst_lt_snd
        omega
      · have hsnd : u.fst = v.fst := by
          simpa [huf, hvf] using congrArg Subtype.val huv
        have hvs : v.snd = x := hv.resolve_left hvf
        cases u
        cases v
        simp_all

/-- At most three within-block pairs are incident with a fixed point. -/
theorem card_incident_le_three (P : BoundedPartition n) (x : Fin n) :
    Fintype.card {u : P.PairIn // u.Incident x} ≤ 3 := by
  exact (Fintype.card_le_of_injective (incidentOtherEmbedding P x)
    (incidentOtherEmbedding P x).injective).trans
      (P.card_otherInBlock_le_three x)

private abbrev sharingTarget (u : P.PairIn) :=
  {v : P.PairIn // v.Incident u.fst} ⊕
    {v : {v : P.PairIn // v.Incident u.snd} // v.1 ≠ u}

private def sharingTargetForget (u : P.PairIn) : sharingTarget u → P.PairIn
  | Sum.inl v => v.1
  | Sum.inr v => v.1.1

private noncomputable def sharingEmbedding (u : P.PairIn) :
    {v : P.PairIn // u.Shares v} ↪ sharingTarget u where
  toFun v := if h : v.1.Incident u.fst then
      Sum.inl ⟨v.1, h⟩
    else
      Sum.inr ⟨⟨v.1,
        (shares_iff_incident_fst_or_snd u v.1).mp v.2 |>.resolve_left h⟩,
        fun hvu => h (hvu.symm ▸ u.incident_fst)⟩
  inj' := by
    intro v w hvw
    apply Subtype.ext
    have hval := congrArg (sharingTargetForget u) hvw
    by_cases hv : v.1.Incident u.fst <;>
      by_cases hw : w.1.Incident u.fst <;>
      simp [sharingTargetForget, hv, hw] at hval
    all_goals exact hval

/-- At most five within-block pairs share an endpoint with a fixed pair. -/
theorem card_sharing_le_five (u : P.PairIn) :
    Fintype.card {v : P.PairIn // u.Shares v} ≤ 5 := by
  have hinj := Fintype.card_le_of_injective (sharingEmbedding u)
    (sharingEmbedding u).injective
  have hfst := card_incident_le_three P u.fst
  have hsnd := card_incident_le_three P u.snd
  have hone :
      Fintype.card
        {v : {v : P.PairIn // v.Incident u.snd} // v.1 = u} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨u, u.incident_snd⟩, rfl⟩, ?_⟩
    intro v
    apply Subtype.ext
    apply Subtype.ext
    exact v.2
  have hcompl :
      Fintype.card {v : {v : P.PairIn // v.Incident u.snd} // v.1 ≠ u} =
        Fintype.card {v : P.PairIn // v.Incident u.snd} - 1 := by
    rw [Fintype.card_subtype_compl (fun v : {v : P.PairIn // v.Incident u.snd} =>
      v.1 = u)]
    rw [hone]
  simp only [sharingTarget, Fintype.card_sum, hcompl] at hinj
  omega

end BoundedPartition.PairIn

namespace CollisionWitness

variable {n : Nat} {P Q : BoundedPartition n}

theorem left_incident_prescribedSource (w : CollisionWitness P Q) (b : Bool) :
    w.left.Incident (w.prescribedSource b) := by
  cases b <;> simp [BoundedPartition.PairIn.Incident, prescribedSource]

theorem right_incident_prescribedTarget (w : CollisionWitness P Q) (b : Bool) :
    w.right.Incident (w.prescribedTarget b) := by
  cases b <;> cases hf : w.flipped <;>
    simp [BoundedPartition.PairIn.Incident, prescribedTarget, hf]

private def leftIncidentWitnessEmbedding (P Q : BoundedPartition n) (x : Fin n) :
    {w : CollisionWitness P Q // w.left.Incident x} ↪
      ({u : P.PairIn // u.Incident x} × Q.PairIn) × Bool where
  toFun w := ((⟨w.1.left, w.2⟩, w.1.right), w.1.flipped)
  inj' := by
    intro u v h
    apply Subtype.ext
    cases u with
    | mk u hu =>
      cases v with
      | mk v hv =>
        cases u
        cases v
        simp_all

private def rightIncidentWitnessEmbedding (P Q : BoundedPartition n) (x : Fin n) :
    {w : CollisionWitness P Q // w.right.Incident x} ↪
      ({u : Q.PairIn // u.Incident x} × P.PairIn) × Bool where
  toFun w := ((⟨w.1.right, w.2⟩, w.1.left), w.1.flipped)
  inj' := by
    intro u v h
    apply Subtype.ext
    cases u with
    | mk u hu =>
      cases v with
      | mk v hv =>
        cases u
        cases v
        simp_all

/-- Ignoring orientation, at most `9n` collision witnesses use a fixed
source point. -/
theorem card_left_incident_le_nine_mul (P Q : BoundedPartition n) (x : Fin n) :
    Fintype.card {w : CollisionWitness P Q // w.left.Incident x} ≤ 9 * n := by
  have hinj := Fintype.card_le_of_injective (leftIncidentWitnessEmbedding P Q x)
    (leftIncidentWitnessEmbedding P Q x).injective
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  have hincident := BoundedPartition.PairIn.card_incident_le_three P x
  have hpairs := Q.two_mul_card_pairIn_le_three_mul
  calc
    Fintype.card {w : CollisionWitness P Q // w.left.Incident x} ≤
        Fintype.card {u : P.PairIn // u.Incident x} * Fintype.card Q.PairIn * 2 := hinj
    _ = Fintype.card {u : P.PairIn // u.Incident x} *
        (2 * Fintype.card Q.PairIn) := by ring
    _ ≤ 3 * (3 * n) := Nat.mul_le_mul hincident hpairs
    _ = 9 * n := by ring

/-- Ignoring orientation, at most `9n` collision witnesses use a fixed
target point. -/
theorem card_right_incident_le_nine_mul (P Q : BoundedPartition n) (x : Fin n) :
    Fintype.card {w : CollisionWitness P Q // w.right.Incident x} ≤ 9 * n := by
  have hinj := Fintype.card_le_of_injective (rightIncidentWitnessEmbedding P Q x)
    (rightIncidentWitnessEmbedding P Q x).injective
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  have hincident := BoundedPartition.PairIn.card_incident_le_three Q x
  have hpairs := P.two_mul_card_pairIn_le_three_mul
  calc
    Fintype.card {w : CollisionWitness P Q // w.right.Incident x} ≤
        Fintype.card {u : Q.PairIn // u.Incident x} * Fintype.card P.PairIn * 2 := hinj
    _ = Fintype.card {u : Q.PairIn // u.Incident x} *
        (2 * Fintype.card P.PairIn) := by ring
    _ ≤ 3 * (3 * n) := Nat.mul_le_mul hincident hpairs
    _ = 9 * n := by ring

private def leftSharingWitnessEmbedding (u : P.PairIn) :
    {w : CollisionWitness P Q // u.Shares w.left} ↪
      ({v : P.PairIn // u.Shares v} × Q.PairIn) × Bool where
  toFun w := ((⟨w.1.left, w.2⟩, w.1.right), w.1.flipped)
  inj' := by
    intro v w h
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases w with
      | mk w hw =>
        cases v
        cases w
        simp_all

private def rightSharingWitnessEmbedding (u : Q.PairIn) :
    {w : CollisionWitness P Q // u.Shares w.right} ↪
      ({v : Q.PairIn // u.Shares v} × P.PairIn) × Bool where
  toFun w := ((⟨w.1.right, w.2⟩, w.1.left), w.1.flipped)
  inj' := by
    intro v w h
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases w with
      | mk w hw =>
        cases v
        cases w
        simp_all

theorem card_left_sharing_le_fifteen_mul (u : P.PairIn) :
    Fintype.card {w : CollisionWitness P Q // u.Shares w.left} ≤ 15 * n := by
  have hinj := Fintype.card_le_of_injective (leftSharingWitnessEmbedding (Q := Q) u)
    (leftSharingWitnessEmbedding (Q := Q) u).injective
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  have hsharing := BoundedPartition.PairIn.card_sharing_le_five u
  have hpairs := Q.two_mul_card_pairIn_le_three_mul
  calc
    Fintype.card {w : CollisionWitness P Q // u.Shares w.left} ≤
        Fintype.card {v : P.PairIn // u.Shares v} * Fintype.card Q.PairIn * 2 := hinj
    _ = Fintype.card {v : P.PairIn // u.Shares v} *
        (2 * Fintype.card Q.PairIn) := by ring
    _ ≤ 5 * (3 * n) := Nat.mul_le_mul hsharing hpairs
    _ = 15 * n := by ring

theorem card_right_sharing_le_fifteen_mul (u : Q.PairIn) :
    Fintype.card {w : CollisionWitness P Q // u.Shares w.right} ≤ 15 * n := by
  have hinj := Fintype.card_le_of_injective (rightSharingWitnessEmbedding (P := P) u)
    (rightSharingWitnessEmbedding (P := P) u).injective
  simp only [Fintype.card_prod, Fintype.card_bool] at hinj
  have hsharing := BoundedPartition.PairIn.card_sharing_le_five u
  have hpairs := P.two_mul_card_pairIn_le_three_mul
  calc
    Fintype.card {w : CollisionWitness P Q // u.Shares w.right} ≤
        Fintype.card {v : Q.PairIn // u.Shares v} * Fintype.card P.PairIn * 2 := hinj
    _ = Fintype.card {v : Q.PairIn // u.Shares v} *
        (2 * Fintype.card P.PairIn) := by ring
    _ ≤ 5 * (3 * n) := Nat.mul_le_mul hsharing hpairs
    _ = 15 * n := by ring

end CollisionWitness

namespace CollisionWitness

variable {n : Nat} {P Q : BoundedPartition n}

/-- Witnesses whose left pair shares an endpoint with `u`. -/
noncomputable def leftSharingSet (u : P.PairIn) :
    Finset (CollisionWitness P Q) := by
  classical
  exact Finset.univ.filter fun w => u.Shares w.left

/-- Witnesses whose right pair shares an endpoint with `u`. -/
noncomputable def rightSharingSet (u : Q.PairIn) :
    Finset (CollisionWitness P Q) := by
  classical
  exact Finset.univ.filter fun w => u.Shares w.right

@[simp]
theorem mem_leftSharingSet {u : P.PairIn} {w : CollisionWitness P Q} :
    w ∈ leftSharingSet (Q := Q) u ↔ u.Shares w.left := by
  classical
  simp [leftSharingSet]

@[simp]
theorem mem_rightSharingSet {u : Q.PairIn} {w : CollisionWitness P Q} :
    w ∈ rightSharingSet (P := P) u ↔ u.Shares w.right := by
  classical
  simp [rightSharingSet]

theorem card_leftSharingSet_le_fifteen_mul (u : P.PairIn) :
    (leftSharingSet (Q := Q) u).card ≤ 15 * n := by
  classical
  rw [leftSharingSet, ← Fintype.card_subtype]
  exact card_left_sharing_le_fifteen_mul (Q := Q) u

theorem card_rightSharingSet_le_fifteen_mul (u : Q.PairIn) :
    (rightSharingSet (P := P) u).card ≤ 15 * n := by
  classical
  rw [rightSharingSet, ← Fintype.card_subtype]
  exact card_right_sharing_le_fifteen_mul (P := P) u

/-- Witnesses whose left pair uses the point `x`. -/
noncomputable def leftIncidentSet (P Q : BoundedPartition n) (x : Fin n) :
    Finset (CollisionWitness P Q) := by
  classical
  exact Finset.univ.filter fun w => w.left.Incident x

/-- Witnesses whose right pair uses the point `x`. -/
noncomputable def rightIncidentSet (P Q : BoundedPartition n) (x : Fin n) :
    Finset (CollisionWitness P Q) := by
  classical
  exact Finset.univ.filter fun w => w.right.Incident x

@[simp]
theorem mem_leftIncidentSet {x : Fin n} {w : CollisionWitness P Q} :
    w ∈ leftIncidentSet P Q x ↔ w.left.Incident x := by
  classical
  simp [leftIncidentSet]

@[simp]
theorem mem_rightIncidentSet {x : Fin n} {w : CollisionWitness P Q} :
    w ∈ rightIncidentSet P Q x ↔ w.right.Incident x := by
  classical
  simp [rightIncidentSet]

theorem card_leftIncidentSet_le_nine_mul (P Q : BoundedPartition n) (x : Fin n) :
    (leftIncidentSet P Q x).card ≤ 9 * n := by
  classical
  rw [leftIncidentSet, ← Fintype.card_subtype]
  exact card_left_incident_le_nine_mul P Q x

theorem card_rightIncidentSet_le_nine_mul (P Q : BoundedPartition n) (x : Fin n) :
    (rightIncidentSet P Q x).card ≤ 9 * n := by
  classical
  rw [rightIncidentSet, ← Fintype.card_subtype]
  exact card_right_incident_le_nine_mul P Q x

/-- A broad conflict between two core matchings forces their left pairs or
their right pairs to share an endpoint. -/
theorem shares_left_or_right_of_canonicalMatching_conflicts
    {u v : CollisionWitness P Q}
    (h : u.canonicalMatching.Conflicts v.canonicalMatching) :
    u.left.Shares v.left ∨ u.right.Shares v.right := by
  rcases h with ⟨k, l, hkl⟩ | ⟨k, l, hkl⟩
  · left
    have hsource :
        u.prescribedSource (finTwoEquiv k) =
          v.prescribedSource (finTwoEquiv l) := by
      change u.prescribedSource (finTwoEquiv k) =
        v.prescribedSource (finTwoEquiv l) at hkl
      exact hkl
    exact ⟨u.prescribedSource (finTwoEquiv k),
      u.left_incident_prescribedSource (finTwoEquiv k),
      hsource.symm ▸ v.left_incident_prescribedSource (finTwoEquiv l)⟩
  · right
    have htarget :
        u.prescribedTarget (finTwoEquiv k) =
          v.prescribedTarget (finTwoEquiv l) := by
      change u.prescribedTarget (finTwoEquiv k) =
        v.prescribedTarget (finTwoEquiv l) at hkl
      exact hkl
    exact ⟨u.prescribedTarget (finTwoEquiv k),
      u.right_incident_prescribedTarget (finTwoEquiv k),
      htarget.symm ▸ v.right_incident_prescribedTarget (finTwoEquiv l)⟩

end CollisionWitness

/-- Every core neighborhood is covered by the witnesses sharing a left or a
right endpoint with its centre. -/
theorem coreCanonicalFamily_neighborhood_subset_sharing
    (P Q : BoundedPartition n) (u : CollisionWitness P Q) :
    CanonicalPartialMatching.neighborhood (coreCanonicalFamily P Q) u ⊆
      CollisionWitness.leftSharingSet (Q := Q) u.left ∪
        CollisionWitness.rightSharingSet (P := P) u.right := by
  classical
  intro v hv
  rw [CanonicalPartialMatching.mem_neighborhood] at hv
  rw [Finset.mem_union, CollisionWitness.mem_leftSharingSet,
    CollisionWitness.mem_rightSharingSet]
  rcases hv with rfl | hconflict
  · exact Or.inl u.left.shares_refl
  · exact CollisionWitness.shares_left_or_right_of_canonicalMatching_conflicts hconflict

/-- The canonical collision family has broad-conflict degree at most `30n`. -/
theorem coreCanonicalFamily_neighborhood_card_le
    (P Q : BoundedPartition n) (u : CollisionWitness P Q) :
    (CanonicalPartialMatching.neighborhood (coreCanonicalFamily P Q) u).card ≤
      30 * n := by
  classical
  calc
    (CanonicalPartialMatching.neighborhood (coreCanonicalFamily P Q) u).card ≤
        (CollisionWitness.leftSharingSet (Q := Q) u.left ∪
          CollisionWitness.rightSharingSet (P := P) u.right).card :=
      Finset.card_le_card (coreCanonicalFamily_neighborhood_subset_sharing P Q u)
    _ ≤ (CollisionWitness.leftSharingSet (Q := Q) u.left).card +
        (CollisionWitness.rightSharingSet (P := P) u.right).card :=
      Finset.card_union_le _ _
    _ ≤ 15 * n + 15 * n := Nat.add_le_add
      (CollisionWitness.card_leftSharingSet_le_fifteen_mul (Q := Q) u.left)
      (CollisionWitness.card_rightSharingSet_le_fifteen_mul (P := P) u.right)
    _ = 30 * n := by ring

/-- Core witnesses covered by the source or target endpoints of an external
canonical matching. -/
noncomputable def externalCoreConflictCover (P Q : BoundedPartition n)
    (c : CanonicalPartialMatching (Fin n)) : Finset (CollisionWitness P Q) := by
  classical
  exact
    ((Finset.univ : Finset (Fin c.size)).biUnion fun k =>
        CollisionWitness.leftIncidentSet P Q (c.source k)) ∪
      ((Finset.univ : Finset (Fin c.size)).biUnion fun k =>
        CollisionWitness.rightIncidentSet P Q (c.target k))

/-- Every core event broadly conflicting with `c` lies in the endpoint cover. -/
theorem conflictSet_coreCanonicalFamily_subset_externalCoreConflictCover
    (P Q : BoundedPartition n) (c : CanonicalPartialMatching (Fin n)) :
    CanonicalPartialMatching.conflictSet (coreCanonicalFamily P Q) c ⊆
      externalCoreConflictCover P Q c := by
  classical
  intro w hw
  rw [CanonicalPartialMatching.mem_conflictSet] at hw
  rcases hw with ⟨k, l, hkl⟩ | ⟨k, l, hkl⟩
  · rw [externalCoreConflictCover, Finset.mem_union]
    left
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_univ k, ?_⟩
    rw [CollisionWitness.mem_leftIncidentSet]
    have hsource : c.source k = w.prescribedSource (finTwoEquiv l) := by
      change c.source k = w.prescribedSource (finTwoEquiv l) at hkl
      exact hkl
    exact hsource ▸ w.left_incident_prescribedSource (finTwoEquiv l)
  · rw [externalCoreConflictCover, Finset.mem_union]
    right
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_univ k, ?_⟩
    rw [CollisionWitness.mem_rightIncidentSet]
    have htarget : c.target k = w.prescribedTarget (finTwoEquiv l) := by
      change c.target k = w.prescribedTarget (finTwoEquiv l) at hkl
      exact hkl
    exact htarget ▸ w.right_incident_prescribedTarget (finTwoEquiv l)

/-- At most `18 n s` core events broadly conflict with an external canonical
event of size `s`. -/
theorem conflictSet_coreCanonicalFamily_card_le
    (P Q : BoundedPartition n) (c : CanonicalPartialMatching (Fin n)) :
    (CanonicalPartialMatching.conflictSet (coreCanonicalFamily P Q) c).card ≤
      18 * n * c.size := by
  classical
  let L := (Finset.univ : Finset (Fin c.size)).biUnion fun k =>
    CollisionWitness.leftIncidentSet P Q (c.source k)
  let R := (Finset.univ : Finset (Fin c.size)).biUnion fun k =>
    CollisionWitness.rightIncidentSet P Q (c.target k)
  have hL : L.card ≤ c.size * (9 * n) := by
    calc
      L.card ≤ ∑ k ∈ (Finset.univ : Finset (Fin c.size)),
          (CollisionWitness.leftIncidentSet P Q (c.source k)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin c.size)), 9 * n := by
        apply Finset.sum_le_sum
        intro k _hk
        exact CollisionWitness.card_leftIncidentSet_le_nine_mul P Q (c.source k)
      _ = c.size * (9 * n) := by simp
  have hR : R.card ≤ c.size * (9 * n) := by
    calc
      R.card ≤ ∑ k ∈ (Finset.univ : Finset (Fin c.size)),
          (CollisionWitness.rightIncidentSet P Q (c.target k)).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _k ∈ (Finset.univ : Finset (Fin c.size)), 9 * n := by
        apply Finset.sum_le_sum
        intro k _hk
        exact CollisionWitness.card_rightIncidentSet_le_nine_mul P Q (c.target k)
      _ = c.size * (9 * n) := by simp
  calc
    (CanonicalPartialMatching.conflictSet (coreCanonicalFamily P Q) c).card ≤
        (externalCoreConflictCover P Q c).card :=
      Finset.card_le_card
        (conflictSet_coreCanonicalFamily_subset_externalCoreConflictCover P Q c)
    _ = (L ∪ R).card := by rfl
    _ ≤ L.card + R.card := Finset.card_union_le _ _
    _ ≤ c.size * (9 * n) + c.size * (9 * n) := Nat.add_le_add hL hR
    _ = 18 * n * c.size := by ring

/-- The real conditioned-event bound specialized to the canonical core
family of two bounded partitions. -/
theorem conditioned_external_event_relative_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (c : CanonicalPartialMatching (Fin n)) :
    (2 / 3 : Real) ^ c.size *
        ((c.event ∩ avoidEvents
          (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card : Real) ≤
      (1 / c.denominator) *
        ((avoidEvents
          (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card : Real) := by
  apply CanonicalPartialMatching.conditioned_external_event_relative_bound
    (coreCanonicalFamily P Q) (by simpa using hn)
  · exact coreCanonicalFamily_size P Q
  · intro w
    simpa using coreCanonicalFamily_neighborhood_card_le P Q w
  · simpa using conflictSet_coreCanonicalFamily_card_le P Q c

/-- The denominator-cleared real conditioned-event bound specialized to the
canonical core family of two bounded partitions. -/
theorem conditioned_external_event_descFactorial_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (c : CanonicalPartialMatching (Fin n)) :
    c.denominator * (2 / 3 : Real) ^ c.size *
        ((c.event ∩ avoidEvents
          (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card : Real) ≤
      ((avoidEvents
        (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card : Real) := by
  simpa using CanonicalPartialMatching.conditioned_external_event_descFactorial_bound
    (coreCanonicalFamily P Q) (by simpa using hn)
    (coreCanonicalFamily_size P Q)
    (fun w => by simpa using coreCanonicalFamily_neighborhood_card_le P Q w)
    c (by simpa using conflictSet_coreCanonicalFamily_card_le P Q c)

/-- The integral conditioned-event bound specialized to the canonical core
family of two bounded partitions. -/
theorem conditioned_external_event_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (c : CanonicalPartialMatching (Fin n)) :
    n.descFactorial c.size * 2 ^ c.size *
        (c.event ∩ avoidEvents
          (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card ≤
      3 ^ c.size *
        (avoidEvents
          (fun w => (coreCanonicalFamily P Q w).event) Finset.univ).card := by
  simpa using CanonicalPartialMatching.conditioned_external_event_nat_bound
    (coreCanonicalFamily P Q) (by simpa using hn)
    (coreCanonicalFamily_size P Q)
    (fun w => by simpa using coreCanonicalFamily_neighborhood_card_le P Q w)
    c (by simpa using conflictSet_coreCanonicalFamily_card_le P Q c)

end Kourovka213

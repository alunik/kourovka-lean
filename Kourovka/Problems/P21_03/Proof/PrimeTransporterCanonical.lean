import Kourovka.Problems.P21_03.Proof.CoreCanonicalProbability
import Kourovka.Problems.P21_03.Proof.PrimeRowReduction

/-!
# Prime-row transporters as canonical support events

The relation `x * a * x⁻¹ = b` is determined by the restriction of `x` to
the support of `a`.  This module packages that restriction as a canonical
partial matching and removes the factorial coming from the arbitrary action
on fixed points before applying the conditioned core estimate.
-/

open Subgroup
open scoped BigOperators

namespace Kourovka213

variable {n : ℕ}

/-- A fixed enumeration of the moved points of a permutation. -/
noncomputable def supportSource (a : Sym n) : Fin a.support.card ↪ Fin n :=
  (Finset.equivFin a.support).symm.toEmbedding.trans
    (Function.Embedding.subtype fun i : Fin n ↦ i ∈ a.support)

@[simp]
theorem supportSource_mem (a : Sym n) (i : Fin a.support.card) :
    supportSource a i ∈ a.support :=
  ((Finset.equivFin a.support).symm i).2

/-- A canonical matching with the moved points of `a` as its source. -/
noncomputable def supportMatching (a : Sym n)
    (f : Fin a.support.card ↪ Fin n) : CanonicalPartialMatching (Fin n) where
  size := a.support.card
  source := supportSource a
  target := f

/-- The target embedding obtained by restricting a permutation to the moved
points of `a`. -/
noncomputable def supportTarget (a x : Sym n) : Fin a.support.card ↪ Fin n :=
  (supportSource a).trans x.toEmbedding

/-- The canonical event prescribing the restriction of `x` to the support
of `a`. -/
noncomputable def supportRestrictionEvent (a x : Sym n) :
    CanonicalPartialMatching (Fin n) :=
  supportMatching a (supportTarget a x)

@[simp]
theorem supportRestrictionEvent_size (a x : Sym n) :
    (supportRestrictionEvent a x).size = a.support.card := rfl

@[simp]
theorem supportMatching_size (a : Sym n)
    (f : Fin a.support.card ↪ Fin n) :
    (supportMatching a f).size = a.support.card := rfl

@[simp]
theorem mem_supportMatching_iff {a : Sym n}
    {f : Fin a.support.card ↪ Fin n} {y : Sym n} :
    y ∈ (supportMatching a f).event ↔
      ∀ k, y (supportSource a k) = f k := by
  classical
  exact CanonicalPartialMatching.mem_event

@[simp]
theorem mem_supportRestrictionEvent_iff {a x y : Sym n} :
    y ∈ (supportRestrictionEvent a x).event ↔
      ∀ i ∈ a.support, y i = x i := by
  classical
  rw [CanonicalPartialMatching.mem_event]
  constructor
  · intro h i hi
    let z : a.support := ⟨i, hi⟩
    let k : Fin a.support.card := Finset.equivFin a.support z
    have hk := h k
    change y (supportSource a k) = x (supportSource a k) at hk
    have hsource : supportSource a k = i := by
      simp [supportSource, k, z]
    simpa [hsource] using hk
  · intro h k
    exact h (supportSource a k) (supportSource_mem a k)

/-- Conjugating `a` to `b` depends only on the restriction to the support of
`a`: every completion of the same support matching is again a conjugator. -/
theorem supportRestrictionEvent_subset_conjugatingElements
    {a b x : Sym n} (hx : x ∈ conjugatingElements a b) :
    (supportRestrictionEvent a x).event ⊆ conjugatingElements a b := by
  classical
  intro y hy
  have hxy : ∀ i ∈ a.support, y i = x i :=
    mem_supportRestrictionEvent_iff.mp hy
  have hxconj : x * a * x⁻¹ = b := mem_conjugatingElements.mp hx
  have hsupportb : b.support = a.support.map x.toEmbedding := by
    rw [← hxconj, Equiv.Perm.support_conj]
  rw [mem_conjugatingElements, mul_inv_eq_iff_eq_mul]
  ext i
  by_cases hi : i ∈ a.support
  · have hai : a i ∈ a.support := Equiv.Perm.apply_mem_support.mpr hi
    have hrel := congrArg (fun z : Sym n ↦ z (x i)) hxconj
    exact congrArg Fin.val <| by
      simpa [Equiv.Perm.mul_apply, hxy i hi, hxy (a i) hai] using hrel
  · have hai : a i = i := Equiv.Perm.notMem_support.mp hi
    have hyNot : y i ∉ b.support := by
      rw [hsupportb]
      intro hyMem
      rw [Finset.mem_map] at hyMem
      obtain ⟨j, hj, hjy⟩ := hyMem
      have hjEq : y j = x j := hxy j hj
      have hyEq : y i = y j := hjy.symm.trans hjEq.symm
      have hij : i = j := y.injective hyEq
      exact hi (hij ▸ hj)
    simp [hai, Equiv.Perm.notMem_support.mp hyNot]

/-- The finite set of distinct support restrictions occurring in a
transporter. -/
noncomputable def transporterTargets (a b : Sym n) :
    Finset (Fin a.support.card ↪ Fin n) := by
  classical
  exact (conjugatingElements a b).image (supportTarget a)

@[simp]
theorem mem_transporterTargets {a b : Sym n}
    {f : Fin a.support.card ↪ Fin n} :
    f ∈ transporterTargets a b ↔
      ∃ x ∈ conjugatingElements a b, supportTarget a x = f := by
  classical
  simp [transporterTargets]

/-- A transporter is the union of the canonical events indexed by its
distinct support restrictions. -/
theorem conjugatingElements_eq_biUnion_supportMatching (a b : Sym n) :
    conjugatingElements a b =
      (transporterTargets a b).biUnion fun f ↦ (supportMatching a f).event := by
  classical
  ext y
  constructor
  · intro hy
    rw [Finset.mem_biUnion]
    refine ⟨supportTarget a y, ?_, ?_⟩
    · exact mem_transporterTargets.mpr ⟨y, hy, rfl⟩
    · rw [mem_supportMatching_iff]
      intro k
      rfl
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨f, hf, hyf⟩ := hy
    obtain ⟨x, hx, rfl⟩ := mem_transporterTargets.mp hf
    apply supportRestrictionEvent_subset_conjugatingElements hx
    simpa [supportRestrictionEvent] using hyf

/-- Distinct target restrictions give disjoint canonical events. -/
theorem supportMatching_pairwiseDisjoint (a b : Sym n) :
    ((transporterTargets a b : Finset (Fin a.support.card ↪ Fin n)) :
      Set (Fin a.support.card ↪ Fin n)).PairwiseDisjoint
        (fun f ↦ (supportMatching a f).event) := by
  classical
  intro f _hf g _hg hfg
  change Disjoint ((supportMatching a f).event) ((supportMatching a g).event)
  rw [Finset.disjoint_left]
  intro y hyf hyg
  apply hfg
  apply Function.Embedding.ext
  intro k
  exact (mem_supportMatching_iff.mp hyf k).symm.trans
    (mem_supportMatching_iff.mp hyg k)

/-- Exact cancellation identity: each distinct support restriction has
`(n-s)!` completions. -/
theorem card_transporterTargets_mul_factorial (a b : Sym n) :
    (transporterTargets a b).card * (n - a.support.card).factorial =
      (conjugatingElements a b).card := by
  classical
  rw [conjugatingElements_eq_biUnion_supportMatching,
    Finset.card_biUnion (supportMatching_pairwiseDisjoint a b)]
  simp_rw [CanonicalPartialMatching.card_event, supportMatching_size,
    Fintype.card_fin]
  simp

/-- A prime row has at most `p^r r!` distinct support restrictions.  The
fixed-point factorial has been cancelled exactly, rather than discarded in
the transporter union bound. -/
theorem card_transporterTargets_primeRow_le
    (a b : Sym n) (p r : ℕ) (hr : 0 < r)
    (hcycle : a.cycleType = Multiset.replicate r p) :
    (transporterTargets a b).card ≤ p ^ r * r.factorial := by
  have hsupport : a.support.card = p * r := by
    rw [← Equiv.Perm.sum_cycleType, hcycle]
    simp [Nat.mul_comm]
  have hcard := card_conjugatingElements_primeRow_le a b p r hr hcycle
  rw [← card_transporterTargets_mul_factorial a b] at hcard
  have hmul :
      (transporterTargets a b).card * (n - p * r).factorial ≤
        (p ^ r * r.factorial) * (n - p * r).factorial := by
    simpa [hsupport, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcard
  exact Nat.le_of_mul_le_mul_right hmul (Nat.factorial_pos _)

/-- Intersecting a transporter with the core-conditioned sample space
distributes over its canonical support restrictions. -/
theorem conjugatingElements_inter_core_eq_biUnion
    (P Q : BoundedPartition n) (a b : Sym n) :
    conjugatingElements a b ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ =
      (transporterTargets a b).biUnion fun f ↦
        (supportMatching a f).event ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ := by
  classical
  ext y
  rw [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hy, hyCore⟩
    rw [conjugatingElements_eq_biUnion_supportMatching,
      Finset.mem_biUnion] at hy
    obtain ⟨f, hf, hyf⟩ := hy
    exact ⟨f, hf, Finset.mem_inter.mpr ⟨hyf, hyCore⟩⟩
  · rintro ⟨f, hf, hyf⟩
    refine ⟨?_, (Finset.mem_inter.mp hyf).2⟩
    rw [conjugatingElements_eq_biUnion_supportMatching,
      Finset.mem_biUnion]
    exact ⟨f, hf, (Finset.mem_inter.mp hyf).1⟩

/-- Integral conditional bound for one transporter, before inserting the
prime-row estimate for the number of support restrictions. -/
theorem conditioned_transporter_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n) (a b : Sym n) :
    n.descFactorial a.support.card * 2 ^ a.support.card *
        (conjugatingElements a b ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      (transporterTargets a b).card * 3 ^ a.support.card *
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card := by
  classical
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  have hcard :
      (conjugatingElements a b ∩ C).card ≤
        ∑ f ∈ transporterTargets a b,
          ((supportMatching a f).event ∩ C).card := by
    rw [conjugatingElements_inter_core_eq_biUnion P Q a b]
    exact Finset.card_biUnion_le
  have hone (f : Fin a.support.card ↪ Fin n) :
      n.descFactorial a.support.card * 2 ^ a.support.card *
          ((supportMatching a f).event ∩ C).card ≤
        3 ^ a.support.card * C.card := by
    simpa [C, supportMatching_size] using
      conditioned_external_event_nat_bound_core P Q hn (supportMatching a f)
  calc
    n.descFactorial a.support.card * 2 ^ a.support.card *
          (conjugatingElements a b ∩ C).card ≤
        n.descFactorial a.support.card * 2 ^ a.support.card *
          (∑ f ∈ transporterTargets a b,
            ((supportMatching a f).event ∩ C).card) :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ f ∈ transporterTargets a b,
          (n.descFactorial a.support.card * 2 ^ a.support.card *
            ((supportMatching a f).event ∩ C).card) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _f ∈ transporterTargets a b,
          (3 ^ a.support.card * C.card) := by
      exact Finset.sum_le_sum fun f _hf ↦ hone f
    _ = (transporterTargets a b).card * 3 ^ a.support.card * C.card := by
      simp [Nat.mul_assoc]

/-- Prime-row specialization of the conditioned transporter bound. -/
theorem conditioned_primeRow_transporter_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (a b : Sym n) (p r : ℕ) (hr : 0 < r)
    (hcycle : a.cycleType = Multiset.replicate r p) :
    n.descFactorial (p * r) * 2 ^ (p * r) *
        (conjugatingElements a b ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      (p ^ r * r.factorial) * 3 ^ (p * r) *
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card := by
  have hsupport : a.support.card = p * r := by
    rw [← Equiv.Perm.sum_cycleType, hcycle]
    simp [Nat.mul_comm]
  have hbase := conditioned_transporter_nat_bound_core P Q hn a b
  have htargets := card_transporterTargets_primeRow_le a b p r hr hcycle
  have hscaled :
      (transporterTargets a b).card * 3 ^ a.support.card *
          (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
        (p ^ r * r.factorial) * 3 ^ a.support.card *
          (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card := by
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_right _ htargets
  simpa only [hsupport] using hbase.trans hscaled

/-- The conditioned union bound for two finite prime-row slices.  This is
the group-theoretic interface consumed by the portrait estimates. -/
theorem conditioned_conjugationHits_primeRow_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r : ℕ) (hr : 0 < r)
    (hcycle : ∀ a ∈ A,
      a.cycleType = Multiset.replicate r p) :
    n.descFactorial (p * r) * 2 ^ (p * r) *
        (conjugationHits A B ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      A.card * B.card *
        ((p ^ r * r.factorial) * 3 ^ (p * r) *
          (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card) := by
  classical
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  have hsubset :
      conjugationHits A B ∩ C ⊆
        A.biUnion fun a ↦ B.biUnion fun b ↦
          conjugatingElements a b ∩ C := by
    intro x hx
    obtain ⟨hxHit, hxC⟩ := Finset.mem_inter.mp hx
    obtain ⟨a, ha, hxaB⟩ := mem_conjugationHits.mp hxHit
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    rw [Finset.mem_biUnion]
    refine ⟨x * a * x⁻¹, hxaB, Finset.mem_inter.mpr ⟨?_, hxC⟩⟩
    exact mem_conjugatingElements.mpr rfl
  have hcard :
      (conjugationHits A B ∩ C).card ≤
        ∑ a ∈ A, ∑ b ∈ B,
          (conjugatingElements a b ∩ C).card := by
    calc
      (conjugationHits A B ∩ C).card ≤
          (A.biUnion fun a ↦ B.biUnion fun b ↦
            conjugatingElements a b ∩ C).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ a ∈ A,
          (B.biUnion fun b ↦ conjugatingElements a b ∩ C).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, ∑ b ∈ B,
          (conjugatingElements a b ∩ C).card := by
        exact Finset.sum_le_sum fun _a _ha ↦ Finset.card_biUnion_le
  have hone (a : Sym n) (ha : a ∈ A) (b : Sym n) :
      n.descFactorial (p * r) * 2 ^ (p * r) *
          (conjugatingElements a b ∩ C).card ≤
        (p ^ r * r.factorial) * 3 ^ (p * r) * C.card := by
    simpa [C] using conditioned_primeRow_transporter_nat_bound_core
      P Q hn a b p r hr (hcycle a ha)
  calc
    n.descFactorial (p * r) * 2 ^ (p * r) *
          (conjugationHits A B ∩ C).card ≤
        n.descFactorial (p * r) * 2 ^ (p * r) *
          (∑ a ∈ A, ∑ b ∈ B,
            (conjugatingElements a b ∩ C).card) :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ a ∈ A, ∑ b ∈ B,
          (n.descFactorial (p * r) * 2 ^ (p * r) *
            (conjugatingElements a b ∩ C).card) := by
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ _a ∈ A, ∑ _b ∈ B,
          ((p ^ r * r.factorial) * 3 ^ (p * r) * C.card) := by
      exact Finset.sum_le_sum fun a ha ↦
        Finset.sum_le_sum fun b _hb ↦ hone a ha b
    _ = A.card * B.card *
          ((p ^ r * r.factorial) * 3 ^ (p * r) * C.card) := by
      simp [Nat.mul_assoc]

/-- The real row majorant after conditioning on the core. -/
noncomputable def conditionedPrimeRowMajorant
    (n : ℕ) (A B : Finset (Sym n)) (p r : ℕ) : ℝ :=
  ((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
      (3 / 2 : ℝ) ^ (p * r) /
    ((n.descFactorial (p * r) : ℕ) : ℝ)

/-- Relative-density form of the conditioned prime-row transporter bound. -/
theorem conditioned_conjugationHits_primeRow_density_le
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r : ℕ) (hr : 0 < r)
    (hsn : p * r ≤ n)
    (hcycle : ∀ a ∈ A,
      a.cycleType = Multiset.replicate r p) :
    ((conjugationHits A B ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeRowMajorant n A B p r := by
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  have hCnat : 0 < C.card := by
    rw [show C = simplePermutations P Q by
      exact avoid_coreCanonicalFamily_eq_simplePermutations P Q]
    exact simplePermutations_card_pos P Q hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hDnat : 0 < n.descFactorial (p * r) :=
    Nat.descFactorial_pos.mpr hsn
  have hD : (0 : ℝ) < (n.descFactorial (p * r) : ℕ) := by
    exact_mod_cast hDnat
  have hNat := conditioned_conjugationHits_primeRow_nat_bound_core
    P Q hn A B p r hr hcycle
  have hReal :
      ((n.descFactorial (p * r) : ℕ) : ℝ) *
          (2 : ℝ) ^ (p * r) *
          ((conjugationHits A B ∩ C).card : ℝ) ≤
        ((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
          (3 : ℝ) ^ (p * r) * (C.card : ℝ) := by
    norm_cast
    simpa [C, Nat.mul_assoc] using hNat
  have hpow :
      (3 / 2 : ℝ) ^ (p * r) * (2 : ℝ) ^ (p * r) =
        (3 : ℝ) ^ (p * r) := by
    rw [← mul_pow]
    norm_num
  have hscaled :
      (((n.descFactorial (p * r) : ℕ) : ℝ) *
          ((conjugationHits A B ∩ C).card : ℝ)) *
          (2 : ℝ) ^ (p * r) ≤
        (((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
          (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ)) *
          (2 : ℝ) ^ (p * r) := by
    calc
      (((n.descFactorial (p * r) : ℕ) : ℝ) *
            ((conjugationHits A B ∩ C).card : ℝ)) *
            (2 : ℝ) ^ (p * r) =
          ((n.descFactorial (p * r) : ℕ) : ℝ) *
            (2 : ℝ) ^ (p * r) *
            ((conjugationHits A B ∩ C).card : ℝ) := by ring
      _ ≤ ((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
            (3 : ℝ) ^ (p * r) * (C.card : ℝ) := hReal
      _ = (((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
            (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ)) *
            (2 : ℝ) ^ (p * r) := by rw [← hpow]; ring
  have hunscaled :
      ((n.descFactorial (p * r) : ℕ) : ℝ) *
          ((conjugationHits A B ∩ C).card : ℝ) ≤
        ((A.card * B.card * (p ^ r * r.factorial) : ℕ) : ℝ) *
          (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ) :=
    le_of_mul_le_mul_right hscaled
      (pow_pos (by norm_num : (0 : ℝ) < 2) (p * r))
  unfold conditionedPrimeRowMajorant
  change ((conjugationHits A B ∩ C).card : ℝ) / C.card ≤ _
  apply (div_le_div_iff₀ hC hD).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hunscaled

/-- Source-outside row specialization for soluble-subgroup slices. -/
theorem conditioned_sourceOutsidePrimeRowHit_density_le
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (H K : Subgroup (Sym n)) (p r : ℕ) (hr : 0 < r)
    (hsn : p * r ≤ n) :
    ((conjugationHits (outsideCorePrimeRowSlice H p r)
          (primeRowSlice K p r) ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeRowMajorant n
        (outsideCorePrimeRowSlice H p r) (primeRowSlice K p r) p r := by
  apply conditioned_conjugationHits_primeRow_density_le
    P Q hn _ _ p r hr hsn
  intro a ha
  exact (mem_outsideCorePrimeRowSlice.mp ha).2.2.1

/-- Target-outside row specialization for soluble-subgroup slices. -/
theorem conditioned_targetOutsidePrimeRowHit_density_le
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (H K : Subgroup (Sym n)) (p r : ℕ) (hr : 0 < r)
    (hsn : p * r ≤ n) :
    ((conjugationHits (primeRowSlice H p r)
          (outsideCorePrimeRowSlice K p r) ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeRowMajorant n
        (primeRowSlice H p r) (outsideCorePrimeRowSlice K p r) p r := by
  apply conditioned_conjugationHits_primeRow_density_le
    P Q hn _ _ p r hr hsn
  intro a ha
  exact (mem_primeRowSlice.mp ha).2.2.1

end Kourovka213

import Kourovka.Problems.P21_03.Proof.PrimeTransporterCanonical
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Core/noncore cycle profiles for a prime row

This file isolates the finite combinatorics behind the refined prime-row
transporter estimate.  A cycle factor is called core when its whole support
lies in one block of the bounded core partition.  A simple conjugator cannot
send a core cycle of length at least two to a core cycle.  Consequently, if
the source and target have `uₐ` and `uᵇ` noncore cycles, respectively, then
the row is relevant only when `r ≤ uₐ + uᵇ`.

The final section packages the sharp finite code.  Its three fields are one
of `p` rotations for every cycle, an injection of the `r-uₐ` source-core
cycles into the `uᵇ` target-noncore cycles, and an ordering of the `uₐ`
remaining source cycles.  Its cardinality is

`p^r * uₐ! * (uᵇ)_(r-uₐ)`,

which is the integral form of
`p^r * uₐ! * uᵇ! / (uₐ+uᵇ-r)!`.
-/

open Subgroup
open scoped BigOperators

namespace Kourovka213

variable {n : ℕ}

/-- The support of `c` lies in a single block of `P`.  The pairwise
formulation avoids choosing a block label and is convenient for `IsSimple`. -/
def CycleContainedInBlock (P : BoundedPartition n) (c : Sym n) : Prop :=
  ∀ {i j : Fin n}, i ∈ c.support → j ∈ c.support →
    P.block i = P.block j

/-- Cycle factors of `g` whose supports lie in single `P`-blocks. -/
noncomputable def coreCycleFactors (P : BoundedPartition n) (g : Sym n) :
    Finset g.cycleFactorsFinset := by
  classical
  exact Finset.univ.filter fun c ↦ CycleContainedInBlock P c.1

/-- Cycle factors of `g` which cross at least two `P`-blocks. -/
noncomputable def noncoreCycleFactors (P : BoundedPartition n) (g : Sym n) :
    Finset g.cycleFactorsFinset := by
  classical
  exact Finset.univ.filter fun c ↦ ¬ CycleContainedInBlock P c.1

@[simp]
theorem mem_coreCycleFactors {P : BoundedPartition n} {g : Sym n}
    {c : g.cycleFactorsFinset} :
    c ∈ coreCycleFactors P g ↔ CycleContainedInBlock P c.1 := by
  classical
  simp [coreCycleFactors]

@[simp]
theorem mem_noncoreCycleFactors {P : BoundedPartition n} {g : Sym n}
    {c : g.cycleFactorsFinset} :
    c ∈ noncoreCycleFactors P g ↔ ¬ CycleContainedInBlock P c.1 := by
  classical
  simp [noncoreCycleFactors]

/-- The intrinsic noncore-cycle count of a permutation relative to `P`. -/
noncomputable def noncoreCycleCount (P : BoundedPartition n) (g : Sym n) : ℕ :=
  (noncoreCycleFactors P g).card

/-- Core and noncore factors partition all cycle factors. -/
theorem card_coreCycleFactors_add_noncoreCycleCount
    (P : BoundedPartition n) (g : Sym n) :
    (coreCycleFactors P g).card + noncoreCycleCount P g = g.cycleType.card := by
  classical
  rw [coreCycleFactors, noncoreCycleCount, noncoreCycleFactors,
    Finset.card_filter_add_card_filter_not]
  simp [Equiv.Perm.cycleType_def]

theorem noncoreCycleCount_le_cycleType_card
    (P : BoundedPartition n) (g : Sym n) :
    noncoreCycleCount P g ≤ g.cycleType.card := by
  have h := card_coreCycleFactors_add_noncoreCycleCount P g
  omega

/-- A permutation preserves every `P`-block exactly when every one of its
nontrivial cycle factors is contained in a single block. -/
theorem mem_youngSubgroup_iff_all_cycleFactors_contained
    (P : BoundedPartition n) (g : Sym n) :
    g ∈ youngSubgroup P ↔
      ∀ c : g.cycleFactorsFinset, CycleContainedInBlock P c.1 := by
  classical
  constructor
  · intro hg c i j hi hj
    have hcycle := Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.2
    obtain ⟨m, _hm_lt, hm⟩ := hcycle.exists_pow_eq hi hj
    have hgpow : g ^ m ∈ youngSubgroup P := (youngSubgroup P).pow_mem hg m
    have hblock := (mem_youngSubgroup.mp hgpow) i
    rw [hm] at hblock
    exact hblock.symm
  · intro hall
    rw [mem_youngSubgroup]
    intro i
    by_cases hi : i ∈ g.support
    · obtain ⟨c, hc, hic⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hi
      let c' : g.cycleFactorsFinset := ⟨c, hc⟩
      have hfactor := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).2 i hic
      have hcImage : c i ∈ c.support := Equiv.Perm.apply_mem_support.mpr hic
      have hsame := hall c' hcImage hic
      simpa [hfactor] using hsame
    · simp [Equiv.Perm.notMem_support.mp hi]

/-- Vanishing intrinsic noncore count is exactly membership in the Young
subgroup on the same blocks. -/
theorem noncoreCycleCount_eq_zero_iff_mem_youngSubgroup
    (P : BoundedPartition n) (g : Sym n) :
    noncoreCycleCount P g = 0 ↔ g ∈ youngSubgroup P := by
  classical
  rw [mem_youngSubgroup_iff_all_cycleFactors_contained]
  constructor
  · intro hzero c
    by_contra hc
    have hmem : c ∈ noncoreCycleFactors P g :=
      mem_noncoreCycleFactors.mpr hc
    have hpos : 0 < noncoreCycleCount P g := by
      rw [noncoreCycleCount]
      exact Finset.card_pos.mpr ⟨c, hmem⟩
    omega
  · intro hall
    rw [noncoreCycleCount, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    exact (mem_noncoreCycleFactors.mp hc) (hall c)

/-- The part of a finite row slice having exactly `u` noncore cycles. -/
noncomputable def primeCycleProfileSlice
    (P : BoundedPartition n) (A : Finset (Sym n)) (u : ℕ) :
    Finset (Sym n) :=
  A.filter fun g ↦ noncoreCycleCount P g = u

@[simp]
theorem mem_primeCycleProfileSlice
    {P : BoundedPartition n} {A : Finset (Sym n)} {u : ℕ} {g : Sym n} :
    g ∈ primeCycleProfileSlice P A u ↔
      g ∈ A ∧ noncoreCycleCount P g = u := by
  classical
  simp [primeCycleProfileSlice]

/-- A row slice with `r` cycle factors is the disjoint profile decomposition
indexed by `0,…,r`.  The equality here is the coverage statement; uniqueness
of the index follows immediately from `noncoreCycleCount`. -/
theorem primeCycleProfileSlice_biUnion_eq
    (P : BoundedPartition n) (A : Finset (Sym n)) (r : ℕ)
    (hrow : ∀ g ∈ A, g.cycleType.card = r) :
    (Finset.range (r + 1)).biUnion (primeCycleProfileSlice P A) = A := by
  classical
  ext g
  constructor
  · intro hg
    rw [Finset.mem_biUnion] at hg
    obtain ⟨u, _hu, hgu⟩ := hg
    exact (mem_primeCycleProfileSlice.mp hgu).1
  · intro hg
    rw [Finset.mem_biUnion]
    refine ⟨noncoreCycleCount P g, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hle := noncoreCycleCount_le_cycleType_card P g
      rw [hrow g hg] at hle
      omega
    · exact mem_primeCycleProfileSlice.mpr ⟨hg, rfl⟩

/-- Ordered source/target pairs in one noncore-cycle profile. -/
noncomputable def primeCyclePairProfileSlice
    (P Q : BoundedPartition n) (A B : Finset (Sym n)) (ua ub : ℕ) :
    Finset (Sym n × Sym n) :=
  (A.product B).filter fun ab ↦
    noncoreCycleCount P ab.1 = ua ∧
      noncoreCycleCount Q ab.2 = ub

@[simp]
theorem mem_primeCyclePairProfileSlice
    {P Q : BoundedPartition n} {A B : Finset (Sym n)}
    {ua ub : ℕ} {a b : Sym n} :
    (a, b) ∈ primeCyclePairProfileSlice P Q A B ua ub ↔
      a ∈ A ∧ b ∈ B ∧
        noncoreCycleCount P a = ua ∧
        noncoreCycleCount Q b = ub := by
  classical
  simp [primeCyclePairProfileSlice, and_assoc]

/-- Conjugation transports each cycle factor of `a` injectively to a cycle
factor of `b`. -/
noncomputable def cycleFactorConjEmbedding
    (a b x : Sym n) (hx : x * a * x⁻¹ = b) :
    a.cycleFactorsFinset ↪ b.cycleFactorsFinset where
  toFun c := ⟨x * c.1 * x⁻¹, by
    rw [← hx]
    exact (Equiv.Perm.mem_cycleFactorsFinset_conj a x c.1).2 c.2⟩
  inj' := by
    intro c d hcd
    apply Subtype.ext
    have hval : x * c.1 * x⁻¹ = x * d.1 * x⁻¹ :=
      congrArg Subtype.val hcd
    calc
      c.1 = x⁻¹ * (x * c.1 * x⁻¹) * x := by group
      _ = x⁻¹ * (x * d.1 * x⁻¹) * x := by rw [hval]
      _ = d.1 := by group

/-- Every cycle factor in a `p^r` row has support cardinality `p`. -/
theorem cycleFactor_support_card_eq_of_cycleType_replicate
    {g : Sym n} {p r : ℕ}
    (hcycle : g.cycleType = Multiset.replicate r p)
    (c : g.cycleFactorsFinset) :
    c.1.support.card = p := by
  have hmem : c.1.support.card ∈ g.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr
      ⟨c.1, Finset.mem_def.mp c.2, rfl⟩
  rw [hcycle] at hmem
  exact Multiset.eq_of_mem_replicate hmem

/-- A cycle supported inside one block of a bounded core partition has at
most four moved points. -/
theorem cycleFactor_support_card_le_four_of_contained
    (P : BoundedPartition n) (g : Sym n) (c : g.cycleFactorsFinset)
    (hc : CycleContainedInBlock P c.1) :
    c.1.support.card ≤ 4 := by
  classical
  obtain ⟨i, hi⟩ :=
    Equiv.Perm.IsCycle.nonempty_support
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
  let e : {j : Fin n // j ∈ c.1.support} ↪
      {j : Fin n // P.block j = P.block i} :=
    { toFun := fun j ↦ ⟨j.1, hc j.2 hi⟩
      inj' := by
        intro j k h
        apply Subtype.ext
        exact congrArg
          (fun z : {x : Fin n // P.block x = P.block i} ↦ (z : Fin n)) h }
  have hcard : Fintype.card {j : Fin n // j ∈ c.1.support} ≤
      Fintype.card {j : Fin n // P.block j = P.block i} :=
    Fintype.card_le_of_injective e e.injective
  calc
    c.1.support.card =
        Fintype.card {j : Fin n // j ∈ c.1.support} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card {j : Fin n // P.block j = P.block i} := hcard
    _ ≤ 4 := P.card_fiber_le_four (P.block i)

/-- If every cycle factor has support at least five, every factor crosses a
core block and hence the noncore count is the full cycle count. -/
theorem noncoreCycleCount_eq_cycleType_card_of_five_le
    (P : BoundedPartition n) (g : Sym n)
    (hfive : ∀ c : g.cycleFactorsFinset, 5 ≤ c.1.support.card) :
    noncoreCycleCount P g = g.cycleType.card := by
  classical
  unfold noncoreCycleCount noncoreCycleFactors
  have hfilter :
      Finset.univ.filter
          (fun c : g.cycleFactorsFinset ↦ ¬ CycleContainedInBlock P c.1) =
        Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c _hc
    intro hcontained
    have hfour := cycleFactor_support_card_le_four_of_contained P g c hcontained
    have hfivec := hfive c
    omega
  rw [hfilter, Finset.card_univ]
  simp [Equiv.Perm.cycleType_def]

/-- In a `p^r` row with `p ≥ 5`, all `r` cycles are intrinsically noncore;
the core partition has blocks of size at most four. -/
theorem noncoreCycleCount_eq_of_five_le_cycleType_replicate
    (P : BoundedPartition n) (g : Sym n) {p r : ℕ}
    (hp : 5 ≤ p) (hcycle : g.cycleType = Multiset.replicate r p) :
    noncoreCycleCount P g = r := by
  calc
    noncoreCycleCount P g = g.cycleType.card :=
      noncoreCycleCount_eq_cycleType_card_of_five_le P g fun c ↦ by
        rw [cycleFactor_support_card_eq_of_cycleType_replicate hcycle c]
        exact hp
    _ = r := by simp [hcycle]

/-- Consequently the intrinsic profile decomposition of a `p ≥ 5` row has
only its all-noncore slice. -/
theorem primeCycleProfileSlice_eq_of_five_le
    (P : BoundedPartition n) (A : Finset (Sym n)) (p r u : ℕ)
    (hp : 5 ≤ p)
    (hcycle : ∀ g ∈ A, g.cycleType = Multiset.replicate r p) :
    primeCycleProfileSlice P A u = if u = r then A else ∅ := by
  classical
  ext g
  by_cases hu : u = r
  · subst u
    simp only [if_pos rfl, mem_primeCycleProfileSlice]
    constructor
    · exact And.left
    · intro hg
      exact ⟨hg,
        noncoreCycleCount_eq_of_five_le_cycleType_replicate
          P g hp (hcycle g hg)⟩
  · simp only [if_neg hu, Finset.notMem_empty, iff_false,
      mem_primeCycleProfileSlice, not_and]
    intro hg
    exact fun hcount ↦ hu (hcount.symm.trans
      (noncoreCycleCount_eq_of_five_le_cycleType_replicate
        P g hp (hcycle g hg)))

/-- Under a simple relative position, a source-core cycle of length at least
two cannot be transported to a target-core cycle. -/
theorem cycleFactorConjEmbedding_mem_noncore_of_mem_core
    (P Q : BoundedPartition n) (a b x : Sym n) (p r : ℕ)
    (hp : 2 ≤ p) (hcycle : a.cycleType = Multiset.replicate r p)
    (hx : x * a * x⁻¹ = b) (hsimple : IsSimple P Q x)
    (c : a.cycleFactorsFinset) (hc : c ∈ coreCycleFactors P a) :
    cycleFactorConjEmbedding a b x hx c ∈ noncoreCycleFactors Q b := by
  classical
  rw [mem_noncoreCycleFactors]
  intro htarget
  have hcard : c.1.support.card = p :=
    cycleFactor_support_card_eq_of_cycleType_replicate hcycle c
  have hone : 1 < c.1.support.card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hone
  have hsource : P.block i = P.block j :=
    (mem_coreCycleFactors.mp hc) hi hj
  apply (hsimple hij hsource)
  apply htarget
  · change x i ∈ (x * c.1 * x⁻¹).support
    rw [Equiv.Perm.support_conj]
    simp [hi]
  · change x j ∈ (x * c.1 * x⁻¹).support
    rw [Equiv.Perm.support_conj]
    simp [hj]

/-- The exact overlap/relevance test used by the profile checker. -/
theorem primeCycleProfiles_relevant
    (P Q : BoundedPartition n) (a b x : Sym n) (p r ua ub : ℕ)
    (hp : 2 ≤ p) (hcycle : a.cycleType = Multiset.replicate r p)
    (hx : x * a * x⁻¹ = b) (hsimple : IsSimple P Q x)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    r ≤ ua + ub := by
  classical
  have hmap : Set.MapsTo
      (cycleFactorConjEmbedding a b x hx)
      (coreCycleFactors P a : Set a.cycleFactorsFinset)
      (noncoreCycleFactors Q b : Set b.cycleFactorsFinset) := by
    intro c hc
    exact cycleFactorConjEmbedding_mem_noncore_of_mem_core
      P Q a b x p r hp hcycle hx hsimple c hc
  have hcore_le : (coreCycleFactors P a).card ≤
      (noncoreCycleFactors Q b).card :=
    Finset.card_le_card_of_injOn (cycleFactorConjEmbedding a b x hx)
      hmap (cycleFactorConjEmbedding a b x hx).injective.injOn
  have hsource := card_coreCycleFactors_add_noncoreCycleCount P a
  have htargetCount : (noncoreCycleFactors Q b).card = ub := hub
  have hcycles : a.cycleType.card = r := by simp [hcycle]
  rw [hua, hcycles] at hsource
  rw [htargetCount] at hcore_le
  omega

/-! ## Relevant cycle embeddings -/

/-- The type of source cycle factors contained in one source-core block. -/
abbrev CoreCycleFactor (P : BoundedPartition n) (g : Sym n) :=
  {c : g.cycleFactorsFinset // CycleContainedInBlock P c.1}

/-- The type of source cycle factors crossing source-core blocks. -/
abbrev NoncoreCycleFactor (P : BoundedPartition n) (g : Sym n) :=
  {c : g.cycleFactorsFinset // ¬ CycleContainedInBlock P c.1}

noncomputable instance coreCycleFactorFintype
    (P : BoundedPartition n) (g : Sym n) :
    Fintype (CoreCycleFactor P g) := Fintype.ofFinite _

noncomputable instance noncoreCycleFactorFintype
    (P : BoundedPartition n) (g : Sym n) :
    Fintype (NoncoreCycleFactor P g) := Fintype.ofFinite _

theorem card_coreCycleFactor (P : BoundedPartition n) (g : Sym n) :
    Fintype.card (CoreCycleFactor P g) = (coreCycleFactors P g).card := by
  classical
  rw [Fintype.card_subtype]
  rfl

theorem card_noncoreCycleFactor (P : BoundedPartition n) (g : Sym n) :
    Fintype.card (NoncoreCycleFactor P g) = noncoreCycleCount P g := by
  classical
  rw [Fintype.card_subtype]
  rfl

/-- Division-free matching code for a relevant cycle embedding.  First map
all source-core cycles injectively into target-noncore cycles.  Then map the
source-noncore cycles into the complement of that first range. -/
abbrev RefinedCycleMatchingCodeFor
    (P Q : BoundedPartition n) (a b : Sym n) :=
  Σ f : CoreCycleFactor P a ↪ NoncoreCycleFactor Q b,
    NoncoreCycleFactor P a ↪
      ↥(Set.range
        (f.trans (Function.Embedding.subtype
          (fun c : b.cycleFactorsFinset ↦
            ¬ CycleContainedInBlock Q c.1))))ᶜ

/-- The refined matching code has exactly
`(uᵇ)_(r-uₐ) * uₐ!` elements. -/
theorem card_refinedCycleMatchingCodeFor
    (P Q : BoundedPartition n) (a b : Sym n) (r ua ub : ℕ)
    (htotalA : a.cycleType.card = r)
    (htotalB : b.cycleType.card = r)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    Fintype.card (RefinedCycleMatchingCodeFor P Q a b) =
      ub.descFactorial (r - ua) * ua.factorial := by
  classical
  have hnonA : Fintype.card (NoncoreCycleFactor P a) = ua := by
    rw [card_noncoreCycleFactor, hua]
  have hnonB : Fintype.card (NoncoreCycleFactor Q b) = ub := by
    rw [card_noncoreCycleFactor, hub]
  have hsumA := card_coreCycleFactors_add_noncoreCycleCount P a
  rw [hua, htotalA] at hsumA
  have hcoreA : Fintype.card (CoreCycleFactor P a) = r - ua := by
    rw [card_coreCycleFactor]
    omega
  have hua_le : ua ≤ r := by
    have := noncoreCycleCount_le_cycleType_card P a
    omega
  have hallB : Fintype.card b.cycleFactorsFinset = r := by
    simpa [Equiv.Perm.cycleType_def] using htotalB
  change Fintype.card
      (Σ f : CoreCycleFactor P a ↪ NoncoreCycleFactor Q b,
        NoncoreCycleFactor P a ↪
          ↥(Set.range
            (f.trans (Function.Embedding.subtype
              (fun c : b.cycleFactorsFinset ↦
                ¬ CycleContainedInBlock Q c.1))))ᶜ) = _
  rw [Fintype.card_sigma]
  calc
    (∑ f : CoreCycleFactor P a ↪ NoncoreCycleFactor Q b,
        Fintype.card
          (NoncoreCycleFactor P a ↪
            ↥(Set.range
              (f.trans (Function.Embedding.subtype
                (fun c : b.cycleFactorsFinset ↦
                  ¬ CycleContainedInBlock Q c.1))))ᶜ)) =
        ∑ _f : CoreCycleFactor P a ↪ NoncoreCycleFactor Q b,
          ua.factorial := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [Fintype.card_embedding_eq, Fintype.card_compl_set,
        Fintype.card_range, hallB, hcoreA, hnonA]
      have hsub : r - (r - ua) = ua := by omega
      rw [hsub, Nat.descFactorial_self]
    _ = Fintype.card
          (CoreCycleFactor P a ↪ NoncoreCycleFactor Q b) * ua.factorial := by
      simp
    _ = ub.descFactorial (r - ua) * ua.factorial := by
      rw [Fintype.card_embedding_eq, hnonB, hcoreA]

/-- A cycle embedding satisfying the core-to-noncore restriction forced by
`IsSimple`. -/
abbrev RelevantCycleEmbedding
    (P Q : BoundedPartition n) (a b : Sym n) :=
  {e : a.cycleFactorsFinset ↪ b.cycleFactorsFinset //
    ∀ c : CoreCycleFactor P a,
      ¬ CycleContainedInBlock Q (e c.1).1}

noncomputable instance relevantCycleEmbeddingFintype
    (P Q : BoundedPartition n) (a b : Sym n) :
    Fintype (RelevantCycleEmbedding P Q a b) :=
  Fintype.ofFinite _

/-- Split a relevant embedding into its core restriction and the restriction
to the complementary source cycles. -/
noncomputable def RelevantCycleEmbedding.toMatchingCode
    {P Q : BoundedPartition n} {a b : Sym n}
    (e : RelevantCycleEmbedding P Q a b) :
    RefinedCycleMatchingCodeFor P Q a b := by
  classical
  let f : CoreCycleFactor P a ↪ NoncoreCycleFactor Q b :=
    ⟨fun c ↦ ⟨e.1 c.1, e.2 c⟩,
      fun _ _ h ↦ Subtype.ext
        (e.1.injective (congrArg Subtype.val h))⟩
  refine ⟨f, ?_⟩
  refine ⟨fun c ↦ ⟨e.1 c.1, ?_⟩, ?_⟩
  · rintro ⟨d, hd⟩
    have htarget : e.1 d.1 = e.1 c.1 := by
      exact Subtype.ext (congrArg Subtype.val hd)
    have hsource : d.1 = c.1 := e.1.injective htarget
    exact c.2 (hsource ▸ d.2)
  · intro c d h
    apply Subtype.ext
    exact e.1.injective (congrArg Subtype.val h)

/-- Recover the underlying map on all source cycles from a split matching
code. -/
noncomputable def refinedCycleMatchingMap
    {P Q : BoundedPartition n} {a b : Sym n}
    (m : RefinedCycleMatchingCodeFor P Q a b)
    (c : a.cycleFactorsFinset) : b.cycleFactorsFinset := by
  classical
  by_cases hc : CycleContainedInBlock P c.1
  · exact (m.1 ⟨c, hc⟩).1
  · exact (m.2 ⟨c, hc⟩).1

@[simp]
theorem refinedCycleMatchingMap_toMatchingCode
    {P Q : BoundedPartition n} {a b : Sym n}
    (e : RelevantCycleEmbedding P Q a b)
    (c : a.cycleFactorsFinset) :
    refinedCycleMatchingMap e.toMatchingCode c = e.1 c := by
  classical
  simp only [refinedCycleMatchingMap, RelevantCycleEmbedding.toMatchingCode]
  split_ifs <;> rfl

/-- Relevant cycle embeddings inject into the sharp split matching code. -/
noncomputable def relevantCycleEmbeddingToMatchingCode
    (P Q : BoundedPartition n) (a b : Sym n) :
    RelevantCycleEmbedding P Q a b ↪
      RefinedCycleMatchingCodeFor P Q a b where
  toFun := RelevantCycleEmbedding.toMatchingCode
  inj' := by
    intro e f hef
    apply Subtype.ext
    apply Function.Embedding.ext
    intro c
    have hmap := congrArg (fun m ↦ refinedCycleMatchingMap m c) hef
    simpa using hmap

theorem card_relevantCycleEmbedding_le
    (P Q : BoundedPartition n) (a b : Sym n) (r ua ub : ℕ)
    (htotalA : a.cycleType.card = r)
    (htotalB : b.cycleType.card = r)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    Fintype.card (RelevantCycleEmbedding P Q a b) ≤
      ub.descFactorial (r - ua) * ua.factorial := by
  rw [← card_refinedCycleMatchingCodeFor P Q a b r ua ub
    htotalA htotalB hua hub]
  exact Fintype.card_le_of_injective
    (relevantCycleEmbeddingToMatchingCode P Q a b)
    (relevantCycleEmbeddingToMatchingCode P Q a b).injective

/-! ## Encoding actual simple support restrictions -/

/-- The cycle embedding induced by a simple conjugator, bundled with the
core-to-noncore fact proved above. -/
noncomputable def relevantCycleEmbeddingOfSimpleConjugator
    (P Q : BoundedPartition n) (a b x : Sym n) (p r : ℕ)
    (hp : 2 ≤ p) (hcycle : a.cycleType = Multiset.replicate r p)
    (hx : x * a * x⁻¹ = b) (hsimple : IsSimple P Q x) :
    RelevantCycleEmbedding P Q a b :=
  ⟨cycleFactorConjEmbedding a b x hx, fun c ↦ by
    exact mem_noncoreCycleFactors.mp
      (cycleFactorConjEmbedding_mem_noncore_of_mem_core
        P Q a b x p r hp hcycle hx hsimple c.1
          (mem_coreCycleFactors.mpr c.2))⟩

/-- A basis point on every cycle factor. -/
noncomputable def primeRowCycleBasis (g : Sym n) : Equiv.Perm.Basis g :=
  Classical.choice (Equiv.Perm.Basis.nonempty g)

/-- A relevant cycle embedding together with the image of one basis point
on every source cycle.  Once the cycle matching is fixed, each point lies
in a target cycle of size `p`, giving exactly `p^r` phase choices. -/
abbrev RefinedPrimeSupportRestrictionCode
    (P Q : BoundedPartition n) (a b : Sym n) :=
  Σ e : RelevantCycleEmbedding P Q a b,
    ∀ c : a.cycleFactorsFinset,
      {z : Fin n // z ∈ (e.1 c).1.support}

/-- Cardinal bound for the semantic code: sharp matching factor times one
of `p` phase choices on each of the `r` cycles. -/
theorem card_refinedPrimeSupportRestrictionCode_le
    (P Q : BoundedPartition n) (a b : Sym n) (p r ua ub : ℕ)
    (hcycleA : a.cycleType = Multiset.replicate r p)
    (hcycleB : b.cycleType = Multiset.replicate r p)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    Fintype.card (RefinedPrimeSupportRestrictionCode P Q a b) ≤
      p ^ r * (ub.descFactorial (r - ua) * ua.factorial) := by
  classical
  have htotalA : a.cycleType.card = r := by simp [hcycleA]
  have htotalB : b.cycleType.card = r := by simp [hcycleB]
  have hcyclesA : Fintype.card a.cycleFactorsFinset = r := by
    simpa [Equiv.Perm.cycleType_def] using htotalA
  have hfinsetCyclesA : a.cycleFactorsFinset.card = r := by
    simpa using hcyclesA
  have hphase (e : RelevantCycleEmbedding P Q a b) :
      Fintype.card
          (∀ c : a.cycleFactorsFinset,
            {z : Fin n // z ∈ (e.1 c).1.support}) = p ^ r := by
    rw [Fintype.card_pi]
    have heach : ∀ c : a.cycleFactorsFinset,
        Fintype.card {z : Fin n // z ∈ (e.1 c).1.support} = p := by
      intro c
      rw [Fintype.card_coe]
      exact cycleFactor_support_card_eq_of_cycleType_replicate hcycleB (e.1 c)
    simp_rw [heach]
    simp [hfinsetCyclesA]
  have hcode :
      Fintype.card (RefinedPrimeSupportRestrictionCode P Q a b) =
        Fintype.card (RelevantCycleEmbedding P Q a b) * p ^ r := by
    change Fintype.card
        (Σ e : RelevantCycleEmbedding P Q a b,
          ∀ c : a.cycleFactorsFinset,
            {z : Fin n // z ∈ (e.1 c).1.support}) = _
    rw [Fintype.card_sigma]
    simp_rw [hphase]
    simp
  rw [hcode]
  have hmatching := card_relevantCycleEmbedding_le
    P Q a b r ua ub htotalA htotalB hua hub
  nlinarith [Nat.mul_le_mul_right (p ^ r) hmatching]

/-- Encode a simple conjugator by its induced relevant cycle matching and
the images of the chosen cycle-basis points. -/
noncomputable def refinedPrimeSupportRestrictionCodeOf
    (P Q : BoundedPartition n) (a b x : Sym n) (p r : ℕ)
    (hp : 2 ≤ p) (hcycle : a.cycleType = Multiset.replicate r p)
    (hx : x * a * x⁻¹ = b) (hsimple : IsSimple P Q x) :
    RefinedPrimeSupportRestrictionCode P Q a b := by
  classical
  let e := relevantCycleEmbeddingOfSimpleConjugator
    P Q a b x p r hp hcycle hx hsimple
  refine ⟨e, fun c ↦ ⟨x (primeRowCycleBasis a c), ?_⟩⟩
  change x (primeRowCycleBasis a c) ∈ (x * c.1 * x⁻¹).support
  rw [Equiv.Perm.support_conj]
  exact Finset.mem_map.mpr
    ⟨primeRowCycleBasis a c,
      (primeRowCycleBasis a).mem_support_self c, rfl⟩

/-- Conjugation intertwines every integral power, pointwise. -/
theorem conjugator_zpow_apply
    {a b x : Sym n} (hx : x * a * x⁻¹ = b) (m : ℤ) (z : Fin n) :
    x ((a ^ m) z) = (b ^ m) (x z) := by
  have hpow : x * a ^ m * x⁻¹ = b ^ m := by
    rw [← conj_zpow, hx]
  have hmul : x * a ^ m = b ^ m * x :=
    (mul_inv_eq_iff_eq_mul).mp hpow
  simpa [Equiv.Perm.mul_apply] using congrArg (fun g : Sym n ↦ g z) hmul

/-- Two conjugators agreeing on the chosen point of every source cycle agree
on the whole moved support. -/
theorem conjugators_eq_on_support_of_eq_on_cycleBasis
    (a b x y : Sym n)
    (hx : x * a * x⁻¹ = b) (hy : y * a * y⁻¹ = b)
    (hbasis : ∀ c : a.cycleFactorsFinset,
      x (primeRowCycleBasis a c) = y (primeRowCycleBasis a c)) :
    ∀ i ∈ a.support, x i = y i := by
  intro i hi
  rcases (primeRowCycleBasis a).mem_fixedPoints_or_exists_zpow_eq i with
    hfixed | ⟨c, _hic, m, hm⟩
  · exact False.elim ((Equiv.Perm.mem_support.mp hi)
      (Function.mem_fixedPoints_iff.mp hfixed))
  · calc
      x i = x ((a ^ m) (primeRowCycleBasis a c)) := by rw [hm]
      _ = (b ^ m) (x (primeRowCycleBasis a c)) :=
        conjugator_zpow_apply hx m _
      _ = (b ^ m) (y (primeRowCycleBasis a c)) := by rw [hbasis c]
      _ = y ((a ^ m) (primeRowCycleBasis a c)) :=
        (conjugator_zpow_apply hy m _).symm
      _ = y i := by rw [hm]

/-- Support restrictions in a transporter which have at least one core-simple
completion. -/
noncomputable def coreSimpleTransporterTargets
    (P Q : BoundedPartition n) (a b : Sym n) :
    Finset (Fin a.support.card ↪ Fin n) := by
  classical
  exact (transporterTargets a b).filter fun f ↦
    ∃ x ∈ conjugatingElements a b,
      supportTarget a x = f ∧ IsSimple P Q x

@[simp]
theorem mem_coreSimpleTransporterTargets
    {P Q : BoundedPartition n} {a b : Sym n}
    {f : Fin a.support.card ↪ Fin n} :
    f ∈ coreSimpleTransporterTargets P Q a b ↔
      f ∈ transporterTargets a b ∧
      ∃ x ∈ conjugatingElements a b,
        supportTarget a x = f ∧ IsSimple P Q x := by
  classical
  simp [coreSimpleTransporterTargets]

noncomputable def coreSimpleTransporterWitness
    (P Q : BoundedPartition n) (a b : Sym n)
    (f : ↑(coreSimpleTransporterTargets P Q a b)) : Sym n :=
  Classical.choose (mem_coreSimpleTransporterTargets.mp f.2).2

theorem coreSimpleTransporterWitness_spec
    (P Q : BoundedPartition n) (a b : Sym n)
    (f : ↑(coreSimpleTransporterTargets P Q a b)) :
    coreSimpleTransporterWitness P Q a b f ∈ conjugatingElements a b ∧
      supportTarget a (coreSimpleTransporterWitness P Q a b f) = f.1 ∧
      IsSimple P Q (coreSimpleTransporterWitness P Q a b f) :=
  Classical.choose_spec (mem_coreSimpleTransporterTargets.mp f.2).2

/-- The actual sharp encoding of every relevant support restriction. -/
noncomputable def coreSimpleTransporterTargetsEmbedding
    (P Q : BoundedPartition n) (a b : Sym n) (p r : ℕ)
    (hp : 2 ≤ p) (hcycle : a.cycleType = Multiset.replicate r p) :
    ↑(coreSimpleTransporterTargets P Q a b) ↪
      RefinedPrimeSupportRestrictionCode P Q a b where
  toFun f := by
    let x := coreSimpleTransporterWitness P Q a b f
    have hs := coreSimpleTransporterWitness_spec P Q a b f
    exact refinedPrimeSupportRestrictionCodeOf
      P Q a b x p r hp hcycle (mem_conjugatingElements.mp hs.1) hs.2.2
  inj' := by
    intro f g hfg
    let x := coreSimpleTransporterWitness P Q a b f
    let y := coreSimpleTransporterWitness P Q a b g
    have hspecF := coreSimpleTransporterWitness_spec P Q a b f
    have hspecG := coreSimpleTransporterWitness_spec P Q a b g
    have hx : x * a * x⁻¹ = b := mem_conjugatingElements.mp hspecF.1
    have hy : y * a * y⁻¹ = b := mem_conjugatingElements.mp hspecG.1
    have hbasis : ∀ c : a.cycleFactorsFinset,
        x (primeRowCycleBasis a c) = y (primeRowCycleBasis a c) := by
      intro c
      exact congrArg
        (fun z : RefinedPrimeSupportRestrictionCode P Q a b ↦ (z.2 c).1) hfg
    have hxy : ∀ i ∈ a.support, x i = y i :=
      conjugators_eq_on_support_of_eq_on_cycleBasis a b x y hx hy hbasis
    apply Subtype.ext
    calc
      f.1 = supportTarget a x := hspecF.2.1.symm
      _ = supportTarget a y := by
        apply Function.Embedding.ext
        intro k
        exact hxy (supportSource a k) (supportSource_mem a k)
      _ = g.1 := hspecG.2.1

/-- Sharp integral bound for the number of support restrictions admitting a
simple completion. -/
theorem card_coreSimpleTransporterTargets_le
    (P Q : BoundedPartition n) (a b : Sym n) (p r ua ub : ℕ)
    (hp : 2 ≤ p)
    (hcycleA : a.cycleType = Multiset.replicate r p)
    (hcycleB : b.cycleType = Multiset.replicate r p)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    (coreSimpleTransporterTargets P Q a b).card ≤
      p ^ r * (ub.descFactorial (r - ua) * ua.factorial) := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_le_of_injective
    (coreSimpleTransporterTargetsEmbedding P Q a b p r hp hcycleA)
    (coreSimpleTransporterTargetsEmbedding P Q a b p r hp hcycleA).injective).trans
      (card_refinedPrimeSupportRestrictionCode_le
        P Q a b p r ua ub hcycleA hcycleB hua hub)

/-- After intersecting with the core-simple sample space, only support
restrictions admitting a simple completion remain. -/
theorem conjugatingElements_inter_core_eq_biUnion_coreSimpleTargets
    (P Q : BoundedPartition n) (a b : Sym n) :
    conjugatingElements a b ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ =
      (coreSimpleTransporterTargets P Q a b).biUnion fun f ↦
        (supportMatching a f).event ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ := by
  classical
  ext y
  rw [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨hy, hyCore⟩
    refine ⟨supportTarget a y, ?_, ?_⟩
    · apply mem_coreSimpleTransporterTargets.mpr
      refine ⟨mem_transporterTargets.mpr ⟨y, hy, rfl⟩, ?_⟩
      exact ⟨y, hy, rfl, (mem_avoid_coreCanonicalFamily_iff_isSimple P Q y).mp hyCore⟩
    · exact Finset.mem_inter.mpr ⟨by
        rw [mem_supportMatching_iff]
        intro k
        rfl, hyCore⟩
  · rintro ⟨f, hf, hyf⟩
    obtain ⟨x, hx, hxf, _hxSimple⟩ :=
      (mem_coreSimpleTransporterTargets.mp hf).2
    have hyMatch : y ∈ (supportRestrictionEvent a x).event := by
      simpa [supportRestrictionEvent, hxf] using (Finset.mem_inter.mp hyf).1
    exact ⟨supportRestrictionEvent_subset_conjugatingElements hx hyMatch,
      (Finset.mem_inter.mp hyf).2⟩

/-- Conditional canonical-event bound indexed only by support restrictions
which can actually survive the core-simple condition. -/
theorem conditioned_transporter_nat_bound_coreSimpleTargets
    (P Q : BoundedPartition n) (hn : 123 ≤ n) (a b : Sym n) :
    n.descFactorial a.support.card * 2 ^ a.support.card *
        (conjugatingElements a b ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      (coreSimpleTransporterTargets P Q a b).card *
        3 ^ a.support.card *
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card := by
  classical
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  have hcard :
      (conjugatingElements a b ∩ C).card ≤
        ∑ f ∈ coreSimpleTransporterTargets P Q a b,
          ((supportMatching a f).event ∩ C).card := by
    rw [conjugatingElements_inter_core_eq_biUnion_coreSimpleTargets P Q a b]
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
          (∑ f ∈ coreSimpleTransporterTargets P Q a b,
            ((supportMatching a f).event ∩ C).card) :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ f ∈ coreSimpleTransporterTargets P Q a b,
          (n.descFactorial a.support.card * 2 ^ a.support.card *
            ((supportMatching a f).event ∩ C).card) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _f ∈ coreSimpleTransporterTargets P Q a b,
          (3 ^ a.support.card * C.card) := by
      exact Finset.sum_le_sum fun f _hf ↦ hone f
    _ = (coreSimpleTransporterTargets P Q a b).card *
          3 ^ a.support.card * C.card := by
      simp [Nat.mul_assoc]

/-- Sharp prime-profile specialization of the conditioned transporter
bound.  The falling factorial form automatically vanishes for irrelevant
profiles (`r-uₐ > uᵇ`). -/
theorem conditioned_primeProfile_transporter_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (a b : Sym n) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hcycleA : a.cycleType = Multiset.replicate r p)
    (hcycleB : b.cycleType = Multiset.replicate r p)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    n.descFactorial (p * r) * 2 ^ (p * r) *
        (conjugatingElements a b ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
        3 ^ (p * r) *
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card := by
  have hsupport : a.support.card = p * r := by
    rw [← Equiv.Perm.sum_cycleType, hcycleA]
    simp [Nat.mul_comm]
  have hbase := conditioned_transporter_nat_bound_coreSimpleTargets P Q hn a b
  have htargets := card_coreSimpleTransporterTargets_le
    P Q a b p r ua ub hp hcycleA hcycleB hua hub
  have hscaled :
      (coreSimpleTransporterTargets P Q a b).card *
          3 ^ a.support.card *
          (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
        (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
          3 ^ a.support.card *
          (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card := by
    apply Nat.mul_le_mul_right
    exact Nat.mul_le_mul_right _ htargets
  simpa only [hsupport] using hbase.trans hscaled

/-- Crude-cardinality analogue of the conditional transporter bound.  Only
support restrictions which survive core simplicity are summed, but each of
their events is bounded by its full `(n-s)!` completions. -/
theorem card_conjugatingElements_inter_core_le_coreSimpleTargets
    (P Q : BoundedPartition n) (a b : Sym n) :
    (conjugatingElements a b ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      (coreSimpleTransporterTargets P Q a b).card *
        (n - a.support.card).factorial := by
  classical
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  calc
    (conjugatingElements a b ∩ C).card ≤
        ∑ f ∈ coreSimpleTransporterTargets P Q a b,
          ((supportMatching a f).event ∩ C).card := by
      rw [conjugatingElements_inter_core_eq_biUnion_coreSimpleTargets P Q a b]
      exact Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ coreSimpleTransporterTargets P Q a b,
          (n - a.support.card).factorial := by
      apply Finset.sum_le_sum
      intro f _hf
      calc
        ((supportMatching a f).event ∩ C).card ≤
            (supportMatching a f).event.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = (n - a.support.card).factorial := by
          simp [CanonicalPartialMatching.card_event, supportMatching_size]
    _ = (coreSimpleTransporterTargets P Q a b).card *
          (n - a.support.card).factorial := by simp

/-- Sharp unconditional-cardinality bound for one transporter profile. -/
theorem card_primeProfile_transporter_inter_core_le
    (P Q : BoundedPartition n) (a b : Sym n) (p r ua ub : ℕ)
    (hp : 2 ≤ p)
    (hcycleA : a.cycleType = Multiset.replicate r p)
    (hcycleB : b.cycleType = Multiset.replicate r p)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub) :
    (conjugatingElements a b ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
        (n - p * r).factorial := by
  have hsupport : a.support.card = p * r := by
    rw [← Equiv.Perm.sum_cycleType, hcycleA]
    simp [Nat.mul_comm]
  have hbase := card_conjugatingElements_inter_core_le_coreSimpleTargets
    P Q a b
  have htargets := card_coreSimpleTransporterTargets_le
    P Q a b p r ua ub hp hcycleA hcycleB hua hub
  have hscaled :
      (coreSimpleTransporterTargets P Q a b).card *
          (n - a.support.card).factorial ≤
        (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
          (n - a.support.card).factorial :=
    Nat.mul_le_mul_right _ htargets
  simpa only [hsupport] using hbase.trans hscaled

/-- Sharp conditioned union bound for a pair of fixed profile slices. -/
theorem conditioned_conjugationHits_primeProfile_nat_bound_core
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p)
    (hprofileA : ∀ a ∈ A, noncoreCycleCount P a = ua)
    (hprofileB : ∀ b ∈ B, noncoreCycleCount Q b = ub) :
    n.descFactorial (p * r) * 2 ^ (p * r) *
        (conjugationHits A B ∩
          avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
            Finset.univ).card ≤
      A.card * B.card *
        ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
          3 ^ (p * r) *
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
  have hone (a : Sym n) (ha : a ∈ A) (b : Sym n) (hb : b ∈ B) :
      n.descFactorial (p * r) * 2 ^ (p * r) *
          (conjugatingElements a b ∩ C).card ≤
        (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
          3 ^ (p * r) * C.card := by
    simpa [C] using conditioned_primeProfile_transporter_nat_bound_core
      P Q hn a b p r ua ub hp (hcycleA a ha) (hcycleB b hb)
        (hprofileA a ha) (hprofileB b hb)
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
          ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
            3 ^ (p * r) * C.card) := by
      exact Finset.sum_le_sum fun a ha ↦
        Finset.sum_le_sum fun b hb ↦ hone a ha b hb
    _ = A.card * B.card *
          ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
            3 ^ (p * r) * C.card) := by
      simp [Nat.mul_assoc]

/-- Unconditional-cardinality companion to the profile union bound.  It is
the input for the inverse-core-density half of the hybrid estimate. -/
theorem card_conditioned_conjugationHits_primeProfile_le
    (P Q : BoundedPartition n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p)
    (hprofileA : ∀ a ∈ A, noncoreCycleCount P a = ua)
    (hprofileB : ∀ b ∈ B, noncoreCycleCount Q b = ub) :
    (conjugationHits A B ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      A.card * B.card *
        ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
          (n - p * r).factorial) := by
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
    exact ⟨x * a * x⁻¹, hxaB,
      Finset.mem_inter.mpr ⟨mem_conjugatingElements.mpr rfl, hxC⟩⟩
  calc
    (conjugationHits A B ∩ C).card ≤
        (A.biUnion fun a ↦ B.biUnion fun b ↦
          conjugatingElements a b ∩ C).card := Finset.card_le_card hsubset
    _ ≤ ∑ a ∈ A, ∑ b ∈ B,
          (conjugatingElements a b ∩ C).card := by
      calc
        _ ≤ ∑ a ∈ A,
            (B.biUnion fun b ↦ conjugatingElements a b ∩ C).card :=
          Finset.card_biUnion_le
        _ ≤ _ := Finset.sum_le_sum fun _a _ha ↦ Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, ∑ _b ∈ B,
          ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
            (n - p * r).factorial) := by
      exact Finset.sum_le_sum fun a ha ↦
        Finset.sum_le_sum fun b hb ↦ by
          simpa [C] using card_primeProfile_transporter_inter_core_le
            P Q a b p r ua ub hp (hcycleA a ha) (hcycleB b hb)
              (hprofileA a ha) (hprofileB b hb)
    _ = A.card * B.card *
          ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) *
            (n - p * r).factorial) := by simp [Nat.mul_assoc]

/-- The sharp conditional-LLL majorant for one pair of cycle profiles. -/
noncomputable def conditionedPrimeProfileLLLMajorant
    (n : ℕ) (A B : Finset (Sym n)) (p r ua ub : ℕ) : ℝ :=
  ((A.card * B.card *
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) : ℕ) : ℝ) *
      (3 / 2 : ℝ) ^ (p * r) /
    ((n.descFactorial (p * r) : ℕ) : ℝ)

/-- Real relative-density form of the exact profile-slice bound. -/
theorem conditioned_conjugationHits_primeProfile_density_le
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hsn : p * r ≤ n)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p)
    (hprofileA : ∀ a ∈ A, noncoreCycleCount P a = ua)
    (hprofileB : ∀ b ∈ B, noncoreCycleCount Q b = ub) :
    ((conjugationHits A B ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeProfileLLLMajorant n A B p r ua ub := by
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  let M := A.card * B.card *
    (p ^ r * (ub.descFactorial (r - ua) * ua.factorial))
  have hCnat : 0 < C.card := by
    rw [show C = simplePermutations P Q by
      exact avoid_coreCanonicalFamily_eq_simplePermutations P Q]
    exact simplePermutations_card_pos P Q hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hDnat : 0 < n.descFactorial (p * r) :=
    Nat.descFactorial_pos.mpr hsn
  have hD : (0 : ℝ) < (n.descFactorial (p * r) : ℕ) := by
    exact_mod_cast hDnat
  have hNat := conditioned_conjugationHits_primeProfile_nat_bound_core
    P Q hn A B p r ua ub hp hcycleA hcycleB hprofileA hprofileB
  have hReal :
      ((n.descFactorial (p * r) : ℕ) : ℝ) *
          (2 : ℝ) ^ (p * r) *
          ((conjugationHits A B ∩ C).card : ℝ) ≤
        (M : ℝ) * (3 : ℝ) ^ (p * r) * (C.card : ℝ) := by
    norm_cast
    simpa [C, M, Nat.mul_assoc] using hNat
  have hpow :
      (3 / 2 : ℝ) ^ (p * r) * (2 : ℝ) ^ (p * r) =
        (3 : ℝ) ^ (p * r) := by
    rw [← mul_pow]
    norm_num
  have hscaled :
      (((n.descFactorial (p * r) : ℕ) : ℝ) *
          ((conjugationHits A B ∩ C).card : ℝ)) *
          (2 : ℝ) ^ (p * r) ≤
        (((M : ℝ) * (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ)) *
          (2 : ℝ) ^ (p * r)) := by
    calc
      (((n.descFactorial (p * r) : ℕ) : ℝ) *
            ((conjugationHits A B ∩ C).card : ℝ)) *
            (2 : ℝ) ^ (p * r) =
          ((n.descFactorial (p * r) : ℕ) : ℝ) *
            (2 : ℝ) ^ (p * r) *
            ((conjugationHits A B ∩ C).card : ℝ) := by ring
      _ ≤ (M : ℝ) * (3 : ℝ) ^ (p * r) * (C.card : ℝ) := hReal
      _ = (((M : ℝ) * (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ)) *
            (2 : ℝ) ^ (p * r)) := by rw [← hpow]; ring
  have hunscaled :
      ((n.descFactorial (p * r) : ℕ) : ℝ) *
          ((conjugationHits A B ∩ C).card : ℝ) ≤
        (M : ℝ) * (3 / 2 : ℝ) ^ (p * r) * (C.card : ℝ) :=
    le_of_mul_le_mul_right hscaled
      (pow_pos (by norm_num : (0 : ℝ) < 2) (p * r))
  unfold conditionedPrimeProfileLLLMajorant
  change ((conjugationHits A B ∩ C).card : ℝ) / C.card ≤ _
  apply (div_le_div_iff₀ hC hD).2
  simpa [M, mul_comm, mul_left_comm, mul_assoc] using hunscaled

/-- The inverse-core-density profile majorant.  Unlike the bare core cap,
this retains the same sharp profile numerator and falling-factorial
denominator as the conditional-LLL estimate. -/
noncomputable def conditionedPrimeProfileInverseMajorant
    (n : ℕ) (A B : Finset (Sym n)) (p r ua ub : ℕ) : ℝ :=
  ((A.card * B.card *
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) : ℕ) : ℝ) *
      (2 : ℝ) ^ 15 /
    ((n.descFactorial (p * r) : ℕ) : ℝ)

/-- Relative-density bound obtained from the sharp unconditional row count
and the inverse density of the core-simple sample space. -/
theorem conditioned_conjugationHits_primeProfile_density_le_inverse
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hsn : p * r ≤ n)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p)
    (hprofileA : ∀ a ∈ A, noncoreCycleCount P a = ua)
    (hprofileB : ∀ b ∈ B, noncoreCycleCount Q b = ub) :
    ((conjugationHits A B ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeProfileInverseMajorant n A B p r ua ub := by
  let C := avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event) Finset.univ
  let M := A.card * B.card *
    (p ^ r * (ub.descFactorial (r - ua) * ua.factorial))
  let D := n.descFactorial (p * r)
  have hCnat : 0 < C.card := by
    rw [show C = simplePermutations P Q by
      exact avoid_coreCanonicalFamily_eq_simplePermutations P Q]
    exact simplePermutations_card_pos P Q hn
  have hC : (0 : ℝ) < C.card := by exact_mod_cast hCnat
  have hDnat : 0 < D := Nat.descFactorial_pos.mpr hsn
  have hD : (0 : ℝ) < D := by exact_mod_cast hDnat
  have hNat := card_conditioned_conjugationHits_primeProfile_le
    P Q A B p r ua ub hp hcycleA hcycleB hprofileA hprofileB
  have hscaledNat :
      D * (conjugationHits A B ∩ C).card ≤ M * n.factorial := by
    calc
      D * (conjugationHits A B ∩ C).card ≤
          D * (M * (n - p * r).factorial) :=
        Nat.mul_le_mul_left D (by
          simpa [C, M, Nat.mul_assoc] using hNat)
      _ = M * ((n - p * r).factorial * D) := by ring
      _ = M * n.factorial := by
        have hfac : (n - p * r).factorial * D = n.factorial := by
          simpa [D] using Nat.factorial_mul_descFactorial hsn
        rw [hfac]
  have hscaled :
      (D : ℝ) * ((conjugationHits A B ∩ C).card : ℝ) ≤
        (M : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast hscaledNat
  have hinvScaled :
      (n.factorial : ℝ) ≤ (2 : ℝ) ^ 15 * (C.card : ℝ) := by
    have hinv : (Fintype.card (Sym n) : ℝ) / (C.card : ℝ) ≤
        (2 : ℝ) ^ 15 := by
      simpa [C, avoid_coreCanonicalFamily_eq_simplePermutations] using
        (coreCanonical_inverse_density_lt P Q hn).le
    have hinv' := (div_le_iff₀ hC).mp hinv
    simpa [C, Fintype.card_perm] using hinv'
  have hfinal :
      (D : ℝ) * ((conjugationHits A B ∩ C).card : ℝ) ≤
        (M : ℝ) * (2 : ℝ) ^ 15 * (C.card : ℝ) := by
    calc
      (D : ℝ) * ((conjugationHits A B ∩ C).card : ℝ) ≤
          (M : ℝ) * (n.factorial : ℝ) := hscaled
      _ ≤ (M : ℝ) * ((2 : ℝ) ^ 15 * (C.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hinvScaled (by positivity)
      _ = (M : ℝ) * (2 : ℝ) ^ 15 * (C.card : ℝ) := by ring
  unfold conditionedPrimeProfileInverseMajorant
  change ((conjugationHits A B ∩ C).card : ℝ) / C.card ≤ _
  apply (div_le_div_iff₀ hC hD).2
  simpa [M, D, mul_comm, mul_left_comm, mul_assoc] using hfinal

/-- Every conditioned set has relative density below the uniform inverse
core-density cap, independently of its support size. -/
theorem conditioned_finset_density_lt_core_cap
    (P Q : BoundedPartition n) (hn : 123 ≤ n) (S : Finset (Sym n)) :
    ((S ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card <
      (2 : ℝ) ^ 15 := by
  rw [avoid_coreCanonicalFamily_eq_simplePermutations]
  have hCnat := simplePermutations_card_pos P Q hn
  have hC : (0 : ℝ) < (simplePermutations P Q).card := by
    exact_mod_cast hCnat
  have hcardNat : (S ∩ simplePermutations P Q).card ≤
      Fintype.card (Sym n) := by
    exact Finset.card_le_univ (s := S ∩ simplePermutations P Q)
  have hcard : (((S ∩ simplePermutations P Q).card : ℕ) : ℝ) ≤
      Fintype.card (Sym n) := by exact_mod_cast hcardNat
  exact ((div_le_div_iff_of_pos_right hC).2 hcard).trans_lt
    (coreCanonical_inverse_density_lt P Q hn)

/-- The exact hybrid profile majorant: use whichever is smaller, the
conditional local-lemma estimate or the sharp row count multiplied by the
inverse core density. -/
noncomputable def conditionedPrimeProfileHybridMajorant
    (n : ℕ) (A B : Finset (Sym n)) (p r ua ub : ℕ) : ℝ :=
  min (conditionedPrimeProfileLLLMajorant n A B p r ua ub)
    (conditionedPrimeProfileInverseMajorant n A B p r ua ub)

/-- Literal checker normal form of the hybrid profile majorant.  The sharp
profile numerator is multiplied by the smaller of the conditional-LLL loss
and the inverse-core-density loss. -/
noncomputable def conditionedPrimeProfileCheckerMajorant
    (n : ℕ) (A B : Finset (Sym n)) (p r ua ub : ℕ) : ℝ :=
  ((A.card * B.card *
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) : ℕ) : ℝ) *
      min ((3 / 2 : ℝ) ^ (p * r)) ((2 : ℝ) ^ 15) /
    ((n.descFactorial (p * r) : ℕ) : ℝ)

/-- The semantic hybrid is definitionally the profile expression evaluated
by the external checker. -/
theorem conditionedPrimeProfileHybridMajorant_eq_checker
    (n : ℕ) (A B : Finset (Sym n)) (p r ua ub : ℕ) :
    conditionedPrimeProfileHybridMajorant n A B p r ua ub =
      conditionedPrimeProfileCheckerMajorant n A B p r ua ub := by
  let M : ℝ :=
    ((A.card * B.card *
      (p ^ r * (ub.descFactorial (r - ua) * ua.factorial)) : ℕ) : ℝ)
  let a : ℝ := (3 / 2 : ℝ) ^ (p * r)
  let b : ℝ := (2 : ℝ) ^ 15
  let D : ℝ := ((n.descFactorial (p * r) : ℕ) : ℝ)
  change min (M * a / D) (M * b / D) = M * min a b / D
  rw [min_div_div_right (by positivity : 0 ≤ D)]
  rw [← mul_min_of_nonneg a b (by positivity : 0 ≤ M)]

theorem conditioned_conjugationHits_primeProfile_density_le_hybrid
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hsn : p * r ≤ n)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p)
    (hprofileA : ∀ a ∈ A, noncoreCycleCount P a = ua)
    (hprofileB : ∀ b ∈ B, noncoreCycleCount Q b = ub) :
    ((conjugationHits A B ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeProfileHybridMajorant n A B p r ua ub := by
  rw [conditionedPrimeProfileHybridMajorant, le_min_iff]
  exact ⟨conditioned_conjugationHits_primeProfile_density_le
      P Q hn A B p r ua ub hp hsn hcycleA hcycleB hprofileA hprofileB,
    conditioned_conjugationHits_primeProfile_density_le_inverse
      P Q hn A B p r ua ub hp hsn hcycleA hcycleB hprofileA hprofileB⟩

/-- Direct specialization to the canonical noncore-count profile slices. -/
theorem conditioned_primeCycleProfileSlice_density_le_hybrid
    (P Q : BoundedPartition n) (hn : 123 ≤ n)
    (A B : Finset (Sym n)) (p r ua ub : ℕ) (hp : 2 ≤ p)
    (hsn : p * r ≤ n)
    (hcycleA : ∀ a ∈ A, a.cycleType = Multiset.replicate r p)
    (hcycleB : ∀ b ∈ B, b.cycleType = Multiset.replicate r p) :
    ((conjugationHits (primeCycleProfileSlice P A ua)
          (primeCycleProfileSlice Q B ub) ∩
        avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card : ℝ) /
        (avoidEvents (fun w ↦ (coreCanonicalFamily P Q w).event)
          Finset.univ).card ≤
      conditionedPrimeProfileHybridMajorant n
        (primeCycleProfileSlice P A ua)
        (primeCycleProfileSlice Q B ub) p r ua ub := by
  apply conditioned_conjugationHits_primeProfile_density_le_hybrid
    P Q hn _ _ p r ua ub hp hsn
  · intro a ha
    exact hcycleA a (mem_primeCycleProfileSlice.mp ha).1
  · intro b hb
    exact hcycleB b (mem_primeCycleProfileSlice.mp hb).1
  · intro a ha
    exact (mem_primeCycleProfileSlice.mp ha).2
  · intro b hb
    exact (mem_primeCycleProfileSlice.mp hb).2

/-- Real factorial form of the sharp actual support-restriction bound. -/
theorem cast_card_coreSimpleTransporterTargets_le_factorial_quotient
    (P Q : BoundedPartition n) (a b : Sym n) (p r ua ub : ℕ)
    (hp : 2 ≤ p) (hua_le : ua ≤ r)
    (hcycleA : a.cycleType = Multiset.replicate r p)
    (hcycleB : b.cycleType = Multiset.replicate r p)
    (hua : noncoreCycleCount P a = ua)
    (hub : noncoreCycleCount Q b = ub)
    (hrel : r ≤ ua + ub) :
    ((coreSimpleTransporterTargets P Q a b).card : ℝ) ≤
      (p : ℝ) ^ r * (ua.factorial : ℝ) * (ub.factorial : ℝ) /
        ((ua + ub - r).factorial : ℝ) := by
  have hnat := card_coreSimpleTransporterTargets_le
    P Q a b p r ua ub hp hcycleA hcycleB hua hub
  have hreal : ((coreSimpleTransporterTargets P Q a b).card : ℝ) ≤
      ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hmatching :
      ((ua.factorial * ub.descFactorial (r - ua) : ℕ) : ℝ) =
        (ua.factorial : ℝ) * (ub.factorial : ℝ) /
          ((ua + ub - r).factorial : ℝ) := by
    have hle : r - ua ≤ ub := by omega
    have hsub : ub - (r - ua) = ua + ub - r := by omega
    have hfac := Nat.factorial_mul_descFactorial hle
    have hmul :
        (ua.factorial * ub.descFactorial (r - ua)) *
            (ua + ub - r).factorial =
          ua.factorial * ub.factorial := by
      calc
        (ua.factorial * ub.descFactorial (r - ua)) *
              (ua + ub - r).factorial =
            ua.factorial *
              ((ua + ub - r).factorial *
                ub.descFactorial (r - ua)) := by ac_rfl
        _ = ua.factorial * ub.factorial := by rw [← hsub, hfac]
    have hden : (((ua + ub - r).factorial : ℕ) : ℝ) ≠ 0 := by
      positivity
    apply (eq_div_iff hden).2
    norm_cast
  rw [Nat.cast_mul, Nat.cast_pow,
    show ((ub.descFactorial (r - ua) * ua.factorial : ℕ) : ℝ) =
        ((ua.factorial * ub.descFactorial (r - ua) : ℕ) : ℝ) by
      norm_num [Nat.mul_comm],
    hmatching] at hreal
  simpa [div_eq_mul_inv, mul_assoc] using hreal

/-! ## The sharp finite code -/

/-- A finite code for a relevant prime-row support restriction.  The three
coordinates record rotations, the injection from source-core cycles into
target-noncore cycles, and the residual permutation of source-noncore
cycles. -/
abbrev RefinedPrimeTransporterCode (p r ua ub : ℕ) :=
  (Fin r → Fin p) × (Fin (r - ua) ↪ Fin ub) × Equiv.Perm (Fin ua)

theorem card_refinedPrimeTransporterCode (p r ua ub : ℕ) :
    Fintype.card (RefinedPrimeTransporterCode p r ua ub) =
      p ^ r * (ub.descFactorial (r - ua) * ua.factorial) := by
  classical
  simp [Fintype.card_embedding_eq, Fintype.card_perm]

/-- Division-free form of the matching-factor identity. -/
theorem refinedCycleMatching_mul_overlap_factorial
    {r ua ub : ℕ} (hua : ua ≤ r) (hrel : r ≤ ua + ub) :
    (ua.factorial * ub.descFactorial (r - ua)) *
        (ua + ub - r).factorial =
      ua.factorial * ub.factorial := by
  have hle : r - ua ≤ ub := by omega
  have hsub : ub - (r - ua) = ua + ub - r := by omega
  have hfac := Nat.factorial_mul_descFactorial hle
  calc
    (ua.factorial * ub.descFactorial (r - ua)) *
          (ua + ub - r).factorial =
        ua.factorial *
          ((ua + ub - r).factorial *
            ub.descFactorial (r - ua)) := by ac_rfl
    _ = ua.factorial * ub.factorial := by rw [← hsub, hfac]

/-- Real-valued form of the checker matching factor. -/
theorem cast_refinedCycleMatching_eq_factorial_quotient
    {r ua ub : ℕ} (hua : ua ≤ r) (hrel : r ≤ ua + ub) :
    ((ua.factorial * ub.descFactorial (r - ua) : ℕ) : ℝ) =
      (ua.factorial : ℝ) * (ub.factorial : ℝ) /
        ((ua + ub - r).factorial : ℝ) := by
  have hden : (((ua + ub - r).factorial : ℕ) : ℝ) ≠ 0 := by
    positivity
  apply (eq_div_iff hden).2
  norm_cast
  exact refinedCycleMatching_mul_overlap_factorial hua hrel

/-- Any injective semantic encoding of relevant support restrictions into
the sharp code immediately gives the desired integral transporter bound.
This theorem deliberately exposes the sole remaining transporter-coding
obligation rather than replacing it with the crude `p^r r!` bound. -/
theorem card_le_refinedPrimeTransporterCode_of_embedding
    {p r ua ub : ℕ} {T : Type*} [Fintype T]
    (encode : T ↪ RefinedPrimeTransporterCode p r ua ub) :
    Fintype.card T ≤
      p ^ r * (ub.descFactorial (r - ua) * ua.factorial) := by
  rw [← card_refinedPrimeTransporterCode]
  exact Fintype.card_le_of_injective encode encode.injective

/-- The sharp refined restriction count, in the exact factorial form used by
the external checker. -/
theorem cast_card_le_refinedPrimeTransporter_factorial_quotient
    {p r ua ub : ℕ} {T : Type*} [Fintype T]
    (hua : ua ≤ r) (hrel : r ≤ ua + ub)
    (encode : T ↪ RefinedPrimeTransporterCode p r ua ub) :
    (Fintype.card T : ℝ) ≤
      (p : ℝ) ^ r * (ua.factorial : ℝ) * (ub.factorial : ℝ) /
        ((ua + ub - r).factorial : ℝ) := by
  have hnat := card_le_refinedPrimeTransporterCode_of_embedding encode
  have hreal : (Fintype.card T : ℝ) ≤
      ((p ^ r * (ub.descFactorial (r - ua) * ua.factorial) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_mul, Nat.cast_pow,
    show ((ub.descFactorial (r - ua) * ua.factorial : ℕ) : ℝ) =
        ((ua.factorial * ub.descFactorial (r - ua) : ℕ) : ℝ) by
      norm_num [Nat.mul_comm],
    cast_refinedCycleMatching_eq_factorial_quotient hua hrel] at hreal
  simpa [div_eq_mul_inv, mul_assoc] using hreal

end Kourovka213

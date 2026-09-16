import Kourovka.Problems.P21_44.Proof.Wreath
import Kourovka.Problems.P21_44.Proof.PerfectSubdirect
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The directed pair generates the full degree-five wreath product

The group-theoretic step uses perfectness, full two-coordinate projections,
and the coordinate-kernel commutator argument from `PerfectSubdirect`.
-/

namespace Kourovka.P21_44

open scoped commutatorElement

instance : Group.IsPerfect A5 where
  commutator_eq_top := commutator_alternatingGroup_eq_top (by simp [Alphabet])

theorem a5_pair_transitive (i j k l : Alphabet) (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ σ : A5, σ.val i = k ∧ σ.val j = l := by
  have h3 := alternatingGroup.isMultiplyPretransitive Alphabet
  have : MulAction.IsMultiplyPretransitive A5 Alphabet 2 :=
    MulAction.isMultiplyPretransitive_of_le (by simp [Alphabet]) (Nat.sub_le (Nat.card Alphabet) 2)
  exact MulAction.is_two_pretransitive_iff.mp this hij hkl

/-- A word in the two root permutations. `true` means `rootA`. -/
private def evalRootWord (w : List Bool) : A5 :=
  (w.map fun b => if b then rootA else rootB).prod

/-- A breadth-first list of sixty words; the following kernel computation
checks that their values cover the sixty even permutations on five points. -/
private def rootWords : List (List Bool) :=
  [[],
   [true],
   [false],
   [true, true],
   [true, false],
   [false, true],
   [false, false],
   [true, true, false],
   [true, false, true],
   [true, false, false],
   [false, true, true],
   [false, true, false],
   [false, false, true],
   [true, true, false, true],
   [true, true, false, false],
   [true, false, true, true],
   [true, false, true, false],
   [true, false, false, true],
   [false, true, true, false],
   [false, true, false, true],
   [false, true, false, false],
   [false, false, true, true],
   [false, false, true, false],
   [true, true, false, true, true],
   [true, true, false, true, false],
   [true, true, false, false, true],
   [true, false, true, true, false],
   [true, false, true, false, true],
   [true, false, true, false, false],
   [true, false, false, true, true],
   [true, false, false, true, false],
   [false, true, true, false, true],
   [false, true, true, false, false],
   [false, true, false, true, true],
   [false, true, false, false, true],
   [false, false, true, true, false],
   [false, false, true, false, true],
   [false, false, true, false, false],
   [true, true, false, true, true, false],
   [true, true, false, true, false, true],
   [true, true, false, true, false, false],
   [true, true, false, false, true, true],
   [true, true, false, false, true, false],
   [true, false, true, true, false, false],
   [true, false, true, false, true, true],
   [true, false, false, true, true, false],
   [true, false, false, true, false, false],
   [false, true, true, false, true, true],
   [false, true, true, false, false, true],
   [false, true, false, false, true, true],
   [false, false, true, true, false, true],
   [false, false, true, true, false, false],
   [false, false, true, false, true, true],
   [false, false, true, false, false, true],
   [true, false, true, true, false, false, true],
   [true, false, false, true, true, false, true],
   [true, false, false, true, false, false, true],
   [false, true, true, false, false, true, false],
   [false, true, false, false, true, true, false],
   [true, false, true, true, false, false, true, false]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem rootWords_cover : ∀ σ : A5, σ ∈ rootWords.map evalRootWord := by
  decide

/-- The two specified root permutations generate the natural alternating group. -/
theorem roots_generate : Subgroup.closure ({rootA, rootB} : Set A5) = ⊤ := by
  let K := Subgroup.closure ({rootA, rootB} : Set A5)
  have ha : rootA ∈ K := Subgroup.subset_closure (by simp)
  have hb : rootB ∈ K := Subgroup.subset_closure (by simp)
  have hword (w : List Bool) : evalRootWord w ∈ K := by
    induction w with
    | nil => exact K.one_mem
    | cons b w ih =>
        cases b <;> exact K.mul_mem (by assumption) ih
  apply top_unique
  intro σ _
  obtain ⟨w, _, hw⟩ := List.mem_map.mp (rootWords_cover σ)
  exact hw ▸ hword w

/-- The semidirect product of two perfect groups is perfect. -/
theorem semidirect_isPerfect {N H : Type*} [Group N] [Group H]
    [Group.IsPerfect N] [Group.IsPerfect H] (φ : H →* MulAut N) :
    Group.IsPerfect (SemidirectProduct N H φ) := by
  constructor
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact (commutator _).mul_mem
    (perfect_image_mem_commutator SemidirectProduct.inl x.left)
    (perfect_image_mem_commutator SemidirectProduct.inr x.right)

instance wreath_isPerfect {P : Type*} [Group P] [Group.IsPerfect P] :
    Group.IsPerfect (Wreath P) := by
  have := finite_pi_isPerfect P Alphabet
  exact semidirect_isPerfect (reindexAction P)

theorem a5_transitive (i j : Alphabet) : ∃ σ : A5, σ.val i = j := by
  obtain ⟨k, hk⟩ := exists_ne i
  obtain ⟨l, hl⟩ := exists_ne j
  obtain ⟨σ, hσ, _⟩ := a5_pair_transitive i k j l hk.symm hl.symm
  exact ⟨σ, hσ⟩

namespace Wreath

variable {P : Type*} [Group P]

/-- The base-group part of a subgroup of the wreath product. -/
def basePart (L : Subgroup (Wreath P)) : Subgroup (Alphabet → P) :=
  L.comap SemidirectProduct.inl

@[simp] theorem mem_basePart (L : Subgroup (Wreath P)) (f : Alphabet → P) :
    f ∈ basePart L ↔ SemidirectProduct.inl f ∈ L := Iff.rfl

/-- Conjugation transports sections by the root permutation and an inner twist. -/
theorem conj_inl (g : Wreath P) (f : Alphabet → P) :
    g * SemidirectProduct.inl f * g⁻¹ =
      SemidirectProduct.inl (fun i =>
        g.left i * f (g.right.val⁻¹ i) * (g.left i)⁻¹) := by
  apply SemidirectProduct.ext
  · funext i
    simp [mul_left_apply, inv_left_apply]
  · simp

/-- The base part is invariant under conjugation by the original subgroup. -/
theorem conj_mem_basePart (L : Subgroup (Wreath P))
    (g : Wreath P) (hg : g ∈ L) (f : Alphabet → P) (hf : f ∈ basePart L) :
    (fun i => g.left i * f (g.right.val⁻¹ i) * (g.left i)⁻¹) ∈ basePart L := by
  rw [mem_basePart, ← conj_inl]
  exact L.mul_mem (L.mul_mem hg hf) (L.inv_mem hg)

/-- An element with trivial root is its own embedded base tuple. -/
theorem inl_left_eq (g : Wreath P) (hg : g.right = 1) :
    SemidirectProduct.inl g.left = g := by
  apply SemidirectProduct.ext
  · rfl
  · exact hg.symm

/-- Transitivity transports one surjective coordinate projection to all others. -/
theorem all_coordinates_surjective (L : Subgroup (Wreath P))
    (hroot : L.map SemidirectProduct.rightHom = ⊤)
    (i : Alphabet) (hi : ∀ p : P, ∃ f ∈ basePart L, f i = p) :
    ∀ j : Alphabet, ∀ p : P, ∃ f ∈ basePart L, f j = p := by
  intro j p
  obtain ⟨σ, hσ⟩ := a5_transitive i j
  have hs : σ ∈ L.map SemidirectProduct.rightHom := by rw [hroot]; trivial
  obtain ⟨g, hg, hgr⟩ := hs
  change g.right = σ at hgr
  have hgi : g.right.val⁻¹ j = i := by
    apply g.right.val.injective
    simpa [hgr] using hσ.symm
  obtain ⟨f, hf, hfi⟩ := hi ((g.left j)⁻¹ * p * g.left j)
  refine ⟨_, conj_mem_basePart L g hg f hf, ?_⟩
  simp [hgi, hfi, mul_assoc]

/-- Two-transitivity transports a full projection on one pair to all pairs. -/
theorem all_pairs_surjective (L : Subgroup (Wreath P))
    (hroot : L.map SemidirectProduct.rightHom = ⊤)
    (i j : Alphabet) (hij : i ≠ j)
    (hpair : ∀ p q : P, ∃ f ∈ basePart L, f i = p ∧ f j = q) :
    ∀ k l : Alphabet, k ≠ l → ∀ p q : P,
      ∃ f ∈ basePart L, f k = p ∧ f l = q := by
  intro k l hkl p q
  obtain ⟨σ, hσi, hσj⟩ := a5_pair_transitive i j k l hij hkl
  have hs : σ ∈ L.map SemidirectProduct.rightHom := by rw [hroot]; trivial
  obtain ⟨g, hg, hgr⟩ := hs
  change g.right = σ at hgr
  have hgi : g.right.val⁻¹ k = i := by
    apply g.right.val.injective
    simpa [hgr] using hσi.symm
  have hgj : g.right.val⁻¹ l = j := by
    apply g.right.val.injective
    simpa [hgr] using hσj.symm
  obtain ⟨f, hf, hfi, hfj⟩ :=
    hpair ((g.left k)⁻¹ * p * g.left k) ((g.left l)⁻¹ * q * g.left l)
  refine ⟨_, conj_mem_basePart L g hg f hf, ?_, ?_⟩
  · simp [hgi, hfi, mul_assoc]
  · simp [hgj, hfj, mul_assoc]

/-- The first witness in the base has initial coordinate `u * v`. -/
theorem genAB_fifth_left_zero (u v : P) :
    ((genA u * genB v) ^ 5).left 0 = u * v := by
  simp [pow_succ, rootA, rootB, Equiv.swap_apply_def]

/-- Reversing the second generator gives initial coordinate `u * v⁻¹`. -/
theorem genABinv_fifth_left_zero (u v : P) :
    ((genA u * (genB v)⁻¹) ^ 5).left 0 = u * v⁻¹ := by
  simp [pow_succ, rootA, rootB, Equiv.swap_apply_def]

theorem right_pow (g : Wreath P) (n : ℕ) : (g ^ n).right = g.right ^ n :=
  (SemidirectProduct.rightHom : Wreath P →* A5).map_pow g n

theorem genAB_fifth_right (u v : P) : ((genA u * genB v) ^ 5).right = 1 := by
  rw [right_pow, SemidirectProduct.mul_right, genA_right, genB_right]
  decide

theorem genABinv_fifth_right (u v : P) :
    ((genA u * (genB v)⁻¹) ^ 5).right = 1 := by
  rw [right_pow, SemidirectProduct.mul_right, SemidirectProduct.inv_right,
    genA_right, genB_right]
  decide

/-- The explicit recursive pair generates the entire degree-five wreath
product whenever its sections generate a perfect group and have order dividing three. -/
theorem generates [Group.IsPerfect P] (u v : P)
    (hgen : Subgroup.closure ({u, v} : Set P) = ⊤)
    (_hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    Subgroup.closure ({genA u, genB v} : Set (Wreath P)) = ⊤ := by
  let L := Subgroup.closure ({genA u, genB v} : Set (Wreath P))
  have hx : genA u ∈ L := Subgroup.subset_closure (by simp)
  have hy : genB v ∈ L := Subgroup.subset_closure (by simp)
  have hroot : L.map SemidirectProduct.rightHom = ⊤ := by
    change (Subgroup.closure _).map _ = _
    rw [MonoidHom.map_closure, Set.image_pair]
    exact roots_generate
  let K := basePart L
  let ev (i : Alphabet) : (Alphabet → P) →* P := Pi.evalMonoidHom (fun _ => P) i
  have huv : u * v ∈ K.map (ev 0) := by
    refine ⟨_, ?_, genAB_fifth_left_zero u v⟩
    change SemidirectProduct.inl ((genA u * genB v) ^ 5).left ∈ L
    rw [inl_left_eq _ (genAB_fifth_right u v)]
    exact L.pow_mem (L.mul_mem hx hy) 5
  have huvi : u * v⁻¹ ∈ K.map (ev 0) := by
    refine ⟨_, ?_, genABinv_fifth_left_zero u v⟩
    change SemidirectProduct.inl ((genA u * (genB v)⁻¹) ^ 5).left ∈ L
    rw [inl_left_eq _ (genABinv_fifth_right u v)]
    exact L.pow_mem (L.mul_mem hx (L.inv_mem hy)) 5
  have hvrel : v⁻¹ * v⁻¹ = v := by
    apply mul_left_cancel (a := v * v)
    calc
      (v * v) * (v⁻¹ * v⁻¹) = 1 := by group
      _ = (v * v) * v := by simpa [pow_succ] using hv.symm
  have hvK : v ∈ K.map (ev 0) := by
    have h := (K.map (ev 0)).mul_mem ((K.map (ev 0)).inv_mem huv) huvi
    simpa [mul_inv_rev, mul_assoc, hvrel] using h
  have huK : u ∈ K.map (ev 0) := by
    simpa [mul_assoc] using
      (K.map (ev 0)).mul_mem huv ((K.map (ev 0)).inv_mem hvK)
  have hzero : K.map (ev 0) = ⊤ := by
    apply top_unique
    rw [← hgen]
    rw [Subgroup.closure_le]
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact huK
    · exact hvK
  have hcoord : ∀ i : Alphabet, ∀ p : P, ∃ f ∈ K, f i = p := by
    apply all_coordinates_surjective L hroot 0
    intro p
    have hp : p ∈ K.map (ev 0) := by rw [hzero]; trivial
    exact hp
  let pair : (Alphabet → P) →* P × P := (ev 3).prod (ev 4)
  let Q := K.map pair
  have hfirst : ∀ p : P, ∃ q, (p, q) ∈ Q := by
    intro p
    obtain ⟨f, hf, hfp⟩ := hcoord 3 p
    exact ⟨f 4, f, hf, by simp [pair, ev, hfp]⟩
  have hsecond : ∀ q : P, ∃ p, (p, q) ∈ Q := by
    intro q
    obtain ⟨f, hf, hfq⟩ := hcoord 4 q
    exact ⟨f 3, f, hf, by simp [pair, ev, hfq]⟩
  have hconj : ∀ p q : P, (p, q) ∈ Q → (u * p * u⁻¹, q) ∈ Q := by
    intro p q hpq
    obtain ⟨f, hf, hfpq⟩ := hpq
    have hfp : f 3 = p := congrArg Prod.fst hfpq
    have hfq : f 4 = q := congrArg Prod.snd hfpq
    refine ⟨_, conj_mem_basePart L (genA u) hx f hf, ?_⟩
    ext <;> simp [pair, ev, hfp, hfq, rootA, Equiv.swap_apply_def]
  have hQ : Q = ⊤ := subdirect_eq_top_of_conj_first u v hgen Q hfirst hsecond hconj
  have hpairs : ∀ i j : Alphabet, i ≠ j → ∀ p q : P,
      ∃ f ∈ K, f i = p ∧ f j = q := by
    apply all_pairs_surjective L hroot 3 4 (by decide)
    intro p q
    have hpq : (p, q) ∈ Q := by rw [hQ]; trivial
    obtain ⟨f, hf, hfpq⟩ := hpq
    exact ⟨f, hf, congrArg Prod.fst hfpq, congrArg Prod.snd hfpq⟩
  have hK : K = ⊤ := eq_top_of_pairwise_surjective K hpairs
  apply top_unique
  intro z _
  have hzroot : z.right ∈ L.map SemidirectProduct.rightHom := by rw [hroot]; trivial
  obtain ⟨g, hg, hgr⟩ := hzroot
  change g.right = z.right at hgr
  have hbase : (z * g⁻¹).right = 1 := by simp [hgr]
  have hzbase : SemidirectProduct.inl (z * g⁻¹).left ∈ L := by
    change (z * g⁻¹).left ∈ K
    rw [hK]
    trivial
  rw [inl_left_eq _ hbase] at hzbase
  simpa [mul_assoc] using L.mul_mem hzbase hg

end Wreath

end Kourovka.P21_44

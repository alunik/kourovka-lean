import Kourovka.Problems.P21_03.Proof.YoungConfigurationCount
import Kourovka.Problems.P21_03.Proof.YoungSubgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The consecutive four-block witness

This file constructs the Young subgroup with consecutive blocks of four (and one final
block of size at most three).  It records the sharp linear density of within-block pairs
and packages the corresponding Young subgroup as a soluble subgroup.
-/

namespace Kourovka213

private def fourBlockLabel (n : ℕ) (i : Fin n) : Fin n :=
  ⟨i.1 / 4, lt_of_le_of_lt (Nat.div_le_self _ _) i.2⟩

/-- Consecutive points are put in blocks of four. -/
def fourBlockPartition (n : ℕ) : BoundedPartition n where
  block := fourBlockLabel n
  card_fiber_le_four i := by
    let f : {x : Fin n // fourBlockLabel n x = i} → Fin 4 := fun x =>
      ⟨x.1.1 % 4, Nat.mod_lt _ (by decide)⟩
    simpa using Fintype.card_le_of_injective f (by
      intro x y h
      apply Subtype.ext
      apply Fin.ext
      have hqx : x.1.1 / 4 = i.1 := by
        simpa [fourBlockLabel] using congrArg Fin.val x.2
      have hqy : y.1.1 / 4 = i.1 := by
        simpa [fourBlockLabel] using congrArg Fin.val y.2
      have hr : x.1.1 % 4 = y.1.1 % 4 := congrArg Fin.val h
      omega)

@[simp]
theorem fourBlockPartition_block_val (i : Fin n) :
    (fourBlockPartition n).block i = ⟨i.1 / 4, lt_of_le_of_lt (Nat.div_le_self _ _) i.2⟩ :=
  rfl

private def otherPoint (x : ℕ) (k : Fin 3) : ℕ :=
  4 * (x / 4) + (x % 4 + k.1 + 1) % 4

private theorem otherPoint_lt {q x : ℕ} (hx : x < 4 * q) (k : Fin 3) :
    otherPoint x k < 4 * q := by
  unfold otherPoint
  have hm : (x % 4 + k.1 + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  have hq : x / 4 < q := by omega
  omega

private theorem otherPoint_ne (x : ℕ) (k : Fin 3) : otherPoint x k ≠ x := by
  unfold otherPoint
  have hx := Nat.mod_lt x (by decide : 0 < 4)
  have hk := k.2
  omega

private theorem otherPoint_div_four (x : ℕ) (k : Fin 3) :
    otherPoint x k / 4 = x / 4 := by
  unfold otherPoint
  have hm : (x % 4 + k.1 + 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  omega

private theorem otherPoint_injective_right (x : ℕ) :
    Function.Injective (otherPoint x) := by
  intro k l h
  apply Fin.ext
  unfold otherPoint at h
  have hx := Nat.mod_lt x (by decide : 0 < 4)
  have hk := k.2
  have hl := l.2
  omega

/-- Every point in a complete four-block has three directed partners in its block. -/
private def fullPointPartners (n : ℕ) :
    Fin (4 * (n / 4)) × Fin 3 → (fourBlockPartition n).OrderedPairIn := fun p =>
  let hfull : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  let x : Fin n := ⟨p.1.1, lt_of_lt_of_le p.1.2 hfull⟩
  let y : Fin n := ⟨otherPoint p.1.1 p.2,
    lt_of_lt_of_le (otherPoint_lt p.1.2 p.2) hfull⟩
  { fst := x
    snd := y
    fst_ne_snd := by
      intro h
      exact otherPoint_ne p.1.1 p.2 (congrArg Fin.val h).symm
    same_block := by
      apply Fin.ext
      simpa [fourBlockPartition, fourBlockLabel] using
        (otherPoint_div_four p.1.1 p.2).symm }

private theorem fullPointPartners_injective (n : ℕ) :
    Function.Injective (fullPointPartners n) := by
  intro p q h
  have hfst : p.1 = q.1 := by
    apply Fin.ext
    exact congrArg (fun z => z.fst.1) h
  apply Prod.ext hfst
  apply otherPoint_injective_right p.1.1
  simpa [fullPointPartners, hfst] using congrArg (fun z => z.snd.1) h

/-- The complete blocks already contribute `12 * (n / 4)` directed pairs. -/
theorem twelve_mul_div_four_le_two_mul_pairCount (n : ℕ) :
    12 * (n / 4) ≤ 2 * Fintype.card (fourBlockPartition n).PairIn := by
  have hinj := Fintype.card_le_of_injective (fullPointPartners n)
    (fullPointPartners_injective n)
  have heq := Fintype.card_congr
    (BoundedPartition.pairInProdBoolEquivOrderedPairIn (fourBlockPartition n))
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hinj heq
  omega

/-- The pair count differs from the extremal value `3n/2` by a bounded amount. -/
theorem three_mul_le_two_mul_fourBlock_pairCount_add_nine (n : ℕ) :
    3 * n ≤ 2 * Fintype.card (fourBlockPartition n).PairIn + 9 := by
  have hdiv := twelve_mul_div_four_le_two_mul_pairCount n
  have hmod := Nat.mod_lt n (by decide : 0 < 4)
  omega

/-- Integral two-sided bounds for the consecutive four-block pair count. -/
theorem fourBlock_pairCount_bounds (n : ℕ) :
    3 * n ≤ 2 * Fintype.card (fourBlockPartition n).PairIn + 9 ∧
      2 * Fintype.card (fourBlockPartition n).PairIn ≤ 3 * n :=
  ⟨three_mul_le_two_mul_fourBlock_pairCount_add_nine n,
    (fourBlockPartition n).two_mul_card_pairIn_le_three_mul⟩

/-- Within-block unordered pairs per point for the consecutive four-block partition. -/
noncomputable def fourBlockPairDensity (n : ℕ) : ℝ :=
  Fintype.card (fourBlockPartition n).PairIn / n

/-- Consecutive four-blocks have asymptotic within-block pair density `3/2`. -/
theorem tendsto_fourBlockPairDensity :
    Filter.Tendsto fourBlockPairDensity Filter.atTop (nhds (3 / 2 : ℝ)) := by
  have herr : Filter.Tendsto (fun n : ℕ => (3 / 2 : ℝ) - fourBlockPairDensity n)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ => (9 / 2 : ℝ) / n)
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hu : (2 : ℝ) * Fintype.card (fourBlockPartition n).PairIn ≤ 3 * n := by
        exact_mod_cast (fourBlockPartition n).two_mul_card_pairIn_le_three_mul
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [fourBlockPairDensity]
      apply sub_nonneg.mpr
      apply (div_le_iff₀ hnpos).mpr
      nlinarith
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hl : (3 : ℝ) * n ≤
          2 * Fintype.card (fourBlockPartition n).PairIn + 9 := by
        exact_mod_cast three_mul_le_two_mul_fourBlock_pairCount_add_nine n
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      rw [fourBlockPairDensity]
      rw [show (3 / 2 : ℝ) - Fintype.card (fourBlockPartition n).PairIn / n =
          (3 * n - 2 * Fintype.card (fourBlockPartition n).PairIn) / (2 * n) by
        field_simp]
      rw [div_div]
      exact (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * n)).mpr (by
        nlinarith)
    · simpa [div_div] using
        (tendsto_const_div_atTop_nhds_zero_nat (9 / 2 : ℝ))
  have hconst : Filter.Tendsto (fun _ : ℕ => (3 / 2 : ℝ)) Filter.atTop
      (nhds (3 / 2 : ℝ)) := tendsto_const_nhds
  simpa only [sub_zero] using (hconst.sub herr).congr'
    (Filter.Eventually.of_forall fun n => by ring)

section Solubility

private theorem alternatingFinFour_isSolvable :
    Group.IsSolvable (alternatingGroup (Fin 4)) := by
  let V := alternatingGroup.kleinFour (Fin 4)
  have h4 : Nat.card (Fin 4) = 4 := by simp
  letI : V.Normal := alternatingGroup.normal_kleinFour h4
  letI : IsKleinFour V := alternatingGroup.kleinFour_isKleinFour h4
  have hV : Group.IsSolvable V :=
    Group.isSolvable_of_comm IsKleinFour.isMulCommutative.is_comm.comm
  have hcard : Nat.card (alternatingGroup (Fin 4) ⧸ V) = 3 := by
    rw [← Nat.mul_left_inj (a := Nat.card V)]
    · rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [alternatingGroup.card_of_card_eq_four h4,
        alternatingGroup.kleinFour_card_of_card_eq_four h4]
    rw [alternatingGroup.kleinFour_card_of_card_eq_four h4]
    simp
  have hquot : Group.IsSolvable (alternatingGroup (Fin 4) ⧸ V) :=
    Group.isSolvable_of_comm
      (isCyclic_of_prime_card hcard).isMulCommutative.is_comm.comm
  exact (Group.isSolvable_iff_subgroup_quotient V).mpr ⟨hV, hquot⟩

private theorem permFinFour_isSolvable :
    Group.IsSolvable (Equiv.Perm (Fin 4)) := by
  let A := alternatingGroup (Fin 4)
  have h4 : Nat.card (Fin 4) = 4 := by simp
  letI : A.Normal := inferInstance
  have hA : Group.IsSolvable A := alternatingFinFour_isSolvable
  have hcard : Nat.card (Equiv.Perm (Fin 4) ⧸ A) = 2 := by
    rw [← Nat.mul_left_inj (a := Nat.card A)]
    · rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
      rw [Nat.card_perm, h4, alternatingGroup.card_of_card_eq_four h4]
      norm_num
    rw [alternatingGroup.card_of_card_eq_four h4]
    norm_num
  have hquot : Group.IsSolvable (Equiv.Perm (Fin 4) ⧸ A) :=
    Group.isSolvable_of_comm
      (isCyclic_of_prime_card hcard).isMulCommutative.is_comm.comm
  exact (Group.isSolvable_iff_subgroup_quotient A).mpr ⟨hA, hquot⟩

private theorem isSolvable_fourPi (ι : Type*) :
    Group.IsSolvable (ι → Equiv.Perm (Fin 4)) := by
  obtain ⟨m, hm⟩ := permFinFour_isSolvable
  refine ⟨⟨m, le_antisymm ?_ bot_le⟩⟩
  intro g hg
  rw [Subgroup.mem_bot]
  funext i
  let ev : (ι → Equiv.Perm (Fin 4)) →* Equiv.Perm (Fin 4) :=
    Pi.evalMonoidHom (fun _ : ι => Equiv.Perm (Fin 4)) i
  have hmem : ev g ∈ (derivedSeries (ι → Equiv.Perm (Fin 4)) m).map ev :=
    Subgroup.mem_map_of_mem ev hg
  have hi : ev g ∈ derivedSeries (Equiv.Perm (Fin 4)) m :=
    (map_derivedSeries_le_derivedSeries ev m) hmem
  rw [hm, Subgroup.mem_bot] at hi
  exact hi

/-- Restrict a block-preserving permutation to one fiber. -/
private def youngRestriction (P : BoundedPartition n) (i : Fin n) :
    youngSubgroup P →* Equiv.Perm {x : Fin n // P.block x = i} where
  toFun sigma :=
    { toFun := fun x => ⟨sigma.1 x.1, sigma.2 x.1 |>.trans x.2⟩
      invFun := fun x => ⟨sigma.1⁻¹ x.1, by
        have h := sigma.2 (sigma.1⁻¹ x.1)
        calc
          P.block (sigma.1⁻¹ x.1) = P.block (sigma.1 (sigma.1⁻¹ x.1)) := h.symm
          _ = P.block x.1 := by
            simpa only [Equiv.Perm.coe_inv] using
              congrArg P.block (sigma.1.apply_symm_apply x.1)
          _ = i := x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun x => by
        apply Subtype.ext
        simp }
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' sigma tau := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

private noncomputable def fiberEmbedding (P : BoundedPartition n) (i : Fin n) :
    {x : Fin n // P.block x = i} ↪ Fin 4 :=
  (Fintype.equivFin {x : Fin n // P.block x = i}).toEmbedding.trans
    (Fin.castLEEmb (P.card_fiber_le_four i))

/-- Faithfully record all fiber restrictions inside a product of copies of `S₄`. -/
private noncomputable def youngToFourPi (P : BoundedPartition n) :
    youngSubgroup P →* (Fin n → Equiv.Perm (Fin 4)) :=
  MonoidHom.pi fun i =>
    (Equiv.Perm.viaEmbeddingHom (fiberEmbedding P i)).comp (youngRestriction P i)

private theorem youngToFourPi_injective (P : BoundedPartition n) :
    Function.Injective (youngToFourPi P) := by
  intro sigma tau h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  let i : Fin n := P.block x
  have hi := congrFun h i
  have hr : youngRestriction P i sigma = youngRestriction P i tau :=
    Equiv.Perm.viaEmbeddingHom_injective (fiberEmbedding P i) hi
  have hx := congrArg (fun e : Equiv.Perm {y : Fin n // P.block y = i} => e ⟨x, rfl⟩) hr
  exact congrArg Subtype.val hx

/-- Every Young subgroup whose blocks have size at most four is soluble. -/
theorem isSolvable_youngSubgroup (P : BoundedPartition n) :
    Group.IsSolvable (youngSubgroup P) := by
  letI : Group.IsSolvable (Fin n → Equiv.Perm (Fin 4)) := isSolvable_fourPi (Fin n)
  exact Group.isSolvable_of_isSolvable_injective (youngToFourPi_injective P)

/-- The consecutive four-block Young subgroup, packaged with its solubility proof. -/
def fourBlockSolubleSubgroup (n : ℕ) : SolubleSubgroup n where
  carrier := youngSubgroup (fourBlockPartition n)
  isSolvable := isSolvable_youngSubgroup (fourBlockPartition n)

end Solubility

end Kourovka213

import Kourovka.Problems.P21_38.Proof.EndpointSlopes
import Kourovka.Problems.P21_38.Proof.AbelianizationCriterion
import Kourovka.Problems.P21_38.Proof.SubgroupGeneration
import Kourovka.External.GroupApproximation.GroupTheory.HigmanThompson.CompactRangeB
import Mathlib.Tactic.FinCases

/-!
# Standard generators and the endpoint kernel

Brown's proved presentation and interval conjugacy give ordinary two-generation
of the concrete group `F`. The endpoint vectors then identify its commutator
subgroup by the abstract abelianization criterion.
-/

namespace Kourovka.P21_38

open GroupApproximation.HigmanThompson

/-- Brown's generator, transported to the unit interval. -/
noncomputable def standardGenerator (k : ℕ) : F :=
  ⟨compConjHom 0 1 (xg 0 k), compConj_mem_compactF 0 1 le_rfl (xg_mem_geoF 0 k)⟩

/-- The concrete interval realization of Brown's presented group. -/
noncomputable def brownToInterval : BrownGroup 0 →* F where
  toFun g := ⟨compConjHom 0 1 (brownEval 0 g),
    compConj_mem_compactF 0 1 le_rfl (brownF_le_geoF 0 ⟨g, rfl⟩)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by apply Subtype.ext; simp

theorem brownToInterval_surjective : Function.Surjective brownToInterval := by
  intro g
  obtain ⟨f, hf, hfg⟩ := compactF_le_map 0 1 le_rfl g.property
  rw [geoF_eq_brownF] at hf
  obtain ⟨b, rfl⟩ := hf
  exact ⟨b, Subtype.ext hfg⟩

@[simp] theorem brownToInterval_of (i : Fin 2) :
    brownToInterval (PresentedGroup.of i) = standardGenerator i.val := by
  apply Subtype.ext
  change compConjHom 0 1 (brownEval 0 (PresentedGroup.of i)) = _
  have hi : (PresentedGroup.of i : BrownGroup 0) = brownX 0 i.val := by
    simp [brownX, brownWord_of_lt 0 i.isLt, PresentedGroup.of]
  rw [hi, brownEval_X]
  rfl

/-- The two standard interval generators generate the whole concrete group. -/
theorem standardGenerators_generate : GeneratesPair (standardGenerator 0) (standardGenerator 1) := by
  have hset : Set.range (PresentedGroup.of : Fin 2 → BrownGroup 0) =
      ({PresentedGroup.of 0, PresentedGroup.of 1} : Set (BrownGroup 0)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hx).symm⟩
  have hbase : Subgroup.closure ({PresentedGroup.of 0, PresentedGroup.of 1} :
      Set (BrownGroup 0)) = ⊤ := by
    rw [← hset]
    exact PresentedGroup.closure_range_of _
  have hmap := congrArg (fun S : Subgroup (BrownGroup 0) => S.map brownToInterval) hbase
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr brownToInterval_surjective] at hmap
  simpa [GeneratesPair, Set.image_pair] using hmap

private theorem compE_first_block {u : ℚ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    compE 0 1 u = u / 2 := by
  have h := compE_block 0 1 0 hu0 (by simpa using hu1)
  convert h using 1 <;> norm_num; ring

private theorem compEinv_first_block {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    compEinv 0 1 t = 2 * t := by
  have hE : compE 0 1 (2 * t) = t := by
    rw [compE_first_block (by linarith) (by linarith)]
    ring
  calc
    compEinv 0 1 t = compEinv 0 1 (compE 0 1 (2 * t)) := by rw [hE]
    _ = 2 * t := compEinv_compE 0 1 _

@[simp] theorem leftExponent_standardGenerator_zero :
    leftExponent (standardGenerator 0) = 1 := by
  apply leftExponent_eq
  refine ⟨1 / 4, by norm_num, fun t ht0 ht => ?_⟩
  change compConjHom 0 1 (xg 0 0) t = _
  rw [compConjHom_apply, compConjFun_of_lt 0 1 _ (by norm_num; linarith),
    compEinv_first_block ht0 (by linarith), xg_apply,
    xfun_of_mem (by norm_num; linarith) (by norm_num; linarith)]
  norm_num only [Nat.cast_zero, zero_add, sub_zero, zpow_one]
  rw [compE_first_block (by linarith) (by linarith)]
  ring

@[simp] theorem leftExponent_standardGenerator_one :
    leftExponent (standardGenerator 1) = 0 := by
  apply leftExponent_eq
  refine ⟨1 / 2, by norm_num, fun t ht0 ht => ?_⟩
  change compConjHom 0 1 (xg 0 1) t = _
  rw [compConjHom_apply, compConjFun_of_lt 0 1 _ (by norm_num; linarith),
    compEinv_first_block ht0 ht, xg_apply,
    xfun_of_le (by norm_num; linarith),
    compE_first_block (by linarith) (by linarith)]
  simp

/-- Every Brown generator translates the far end of the half-line by one,
which becomes endpoint exponent `-1` after compactification. -/
@[simp] theorem rightExponent_standardGenerator (k : ℕ) :
    rightExponent (standardGenerator k) = -1 := by
  apply rightExponent_eq
  let c : ℚ := compE 0 1 ((k + 2 : ℕ) : ℚ)
  have hc : c < 1 := compE_lt 0 1 _
  have hT : ∀ t : ℚ, ((k + 1 : ℕ) : ℚ) ≤ t →
      xg 0 k t = t + (1 : ℤ) * ((0 : ℚ) + 1) := by
    intro t ht
    rw [xg_apply, xfun_of_ge (by simpa using ht)]
    norm_num
  refine ⟨1 - c, by linarith, fun t ht ht1 => ?_⟩
  by_cases heq : t = 1
  · subst t
    rw [compactF_fix_one (standardGenerator k).property le_rfl]
    simp
  · have htlt : t < 1 := lt_of_le_of_ne ht1 heq
    have hct : c ≤ t := by linarith
    have hgerm := compConj_near 0 1 le_rfl (k := (1 : ℤ)) hT
      (t := t) (by simpa [c, Nat.add_assoc] using hct) htlt
    change compConjHom 0 1 (xg 0 k) t = _
    calc
      compConjHom 0 1 (xg 0 k) t = 1 - (1 - t) * (2 : ℚ) ^ (-1 : ℤ) := by
        simpa using hgerm
      _ = 1 + (2 : ℚ) ^ (-1 : ℤ) * (t - 1) := by ring

@[simp] theorem endpointCharacter_standardGenerator_zero :
    endpointCharacter (standardGenerator 0) = Multiplicative.ofAdd (1, -1) := by
  simp

@[simp] theorem endpointCharacter_standardGenerator_one :
    endpointCharacter (standardGenerator 1) = Multiplicative.ofAdd (0, -1) := by
  simp

/-- The endpoint character of the concrete Thompson group is its abelianization
map at the level of kernels. -/
theorem endpointCharacter_ker_eq_commutator : endpointCharacter.ker = commutator F :=
  ker_eq_commutator_of_generatesPair_of_signed_basis_images standardGenerators_generate
    endpointCharacter endpointCharacter_standardGenerator_zero endpointCharacter_standardGenerator_one

end Kourovka.P21_38

#audit_axioms Kourovka.P21_38.standardGenerators_generate
#audit_axioms Kourovka.P21_38.endpointCharacter_standardGenerator_zero
#audit_axioms Kourovka.P21_38.endpointCharacter_standardGenerator_one
#audit_axioms Kourovka.P21_38.endpointCharacter_ker_eq_commutator

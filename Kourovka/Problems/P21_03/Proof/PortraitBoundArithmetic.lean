import Kourovka.Problems.P21_03.Proof.SupportError
import Kourovka.Problems.P21_03.Proof.WeightedConfiguration

/-!
# From weighted portrait encodings to support bounds

This is the final arithmetic wrapper for the forest portrait construction.  It
also discharges the exceptional support values where the generic weighted-code
estimate is not applicable.
-/

namespace Kourovka213

universe u

private theorem supportSlice_eq_empty_of_degree_lt
    {n s : ℕ} (H : Subgroup (Sym n)) (hns : n < s) :
    supportSlice H s = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨g, hg⟩
  have hsupport := (mem_supportSlice.mp hg).2
  have hcard : g.support.card ≤ n := by
    simpa using g.support.card_le_univ
  omega

private theorem outsideCoreSlice_eq_empty_of_lt_three
    {n s : ℕ} (H : Subgroup (Sym n)) (hs : s < 3) :
    outsideCoreSlice H s = ∅ := by
  classical
  by_contra hne
  have hnonempty : (outsideCoreSlice H s).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  exact (not_le_of_gt hs) (three_le_of_outsideCoreSlice_nonempty H s hnonempty)

private theorem supportSlice_zero_card_le_one
    {n : ℕ} (H : Subgroup (Sym n)) :
    (supportSlice H 0).card ≤ 1 := by
  classical
  have hsub : supportSlice H 0 ⊆ {1} := by
    intro g hg
    rw [Finset.mem_singleton]
    exact Equiv.Perm.card_support_eq_zero.mp (mem_supportSlice.mp hg).2
  exact (Finset.card_le_card hsub).trans_eq (Finset.card_singleton 1)

/-- Cardinal injections into weighted configuration codes imply the two
cleared-denominator estimates needed by `SupportBoundsFor`. -/
theorem supportBoundsFor_of_weightedConfiguration_encodings
    {n : ℕ} (H : SolubleSubgroup n)
    (Site : Type u) [Fintype Site] [DecidableEq Site]
    (D : ℕ) (hsite : Fintype.card Site ≤ n)
    (hsupport : ∀ s : ℕ, 1 ≤ s → s ≤ n →
      (supportSlice H.carrier s).card ≤
        ∑ k ∈ Finset.range (s / 2 + 1),
          Fintype.card (WeightedConfigurationCode Site D s k))
    (houtside : ∀ s : ℕ, 3 ≤ s → s ≤ n →
      (outsideCoreSlice H.carrier s).card ≤
        ∑ k ∈ Finset.range ((s - 1) / 2 + 1),
          Fintype.card (WeightedConfigurationCode Site D s k)) :
    SupportBoundsFor (16 * D) H := by
  intro s
  constructor
  · by_cases hs0 : s = 0
    · subst s
      simpa using supportSlice_zero_card_le_one H.carrier
    · by_cases hsn : s ≤ n
      · have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
        calc
          (supportSlice H.carrier s).card * s ^ (s / 2) ≤
              (∑ k ∈ Finset.range (s / 2 + 1),
                Fintype.card (WeightedConfigurationCode Site D s k)) *
                  s ^ (s / 2) := Nat.mul_le_mul_right _ (hsupport s hs hsn)
          _ ≤ (16 * D) ^ s * n ^ (s / 2) :=
            sum_card_weightedConfigurationCode_mul_support_pow_le
              Site n s (s / 2) D hsite hs hsn (by omega)
      · have hempty := supportSlice_eq_empty_of_degree_lt H.carrier
          (Nat.lt_of_not_ge hsn)
        simp [hempty]
  · by_cases hs3 : 3 ≤ s
    · by_cases hsn : s ≤ n
      · calc
          (outsideCoreSlice H.carrier s).card * s ^ ((s - 1) / 2) ≤
              (∑ k ∈ Finset.range ((s - 1) / 2 + 1),
                Fintype.card (WeightedConfigurationCode Site D s k)) *
                  s ^ ((s - 1) / 2) :=
            Nat.mul_le_mul_right _ (houtside s hs3 hsn)
          _ ≤ (16 * D) ^ s * n ^ ((s - 1) / 2) :=
            sum_card_weightedConfigurationCode_mul_support_pow_le
              Site n s ((s - 1) / 2) D hsite (by omega) hsn (by omega)
      · have hsuppEmpty := supportSlice_eq_empty_of_degree_lt H.carrier
          (Nat.lt_of_not_ge hsn)
        have houtEmpty : outsideCoreSlice H.carrier s = ∅ := by
          simp [outsideCoreSlice, hsuppEmpty]
        simp [houtEmpty]
    · have houtEmpty := outsideCoreSlice_eq_empty_of_lt_three H.carrier
        (Nat.lt_of_not_ge hs3)
      simp [houtEmpty]

end Kourovka213

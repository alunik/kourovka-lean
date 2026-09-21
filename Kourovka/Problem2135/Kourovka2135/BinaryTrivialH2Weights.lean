import Kourovka2135.BinaryTorusFixedCoordinates

/-! The empty tensor support has no degree-two torus-fixed coordinate when
the binary extension degree is at least three. The arithmetic includes
repeated exponents and is uniform in the extension degree. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTrivialH2Weights

open Finset BinaryWeights BinarySurvivorWeights BinarySurvivorDegree
open BinaryCochainGraded BinaryTorusFixedCoordinates DiagonalFixedCoordinates

private theorem sum_range_binary (f : ℕ) :
    (∑ i ∈ range f, 2 ^ i) = 2 ^ f - 1 := by
  have h : ∀ n : ℕ, (∑ i ∈ range n, 2 ^ i) + 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, pow_succ]
      omega
  have := h f
  omega

/-- Two binary powers cannot sum to zero modulo the odd torus order in
extension degree at least three, even when their exponents coincide. -/
theorem two_terms_not_modEq_zero {f j k : ℕ} (hf : 3 ≤ f) :
    ¬ Nat.ModEq (2 ^ f - 1) 0 (2 ^ j + 2 ^ k) := by
  intro h
  let a := j % f
  let b := k % f
  have ha : a < f := Nat.mod_lt _ (by omega)
  have hb : b < f := Nat.mod_lt _ (by omega)
  have hp : 0 < 2 ^ f - 1 :=
    lt_trans (by positivity : 0 < 2 ^ a) (two_pow_lt_modulus (by omega) ha)
  have hred : Nat.ModEq (2 ^ f - 1) 0 (2 ^ a + 2 ^ b) :=
    h.trans ((two_pow_modEq_reduced f j).add (two_pow_modEq_reduced f k))
  by_cases hab : a = b
  · have hcarry : 2 ^ a + 2 ^ b = 2 ^ (a + 1) := by
      rw [← hab, pow_succ]
      omega
    rw [hcarry] at hred
    have hsingle := hred.trans (two_pow_modEq_reduced f (a + 1))
    have he := hsingle.eq_of_lt_of_lt hp
      (two_pow_lt_modulus (by omega) (Nat.mod_lt _ (by omega)))
    have : 0 < 2 ^ ((a + 1) % f) := by positivity
    omega
  · have hsub : ({a, b} : Finset ℕ) ⊆ range f := by
      intro i hi
      simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact mem_range.mpr ha
      · exact mem_range.mpr hb
    have hle : 2 ^ a + 2 ^ b ≤ 2 ^ f - 1 := by
      simpa only [sum_pair hab] using subsetWeight_le_modulus {a, b} hsub
    have hsum : 2 ^ a + 2 ^ b = 2 ^ f - 1 := by
      by_contra hne
      have hlt : 2 ^ a + 2 ^ b < 2 ^ f - 1 := by omega
      have he := hred.eq_of_lt_of_lt hp hlt
      exact (Nat.ne_of_gt (by positivity : 0 < 2 ^ a + 2 ^ b)) he.symm
    have hset : ({a, b} : Finset ℕ) = range f := by
      apply Finset.geomSum_injective (n := 2) (by decide)
      change (∑ i ∈ ({a, b} : Finset ℕ), 2 ^ i) = ∑ i ∈ range f, 2 ^ i
      rw [sum_pair hab, hsum, sum_range_binary]
    have hc := congrArg Finset.card hset
    simp only [card_pair hab, card_range] at hc
    omega

/-- Empty-support degree-two survivor coordinates have no zero torus weight. -/
theorem isEmpty_zeroWeightIndex {f : ℕ} (hf : 3 ≤ f) :
    IsEmpty (ZeroWeightIndex (∅ : Finset (Fin f)) 2) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨i, j, _, _, he⟩ := survivor_two_exists ∅ a.val
  have hw := a.property
  rw [he, map_add, generatorWeight_single, generatorWeight_single] at hw
  exact two_terms_not_modEq_zero hf (by simpa only [sum_empty] using hw)

variable (k : Type*) [Field k] {f : ℕ}

/-- The actual diagonal torus character has no fixed degree-two coordinate
for empty tensor support. -/
theorem isEmpty_fixedIndex (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 3 ≤ f) :
    IsEmpty (FixedIndex (character k (∅ : Finset (Fin f)) r 2)) := by
  let := isEmpty_zeroWeightIndex hf
  exact ⟨fun a => isEmptyElim (fixedIndexEquiv k ∅ r hr 2 a)⟩

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- Injective cochain coordinates with the proved empty-support characters
force the actual fixed subspace to vanish. -/
theorem fixedSpace_eq_bot (r : kˣ) (hr : orderOf r = 2 ^ f - 1) (hf : 3 ≤ f)
    (T : V →ₗ[k] V) (q : V →ₗ[k] (SurvivorIndex (∅ : Finset (Fin f)) 2 → k))
    (hq : Function.Injective q)
    (hdiag : ∀ v a, q (T v) a = character k ∅ r 2 a * q v a) :
    (T - LinearMap.id).ker = ⊥ := by
  let := isEmpty_fixedIndex k r hr hf
  exact fixedSpace_eq_bot_of_no_weight_one T q (character k ∅ r 2) hq hdiag
    (fun a ha => isEmptyElim (⟨a, ha⟩ : FixedIndex (character k ∅ r 2)))

end Kourovka2135.BinaryTrivialH2Weights

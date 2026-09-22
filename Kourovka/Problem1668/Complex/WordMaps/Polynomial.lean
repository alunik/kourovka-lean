import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Polynomial

namespace WordMaps

/-- Two distinct fibres of a nonconstant polynomial over an algebraically closed
field of characteristic zero cannot both consist entirely of multiple roots. -/
theorem exists_regular_fiber {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (f : K[X]) (hf : f.natDegree ≠ 0) (a b : K) (hab : a ≠ b) :
    ∃ t : K, (f.eval t = a ∨ f.eval t = b) ∧ f.derivative.eval t ≠ 0 := by
  classical
  by_contra! h
  have hnonzero (c : K) : f - C c ≠ 0 := by
    intro hc
    have := congrArg Polynomial.natDegree hc
    exact hf (by simpa only [natDegree_sub_C, natDegree_zero] using this)
  have hroot (c : K) (t : K) : (f - C c).IsRoot t ↔ f.eval t = c := by
    simp only [IsRoot, eval_sub, eval_C, sub_eq_zero]
  have hmult (c : K) (hc : c = a ∨ c = b) (t : K)
      (ht : (f - C c).IsRoot t) :
      (f - C c).rootMultiplicity t ≤ 2 * f.derivative.rootMultiplicity t := by
    have heval : f.eval t = a ∨ f.eval t = b := by
      rcases hc with rfl | rfl
      · exact Or.inl ((hroot _ t).mp ht)
      · exact Or.inr ((hroot _ t).mp ht)
    have hder : (f - C c).derivative.IsRoot t := by
      simpa only [derivative_sub, derivative_C, sub_zero, IsRoot] using h t heval
    have hm := (one_lt_rootMultiplicity_iff_isRoot (hnonzero c)).mpr ⟨ht, hder⟩
    have hd := derivative_rootMultiplicity_of_root ht
    simp only [derivative_sub, derivative_C, sub_zero] at hd
    omega
  have hle : (f - C a).roots + (f - C b).roots ≤
      f.derivative.roots + f.derivative.roots := by
    apply Multiset.le_iff_count.mpr
    intro t
    simp only [Multiset.count_add, count_roots]
    by_cases ha : (f - C a).IsRoot t
    · have hb : ¬ (f - C b).IsRoot t := by
        intro hb
        exact hab (((hroot a t).mp ha).symm.trans ((hroot b t).mp hb))
      rw [rootMultiplicity_eq_zero hb, add_zero]
      simpa only [two_mul] using hmult a (Or.inl rfl) t ha
    · rw [rootMultiplicity_eq_zero ha, zero_add]
      by_cases hb : (f - C b).IsRoot t
      · simpa only [two_mul] using hmult b (Or.inr rfl) t hb
      · simp only [rootMultiplicity_eq_zero hb, Nat.zero_le]
  have hcard := Multiset.card_le_card hle
  have ha := (IsAlgClosed.splits (f - C a)).natDegree_eq_card_roots
  have hb := (IsAlgClosed.splits (f - C b)).natDegree_eq_card_roots
  simp only [natDegree_sub_C] at ha hb
  simp only [Multiset.card_add, ← ha, ← hb] at hcard
  have hbound := Polynomial.card_roots' f.derivative
  have hdegree := Polynomial.natDegree_derivative_lt hf
  omega

end WordMaps

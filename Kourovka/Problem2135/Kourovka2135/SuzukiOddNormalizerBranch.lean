import Kourovka2135.SuzukiSplitGoodSet
import Kourovka2135.SuzukiRootNormalizer
import Kourovka2135.OddNormalizerModelObstruction
import Kourovka2135.MinimalSimpleReduction
import Kourovka2135.BinarySLTwoMinimalException

/-! The actual Suzuki family is excluded for odd-prime least exceptions
with noncentral radical. The torus good set supplies a root-two normalizer
witness; no multiplier or cohomology statement is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiOddNormalizerBranch

open SuzukiTorusMovingRank

theorem exists_split_prime (m : ℕ) (hm : 0 < m) :
    ∃ r, r.Prime ∧ r ∣ SuzukiGeometry.q m - 1 := by
  have hq : 8 ≤ SuzukiGeometry.q m := by
    change 2 ^ 3 ≤ 2 ^ (2 * m + 1)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.exists_prime_and_dvd (by omega)

end Kourovka2135.SuzukiOddNormalizerBranch

namespace Kourovka2135
open SuzukiTorusMovingRank

/-- The concrete Suzuki matrix group, at every positive parameter. -/
theorem OrderMinimalException.false_of_odd_noncentral_suzuki_quotient
    {E : Type*} [Group E] [Finite E] {w : OuterWord} {p : ℕ}
    (h : OrderMinimalException w p E) (hp : p.Prime) (hodd : p ≠ 2)
    (hnoncentral : ¬ solubleRadical E ≤ Subgroup.center E)
    (m : ℕ) (hm : 0 < m) (e : (E ⧸ solubleRadical E) ≃* G m) : False := by
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable hp hnoncentral)
  obtain ⟨r, hr, hd⟩ := SuzukiOddNormalizerBranch.exists_split_prime m hm
  let : Fact r.Prime := ⟨hr⟩
  have hgood := SuzukiSplitGoodSet.isGeneratingGoodSet m hd hsolv
  have hdiv : r ∣ Nat.card (K m)ˣ := by
    rw [Nat.card_units, card_field]
    exact hd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := (K m)ˣ) r hdiv
  have hane : a ≠ 1 := by
    intro he
    exact hr.ne_one (by simpa only [he, orderOf_one] using ha.symm)
  exact h.false_of_odd_model_normalizer_good_set hp Nat.prime_two hodd hodd.symm
    hnoncentral e hgood (SuzukiRootNormalizer.U m) (SuzukiRootNormalizer.isPGroup_U m)
    (torusHom m a) (SuzukiRootNormalizer.rootZero m 1)
    ((orderOf_torus m a).trans ha)
    (SuzukiRootNormalizer.torus_normalizes_U m a)
    ((SuzukiRootNormalizer.mem_U_iff m _).mpr ⟨1, rfl⟩)
    (SuzukiRootNormalizer.double_commutator_ne_one m a hane)

end Kourovka2135

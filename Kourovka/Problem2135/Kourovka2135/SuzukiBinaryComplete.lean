import Kourovka2135.SuzukiEightBinaryNoncentral
import Kourovka2135.BinaryMinimalSimpleReduction

/-! Every actual Suzuki quotient is excluded for a binary least exception.
Thompson supplies proper-subgroup solubility even when the soluble radical
is central. All cover, module and word-value statements are proved inputs. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open SuzukiTorusMovingRank

/-- The large actual quotient exclusion, with no condition on the radical. -/
theorem OrderMinimalException.false_of_binary_large_suzuki_quotient
    {A : Type} [Group A] [Finite A] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 A)
    (m : ℕ) (hm : 2 ≤ m) (e : (A ⧸ solubleRadical A) ≃* G m) : False := by
  let : Group.IsPerfect A := h.isPerfect Nat.prime_two
  let : IsSimpleGroup (A ⧸ solubleRadical A) := h.quotient_radical_isSimple Nat.prime_two
  let : IsSimpleGroup (G m) := e.symm.isSimpleGroup
  have hsolv := proper_subgroups_solvable_of_equiv e
    (h.quotient_radical_proper_subgroup_isSolvable_two classification)
  obtain ⟨r, hr, hrd⟩ := SuzukiOddNormalizerBranch.exists_split_prime m (by omega)
  let : Fact r.Prime := ⟨hr⟩
  let pi := e.toMonoidHom.comp (QuotientGroup.mk' (solubleRadical A))
  have hpi : Function.Surjective pi :=
    e.surjective.comp (QuotientGroup.mk'_surjective (solubleRadical A))
  have hker : pi.ker = solubleRadical A :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (solubleRadical A)) e).trans
      (QuotientGroup.ker_mk' (solubleRadical A))
  have hR : IsPGroup 2 pi.ker := by
    rw [hker, h.radical_eq_pCore Nat.prime_two]
    exact pCore_isPGroup
  have hF : pi.ker ≤ frattini A := by
    rw [hker]
    exact h.radical_le_frattini Nat.prime_two
  exact SuzukiLargeBinaryNoncentral.not_productOrderCondition m hm r hrd hsolv
    pi hpi hR hF w h.condition

/-- All positive Suzuki parameters, without a prime-degree or radical condition. -/
theorem OrderMinimalException.false_of_binary_suzuki_quotient
    {A : Type} [Group A] [Finite A] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 A)
    (m : ℕ) (hm : 0 < m) (e : (A ⧸ solubleRadical A) ≃* G m) : False := by
  by_cases hm1 : m = 1
  · subst m
    exact h.false_of_binary_suzuki_eight_quotient e
  · exact h.false_of_binary_large_suzuki_quotient classification m (by omega) e

end Kourovka2135

import Kourovka2135.GoodSetLifting
import Mathlib.Data.Nat.Factorization.Basic

/-! Prime-to-p elements can be selected in a complete fiber of a finite-group epimorphism. -/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H]

theorem exists_coprime_order_lift_of_surjective
    {p : ℕ} (hp : p.Prime) (f : G →* H) (hf : Function.Surjective f)
    (y : H) (hy : ¬ p ∣ orderOf y) :
    ∃ x : G, f x = y ∧ ¬ p ∣ orderOf x := by
  obtain ⟨a, ha⟩ := hf y
  let e := (orderOf a).factorization p
  have he : p ^ e ∣ orderOf a := Nat.ordProj_dvd _ _
  have horder : orderOf (a ^ p ^ e) = orderOf a / p ^ e := by
    rw [orderOf_pow' a (pow_ne_zero e hp.ne_zero), Nat.gcd_eq_right he]
  have hcoprime : ¬ p ∣ orderOf (a ^ p ^ e) := by
    rw [horder]
    exact Nat.not_dvd_ordCompl hp (orderOf_pos a).ne'
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime
    (((hp.coprime_iff_not_dvd).mpr hy).pow_left e)
  refine ⟨(a ^ p ^ e) ^ k, ?_, ?_⟩
  · rw [map_pow, map_pow, ha]
    exact hk
  · intro hx
    exact hcoprime (hx.trans (orderOf_pow_dvd _))

/-- This uses membership for the whole fiber before choosing an element of coprime order. -/
theorem exists_nontrivial_coprime_value_of_good_preimage
    {p : ℕ} (hp : p.Prime) (f : G →* H) (hf : Function.Surjective f)
    {Y : Set H} (hY : IsGeneratingGoodSet (f ⁻¹' Y))
    {y : H} (hy : y ∈ Y) (hne : y ≠ 1) (hyp : ¬ p ∣ orderOf y)
    (w : OuterWord) :
    ∃ x ∈ w.values G, x ≠ 1 ∧ ¬ p ∣ orderOf x := by
  obtain ⟨x, hx, hxp⟩ := exists_coprime_order_lift_of_surjective hp f hf y hyp
  refine ⟨x, hY.subset_values w ?_, ?_, hxp⟩
  · change f x ∈ Y
    rw [hx]
    exact hy
  · intro h
    apply hne
    rw [← hx, h, map_one]

end Kourovka2135

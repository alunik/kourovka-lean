import Kourovka2135.PSL33OrderObstructions
import Kourovka2135.NormalComplementOperations
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! Complete 21.35 for mathlib's PSL(3, ZMod 3), for every outer word and
every prime. This does not cover its noncentral Frattini extensions. -/

set_option autoImplicit false
namespace Kourovka2135
open scoped MatrixGroups

theorem psl33_card_dvd : Nat.card PSL(3, ZMod 3) ∣ 11232 := by
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) = 11232 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hS := Subgroup.card_dvd_of_injective
    (Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := ZMod 3))
    Matrix.SpecialLinearGroup.toGL_injective
  have hQ := Subgroup.card_quotient_dvd_card (Subgroup.center SL(3, ZMod 3))
  exact hGL ▸ hQ.trans hS

theorem prime_dvd_psl33_card {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card PSL(3, ZMod 3)) : p = 2 ∨ p = 3 ∨ p = 13 := by
  have hn : p ∣ 2 ^ 5 * 3 ^ 3 * 13 := hd.trans psl33_card_dvd
  rcases hp.dvd_mul.mp hn with hn | hn
  · rcases hp.dvd_mul.mp hn with h2 | h3
    · left
      exact ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)).resolve_left hp.ne_one
    · right; left
      exact ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)).resolve_left hp.ne_one
  · right; right
    exact ((Nat.dvd_prime (by decide : Nat.Prime 13)).mp hn).resolve_left hp.ne_one

theorem problem2135_psl33 : Problem2135 PSL(3, ZMod 3) := by
  intro w p hp h
  by_cases hd : p ∣ Nat.card PSL(3, ZMod 3)
  · rcases prime_dvd_psl33_card hp hd with rfl | rfl | rfl
    · exact (PSL33OrderObstructions.not_condition_two w h).elim
    · exact (PSL33OrderObstructions.not_condition_three w h).elim
    · exact (PSL33OrderObstructions.not_condition_thirteen w h).elim
  · have hc := (hp.coprime_iff_not_dvd.mpr hd).symm
    exact HasNormalPComplement.subgroup hp (hasNormalPComplement_of_coprime_card hc)
      (w.verbalSubgroup PSL(3, ZMod 3))

end Kourovka2135

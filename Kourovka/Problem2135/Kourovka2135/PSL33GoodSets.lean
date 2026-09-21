import Kourovka2135.SL33Witnesses
import Kourovka2135.GoodSetImage
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Explicit generating good sets in mathlib's PSL(3, ZMod 3). -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Kourovka2135.PSL33GoodSets
open scoped MatrixGroups
abbrev Q := PSL(3, ZMod 3)
def q : SL33Witnesses.S →* Q := QuotientGroup.mk' _
def y13 : Q := q SL33Witnesses.a13
def y8 : Q := q SL33Witnesses.a8
def Y13 : Set Q := q '' conjugatesOf SL33Witnesses.a13
def Y8 : Set Q := q '' conjugatesOf SL33Witnesses.a8

theorem good13 : IsGeneratingGoodSet Y13 :=
  SL33Witnesses.goodClass13.image_of_surjective q (QuotientGroup.mk'_surjective _)
theorem good8 : IsGeneratingGoodSet Y8 :=
  SL33Witnesses.goodClass8.image_of_surjective q (QuotientGroup.mk'_surjective _)
theorem y13_mem : y13 ∈ Y13 := ⟨_, IsConj.refl _, rfl⟩
theorem y8_mem : y8 ∈ Y8 := ⟨_, IsConj.refl _, rfl⟩

theorem y13_ne_one : y13 ≠ 1 := by
  intro h
  have hc : SL33Witnesses.a13 ∈ Subgroup.center SL33Witnesses.S :=
    (QuotientGroup.eq_one_iff _).mp h
  have he := Subgroup.mem_center_iff.mp hc SL33Witnesses.b13
  exact (by decide : SL33Witnesses.b13 * SL33Witnesses.a13 ≠
    SL33Witnesses.a13 * SL33Witnesses.b13) he

theorem y8_ne_one : y8 ≠ 1 := by
  intro h
  have hc : SL33Witnesses.a8 ∈ Subgroup.center SL33Witnesses.S :=
    (QuotientGroup.eq_one_iff _).mp h
  have he := Subgroup.mem_center_iff.mp hc SL33Witnesses.b8
  exact (by decide : SL33Witnesses.b8 * SL33Witnesses.a8 ≠
    SL33Witnesses.a8 * SL33Witnesses.b8) he

theorem order_y13 : orderOf y13 = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply orderOf_eq_prime ?_ y13_ne_one
  change q SL33Witnesses.a13 ^ 13 = 1
  rw [← map_pow, SL33Witnesses.power13, map_one]

theorem order_y8_dvd : orderOf y8 ∣ 8 := by
  simpa only [y8, SL33Witnesses.order8] using orderOf_map_dvd q SL33Witnesses.a8

theorem exists_generating_good_set_with_coprime_element (p : ℕ) (hp : p.Prime) :
    ∃ Y : Set Q, IsGeneratingGoodSet Y ∧ ∃ y ∈ Y, y ≠ 1 ∧ ¬ p ∣ orderOf y := by
  by_cases htwo : p = 2
  · refine ⟨Y13, good13, y13, y13_mem, y13_ne_one, ?_⟩
    rw [htwo, order_y13]
    decide
  · refine ⟨Y8, good8, y8, y8_mem, y8_ne_one, ?_⟩
    intro hd
    have hd8 : p ∣ 2 ^ 3 := hd.trans order_y8_dvd
    have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow hd8
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with he | he
    · exact hp.ne_one he
    · exact htwo he

end Kourovka2135.PSL33GoodSets

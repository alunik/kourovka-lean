import Kourovka2135.OddPSLTwoSplitDihedral
import Kourovka2135.OddGoodSetTripleObstruction
import Kourovka2135.BinarySplitTorusGoodPair

/-! Explicit even-order iterated commutators for the split order-three classes
in PSL2(F7) and PSL2(F13). Every finite identity uses ordinary kernel reduction.
No subgroup classification or representation hypothesis is used. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SmallOddPSLTwoTripleObstruction
open scoped Matrix
open OddPSLTwoProjectiveChart

private theorem noncentral_of_upper_right {F : Type*} [Field F]
    (g : SLTwo.SL2 F) (h : g.val 0 1 ≠ 0) : g ∉ Subgroup.center (SLTwo.SL2 F) := by
  intro hc
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hr
  apply h
  simpa [Matrix.scalar] using he.symm

namespace Q7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F := ZMod 7
abbrev S := SLTwo.SL2 F
def unit : Fˣ := ⟨2, 4, by decide, by decide⟩
def a : S := SLTwo.tor unit
def z : S := ⟨!![3, 1; 2, 1], by decide⟩
def triple : S := paperCommutator (paperCommutator z a) a
def minusOne : S := ⟨!![6, 0; 0, 6], by decide⟩

theorem minusOne_mem_center : minusOne ∈ Subgroup.center S := by
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by decide, by decide⟩

theorem triple_power_noncentral : triple ^ 1 ∉ Subgroup.center S := by
  apply noncentral_of_upper_right
  decide +kernel

theorem triple_power : triple ^ 2 = minusOne := by decide +kernel

theorem orderOf_projected_power : orderOf ((quotient F triple) ^ 1) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, show 1 * 2 = 2 by decide, ← map_pow, triple_power]
    exact (QuotientGroup.eq_one_iff _).mpr minusOne_mem_center
  · intro h
    apply triple_power_noncentral
    apply (QuotientGroup.eq_one_iff _).mp
    change quotient F (triple ^ 1) = 1
    simpa only [map_pow] using h

theorem two_dvd_orderOf_tripleCommutator :
    2 ∣ orderOf (paperCommutator (paperCommutator (quotient F z) (quotient F a))
      (quotient F a)) := by
  have h := orderOf_pow_dvd (x := quotient F triple) 1
  rw [orderOf_projected_power] at h
  simpa only [triple, paperCommutator, map_mul, map_inv] using h

private theorem cube_roots (v : Fˣ) :
    v ^ 3 = 1 → v ≠ 1 → v = unit ∨ v = unit⁻¹ := by
  revert v
  decide +kernel

theorem isConj_of_mem_splitOrderSet {g : S}
    (hg : g ∈ BinarySplitTorusGoodPair.splitOrderSet (F := F) 3) :
    IsConj (quotient F a) (quotient F g) := by
  obtain ⟨v, hv, hvg⟩ := hg
  have hv3 : v ^ 3 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hvne : v ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hv
    norm_num at hv
  have ha : IsConj a (SLTwo.tor v) := by
    rcases cube_roots v hv3 hvne with rfl | rfl
    · exact IsConj.refl a
    · exact isConj_iff.mpr ⟨OddPSLTwoSplitDihedral.weylSL F,
        OddPSLTwoSplitDihedral.weylSL_conj F unit⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (ha.trans hvg)
  exact isConj_iff.mpr ⟨quotient F c, by
    simpa only [map_mul, map_inv] using congrArg (quotient F) hc⟩

end Q7

namespace Q13
instance : Fact (Nat.Prime 13) := ⟨by decide⟩
abbrev F := ZMod 13
abbrev S := SLTwo.SL2 F
def unit : Fˣ := ⟨3, 9, by decide, by decide⟩
def a : S := SLTwo.tor unit
def z : S := ⟨!![3, 1; 2, 1], by decide⟩
def triple : S := paperCommutator (paperCommutator z a) a
def minusOne : S := ⟨!![12, 0; 0, 12], by decide⟩

theorem minusOne_mem_center : minusOne ∈ Subgroup.center S := by
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by decide, by decide⟩

theorem triple_power_noncentral : triple ^ 3 ∉ Subgroup.center S := by
  apply noncentral_of_upper_right
  decide +kernel

theorem triple_power : triple ^ 6 = minusOne := by decide +kernel

theorem orderOf_projected_power : orderOf ((quotient F triple) ^ 3) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, show 3 * 2 = 6 by decide, ← map_pow, triple_power]
    exact (QuotientGroup.eq_one_iff _).mpr minusOne_mem_center
  · intro h
    apply triple_power_noncentral
    apply (QuotientGroup.eq_one_iff _).mp
    change quotient F (triple ^ 3) = 1
    simpa only [map_pow] using h

theorem two_dvd_orderOf_tripleCommutator :
    2 ∣ orderOf (paperCommutator (paperCommutator (quotient F z) (quotient F a))
      (quotient F a)) := by
  have h := orderOf_pow_dvd (x := quotient F triple) 3
  rw [orderOf_projected_power] at h
  simpa only [triple, paperCommutator, map_mul, map_inv] using h

private theorem cube_roots (v : Fˣ) :
    v ^ 3 = 1 → v ≠ 1 → v = unit ∨ v = unit⁻¹ := by
  revert v
  decide +kernel

theorem isConj_of_mem_splitOrderSet {g : S}
    (hg : g ∈ BinarySplitTorusGoodPair.splitOrderSet (F := F) 3) :
    IsConj (quotient F a) (quotient F g) := by
  obtain ⟨v, hv, hvg⟩ := hg
  have hv3 : v ^ 3 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hvne : v ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hv
    norm_num at hv
  have ha : IsConj a (SLTwo.tor v) := by
    rcases cube_roots v hv3 hvne with rfl | rfl
    · exact IsConj.refl a
    · exact isConj_iff.mpr ⟨OddPSLTwoSplitDihedral.weylSL F,
        OddPSLTwoSplitDihedral.weylSL_conj F unit⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (ha.trans hvg)
  exact isConj_iff.mpr ⟨quotient F c, by
    simpa only [map_mul, map_inv] using congrArg (quotient F) hc⟩

end Q13

end Kourovka2135.SmallOddPSLTwoTripleObstruction

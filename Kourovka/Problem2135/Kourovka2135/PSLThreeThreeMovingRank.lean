import Kourovka2135.RepresentationMovingConjugacy
import Kourovka2135.PSLThreeThreeOddConjugacy
import Kourovka2135.PSL33GoodSets

/-! All order-thirteen elements of the actual PSL3(F3) have the same moving
rank in every finite-dimensional representation. The checked conjugacy cover
reduces them to four coprime powers of `y13`. Thus a computed rank at any
order-thirteen Singer element suffices, without identifying it with `y13`. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeMovingRank

open PSLThreeThreeOddConjugacy PSLThreeThreeOddConjugacyData
open PSLThreeThreeSemidihedralData (projectiveEquiv)
open PSL33GoodSets (y13 order_y13)

theorem orderThirteenExponent_coprime (i : Fin 4) :
    (orderThirteenExponent i).Coprime 13 :=
  (by decide : ∀ j : Fin 4, (orderThirteenExponent j).Coprime 13) i

/-- Every actual order-thirteen element is conjugate to one of the four
already checked coprime powers of the common representative. -/
theorem exists_isConj_y13_pow (g : Q) (hg : orderOf g = 13) :
    ∃ i : Fin 4, IsConj (y13 ^ orderThirteenExponent i) g := by
  let s := projectiveEquiv.symm g
  have hs : orderOf s = 13 := (projectiveEquiv.symm.orderOf_eq g).trans hg
  obtain ⟨j, hj⟩ := conjugacy_cover s
  have hjorder : representativeOrder j = 13 := by
    rw [← representative_order]
    obtain ⟨c, hc⟩ := isConj_iff.mp hj
    exact (SemiconjBy.orderOf_eq c (mul_inv_eq_iff_eq_mul.mp hc)).trans hs
  have hjrange : 3 ≤ j.val ∧ j.val < 7 :=
    (by decide : ∀ l : Fin 12, representativeOrder l = 13 →
      3 ≤ l.val ∧ l.val < 7) j hjorder
  let i : Fin 4 := ⟨j.val - 3, by omega⟩
  have hij : orderThirteenIndex i = j := by
    apply Fin.ext
    dsimp [orderThirteenIndex, i]
    omega
  have hc : IsConj (SL33Witnesses.a13 ^ orderThirteenExponent i) s := by
    rw [← representative_orderThirteen, hij]
    exact hj
  refine ⟨i, ?_⟩
  have hc' := PSL33GoodSets.q.map_isConj hc
  change IsConj (PSL33GoodSets.q (SL33Witnesses.a13 ^ orderThirteenExponent i))
    (projectiveEquiv s) at hc'
  rw [map_pow] at hc'
  change IsConj (y13 ^ orderThirteenExponent i) (projectiveEquiv s) at hc'
  simpa only [s, MulEquiv.apply_symm_apply] using hc'

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V] (ρ : Representation k Q V)

theorem finrank_moving_eq_y13 (g : Q) (hg : orderOf g = 13) :
    Module.finrank k (ρ g - LinearMap.id).range =
      Module.finrank k (ρ y13 - LinearMap.id).range := by
  obtain ⟨i, hi⟩ := exists_isConj_y13_pow g hg
  have hc := RepresentationMovingConjugacy.finrank_moving_eq_of_isConj ρ hi
  have hp := RepresentationMovingConjugacy.finrank_moving_pow_eq ρ y13
    (orderThirteenExponent i) (by
      rw [order_y13]
      exact orderThirteenExponent_coprime i)
  exact hc.symm.trans hp

/-- The computed Singer need only have order thirteen; its matrix need not
be recognized as the fixed representative used by the conjugacy certificate. -/
theorem finrank_moving_eq_of_order_thirteen (g h : Q)
    (hg : orderOf g = 13) (hh : orderOf h = 13) :
    Module.finrank k (ρ g - LinearMap.id).range =
      Module.finrank k (ρ h - LinearMap.id).range :=
  (finrank_moving_eq_y13 ρ g hg).trans (finrank_moving_eq_y13 ρ h hh).symm

end Kourovka2135.PSLThreeThreeMovingRank

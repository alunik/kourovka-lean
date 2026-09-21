import Kourovka2135.PSLThreeThreeOddConjugacyCertificate

/-! The seven explicit odd conjugacy representatives cover every odd-order
element of the actual PSL3(F3). The finite witness checker establishes a full
twelve-representative cover first; exact representative orders remove the five
even-order possibilities. -/
set_option autoImplicit false
namespace Kourovka2135.PSLThreeThreeOddConjugacy
open PSLThreeThreeOddConjugacyData
open PSLThreeThreeSemidihedralData (projectiveEquiv)

def orderThirteenExponent : Fin 4 → ℕ := ![1, 2, 4, 7]
def orderThirteenIndex (i : Fin 4) : Fin 12 := ⟨i.val + 3, by omega⟩

/-- The four order-thirteen representatives are powers of the already
checked generating-good-set element. -/
theorem representative_orderThirteen (i : Fin 4) :
    representative (orderThirteenIndex i) =
      SL33Witnesses.a13 ^ orderThirteenExponent i := by
  exact (by decide : ∀ j : Fin 4,
    representative (orderThirteenIndex j) =
      SL33Witnesses.a13 ^ orderThirteenExponent j) i

theorem conjugacy_cover (g : S) : ∃ i : Fin 12, IsConj (representative i) g := by
  obtain ⟨entry, hentry⟩ :=
    PSLThreeThreeOddConjugacyCertificate.exists_entry (matrixCodeEquiv (g : Mat))
  have hg : (decode (matrixCodeEquiv (g : Mat)).val).det = 1 := by
    rw [decode_code]
    exact g.property
  obtain ⟨hc, he⟩ := hentry hg
  let i : Fin 12 := ⟨entry % 12, Nat.mod_lt _ (by decide)⟩
  let c : S := ⟨decode (entry / 12), hc⟩
  have heq : c * representative i = g * c := by
    apply Subtype.ext
    change decode (entry / 12) * representativeMatrix i = (g : Mat) * decode (entry / 12)
    simpa only [decode_code] using he
  exact ⟨i, isConj_iff.mpr ⟨c, mul_inv_eq_iff_eq_mul.mpr heq⟩⟩

theorem odd_conjugacy_cover (g : S) (hodd : Odd (orderOf g)) :
    ∃ i : Fin 7, IsConj (oddRepresentative i) g := by
  obtain ⟨i, hi⟩ := conjugacy_cover g
  have ho : orderOf (representative i) = orderOf g := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hi
    exact SemiconjBy.orderOf_eq c (mul_inv_eq_iff_eq_mul.mp hc)
  have hi7 : i.val < 7 := (odd_representativeOrder_iff i).mp (by
    rw [← representative_order, ho]
    exact hodd)
  exact ⟨⟨i.val, hi7⟩, hi⟩

noncomputable def representatives (i : Fin 7) : Q := projectiveEquiv (oddRepresentative i)

theorem representatives_order_odd (i : Fin 7) : Odd (orderOf (representatives i)) := by
  have ho := orderOf_injective projectiveEquiv.toMonoidHom projectiveEquiv.injective
    (oddRepresentative i)
  change orderOf (representatives i) = orderOf (oddRepresentative i) at ho
  rw [ho]
  exact oddRepresentative_order_odd i

/-- Exact interface for the generic modular-character counting theorem. -/
theorem projective_odd_conjugacy_cover (g : Q) (hodd : Odd (orderOf g)) :
    ∃ i : Fin 7, IsConj (representatives i) g := by
  let s := projectiveEquiv.symm g
  have hs : Odd (orderOf s) := by
    have ho := orderOf_injective projectiveEquiv.toMonoidHom projectiveEquiv.injective s
    change orderOf (projectiveEquiv s) = orderOf s at ho
    have hg : projectiveEquiv s = g := projectiveEquiv.apply_symm_apply g
    rw [hg] at ho
    exact ho ▸ hodd
  obtain ⟨i, hi⟩ := odd_conjugacy_cover s hs
  refine ⟨i, ?_⟩
  have h := projectiveEquiv.toMonoidHom.map_isConj hi
  change IsConj (representatives i) (projectiveEquiv s) at h
  have hg : projectiveEquiv s = g := projectiveEquiv.apply_symm_apply g
  exact hg ▸ h

end Kourovka2135.PSLThreeThreeOddConjugacy

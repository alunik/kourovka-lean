import Kourovka2135.MinimalFrattini
import Mathlib.GroupTheory.SchurZassenhaus

/-! The fixed prime divides the simple quotient of a smallest exception. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.dvd_card_quotient_radical
    (h : OrderMinimalException w p G) (hp : p.Prime) :
    p ∣ Nat.card (G ⧸ solubleRadical G) := by
  let : Fact p.Prime := ⟨hp⟩
  let R := solubleRadical G
  by_contra hnd
  have hprime : p.Coprime R.index := by
    rw [R.index_eq_card]
    exact hp.coprime_iff_not_dvd.mpr hnd
  have hP : IsPGroup p R := by
    change IsPGroup p (solubleRadical G)
    rw [h.radical_eq_pCore hp]
    exact pCore_isPGroup
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hcop : (Nat.card R).Coprime R.index := by
    rw [hn]
    exact hprime.pow_left n
  obtain ⟨H, hH⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have htop : H = ⊤ := h.radical_nongenerating hp H hH.sup_eq_top
  have hindex : R.index = Nat.card G := by
    simpa only [htop, Subgroup.card_top] using hH.index_eq_card
  have hGcop : (Nat.card G).Coprime p := by
    rw [hindex] at hprime
    exact hprime.symm
  exact h.failure ((hasNormalPComplement_of_coprime_card hGcop).subgroup hp
    (w.verbalSubgroup G))

end Kourovka2135

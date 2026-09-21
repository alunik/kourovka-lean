import Kourovka2135.BinarySplitSylow
import Kourovka2135.BinarySplitTorusGoodPair
import Kourovka2135.FocalLift

/-! Actual conjugacy into the split torus at odd split primes.

A subgroup of prime-to-r index contains a Sylow r-subgroup. Conjugating
an actual r-element into that Sylow subgroup gives an actual torus
parameter with the same order. No matrix or subgroup classification is
used. The order-three, four-element-field endpoint does not need a
separate characteristic-two assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SplitTorusPrimeConjugacy

section Generic

variable {G : Type*} [Group G] [Finite G]
variable {r : ℕ} [Fact r.Prime]

/-- Every r-element is conjugate into any subgroup of r-prime index. -/
theorem exists_conj_mem_of_not_dvd_index
    (H : Subgroup G) (hindex : ¬ r ∣ H.index) (x : G)
    (hx : ∃ k : ℕ, orderOf x = r ^ k) :
    ∃ c : G, c * x * c⁻¹ ∈ H := by
  let Q : Sylow r H := Sylow.nonempty.some
  let T : Subgroup G := (Q : Subgroup H).map H.subtype
  have hT : IsPGroup r T := Q.isPGroup'.map H.subtype
  have hTindex : ¬ r ∣ T.index := by
    dsimp [T]
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul Q.not_dvd_index hindex
  let P : Sylow r G := hT.toSylow hTindex
  obtain ⟨c, hc⟩ := FocalLift.exists_conj_mem_sylow P hx
  have hcT : c * x * c⁻¹ ∈ T := hc
  obtain ⟨y, _, hy⟩ := hcT
  exact ⟨c, hy ▸ y.property⟩

end Generic

section SplitTorus

variable {F : Type*} [Field F] [Finite F]
variable {r : ℕ} [Fact r.Prime]

/-- An actual prime-power-order element at an odd split prime has an actual
diagonal-torus conjugate, with its element order preserved. -/
theorem exists_torus_isConj
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (g : SLTwo.SL2 F) (hg : ∃ k : ℕ, orderOf g = r ^ k) :
    ∃ u : Fˣ, orderOf u = orderOf g ∧ IsConj (SLTwo.tor u) g := by
  obtain ⟨c, hc⟩ := exists_conj_mem_of_not_dvd_index (SLTwo.Torus F)
    (BinarySplitSylow.not_dvd_index_torus F hrOdd hrSplit) g hg
  obtain ⟨u, hu⟩ := hc
  change SLTwo.tor u = c * g * c⁻¹ at hu
  refine ⟨u, ?_, isConj_iff.mpr ⟨c⁻¹, ?_⟩⟩
  · calc
      orderOf u = orderOf (SLTwo.tor u) :=
        (BinarySplitTorusGoodPair.orderOf_tor u).symm
      _ = orderOf g := by
        rw [hu]
        exact (MulAut.conj c).orderOf_eq g
  · rw [hu]
    group

/-- At an odd split prime, every element of that prime order belongs to
the actual conjugacy-defined split-order set. -/
theorem mem_splitOrderSet_of_orderOf
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (g : SLTwo.SL2 F) (hg : orderOf g = r) :
    g ∈ BinarySplitTorusGoodPair.splitOrderSet r := by
  obtain ⟨u, hu, hconj⟩ := exists_torus_isConj hrOdd hrSplit g
    ⟨1, by simpa only [pow_one] using hg⟩
  exact ⟨u, hu.trans hg, hconj⟩

/-- The split-order set is precisely the set of prime-order elements
under the actual odd split-prime arithmetic hypotheses. -/
theorem mem_splitOrderSet_iff_orderOf
    (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1) (g : SLTwo.SL2 F) :
    g ∈ BinarySplitTorusGoodPair.splitOrderSet r ↔ orderOf g = r :=
  ⟨BinarySplitTorusGoodPair.orderOf_mem_splitOrderSet,
    mem_splitOrderSet_of_orderOf hrOdd hrSplit g⟩

/-- Every order-three element of SL2 over a four-element field is an
actual conjugate of a split-torus parameter of order three. -/
theorem mem_splitOrderSet_three_of_card_four
    (hcard : Nat.card F = 4) (g : SLTwo.SL2 F) (hg : orderOf g = 3) :
    g ∈ BinarySplitTorusGoodPair.splitOrderSet 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact mem_splitOrderSet_of_orderOf (by decide) (by rw [hcard]) g hg

end SplitTorus

/-- Fintype-cardinality adapter for the actual four-element-field models. -/
theorem mem_splitOrderSet_three_of_fintype_card_four
    {F : Type*} [Field F] [Fintype F]
    (hcard : Fintype.card F = 4) (g : SLTwo.SL2 F) (hg : orderOf g = 3) :
    g ∈ BinarySplitTorusGoodPair.splitOrderSet 3 :=
  mem_splitOrderSet_three_of_card_four
    (by simpa only [Nat.card_eq_fintype_card] using hcard) g hg

end Kourovka2135.SplitTorusPrimeConjugacy

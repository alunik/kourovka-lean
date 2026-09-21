import Kourovka2135.BinaryFourMinimalException
import Kourovka2135.OddPSLTwoAllMinimalBranches
import Kourovka2135.PSLThreeThreeBinaryBranch

/-! After the actual linear-group branch proofs, a least binary exception
can only have a Suzuki radical quotient. This is a reduction, not the full
Kourovka endpoint. Thompson's statement remains an explicit parameter. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135
open BenderSuzuki.MatrixGroups

theorem OrderMinimalException.exists_suzuki_quotient_two
    {G : Type} [Group G] [Finite G] {w : OuterWord}
    (classification : MinimalSimpleClassification.{0})
    (h : OrderMinimalException w 2 G) :
    ∃ m : ℕ, 0 < m ∧ (2 * m + 1).Prime ∧
      Nonempty ((G ⧸ solubleRadical G) ≃* SuzukiMatrixGroup m) := by
  have hmodel := h.radical_quotient_has_classified_model_two classification
  rcases hmodel with heven | hthree | hprime | hsuzuki | hthreeThree
  · obtain ⟨f, hf, ⟨e⟩⟩ := heven
    let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
      simpa only [Nat.card_eq_fintype_card] using GaloisField.card 2 f hf.ne_zero
    exact (h.false_of_binary_pslTwo_quotient_of_two_le classification f hcard hf.two_le e).elim
  · exact (h.false_of_binary_odd_pslTwo_model_quotient classification (Or.inl hthree)).elim
  · exact (h.false_of_binary_odd_pslTwo_model_quotient classification (Or.inr hprime)).elim
  · exact hsuzuki
  · obtain ⟨e⟩ := hthreeThree
    exact (h.false_of_binary_pslThreeThree_quotient_complete e).elim

end Kourovka2135

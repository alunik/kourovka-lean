import Kourovka2135.SLTwoFiveReflectorData
import Kourovka2135.SLTwoFiveGoodSet

/-! The explicit SL2(F5) reflector has persistent order-six inputs whose
projective images generate the actual point stabilizer L. The short finite
word list certifies generation; no subgroup-recognition premise is used. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section

namespace Kourovka2135.SLTwoFiveReflector

open SLTwoFiveAlternating SLTwoFiveReflectorData A5RelativeModuleCertificate

/-- Positive words in the two projective three-cycles. -/
def projectiveLetter : Fin 2 → A5 := ![projectiveB, w]

def projectiveEval : List (Fin 2) → A5
  | [] => 1
  | i :: word => projectiveLetter i * projectiveEval word

/-- These twelve words cover precisely the point stabilizer. -/
def stabilizerWords : Fin 12 → List (Fin 2) :=
  ![[], [0, 0, 1, 0], [0, 1], [0, 1, 1], [1, 1], [0, 0, 1, 1],
    [1], [0, 0], [0, 1, 0], [1, 0], [0], [0, 0, 1]]

theorem stabilizer_word_certificate : ∀ g : A5, g ∈ L →
    ∃ i : Fin 12, projectiveEval (stabilizerWords i) = g := by
  change ∀ g : A5, g.val (2 : Fin 5) = 2 →
    ∃ i : Fin 12, projectiveEval (stabilizerWords i) = g
  decide

theorem projectiveEval_mem (H : Subgroup A5) (hb : projectiveB ∈ H) (hc : w ∈ H)
    (word : List (Fin 2)) : projectiveEval word ∈ H := by
  induction word with
  | nil => exact H.one_mem
  | cons i word ih =>
    apply H.mul_mem _ ih
    fin_cases i
    · exact hb
    · exact hc

/-- The actual images of the two order-six inputs generate L. -/
theorem images_closure_eq_L :
    Subgroup.closure ({toAlternating b, toAlternating c} : Set A5) = L := by
  rw [toAlternating_b, toAlternating_c]
  apply le_antisymm
  · apply (Subgroup.closure_le L).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact projectiveB_mem_L
    · have : g = w := Set.mem_singleton_iff.mp hg
      subst g
      exact w_mem_L
  · intro g hg
    obtain ⟨i, hi⟩ := stabilizer_word_certificate g hg
    rw [← hi]
    exact projectiveEval_mem _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _

/-- Both actual inputs lie in the checked persistent good set. -/
theorem b_mem_goodSet : b ∈ SLTwoFiveGoodSet.Y :=
  SLTwoFiveGoodSet.mem_of_order_six b orderOf_b

theorem c_mem_goodSet : c ∈ SLTwoFiveGoodSet.Y :=
  SLTwoFiveGoodSet.mem_of_order_six c orderOf_c

/-- The complete finite base reflector, using the fixed u,t,L data. -/
theorem base_reflector :
    ∃ uE a b c : S,
      orderOf uE = 3 ∧ toAlternating uE = u ∧
      toAlternating a = t ∧ a⁻¹ * uE * a = uE⁻¹ ∧
      a = paperCommutator b c ∧
      orderOf b = 6 ∧ orderOf c = 6 ∧
      b ∈ SLTwoFiveGoodSet.Y ∧ c ∈ SLTwoFiveGoodSet.Y ∧
      toAlternating b ∈ L ∧ toAlternating c ∈ L ∧
      Subgroup.closure ({toAlternating b, toAlternating c} : Set A5) = L :=
  ⟨uE, a, b, c, orderOf_uE, toAlternating_uE, toAlternating_a,
    a_inv_conjugates_uE, a_eq_commutator, orderOf_b, orderOf_c,
    b_mem_goodSet, c_mem_goodSet, image_b_mem_L, image_c_mem_L,
    images_closure_eq_L⟩

end Kourovka2135.SLTwoFiveReflector

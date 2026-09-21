import Kourovka2135.SLTwoEqualTracePair
import Kourovka2135.SLTwoTraceGoodSetProjective
import Kourovka2135.SLTwoRegularTraceConjugacy
import Kourovka2135.SLTwoPrimeUnipotentPowers

/-! The actual auxiliary generating pair for every member of the broad
projective trace set. Regular outputs use determinant-one conjugacy;
unipotent outputs use prime-field Sylow conjugacy to powers. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SLTwoTracePowerPair
open SLTwoEqualTracePair SLTwoTraceGoodSetProjective OddPSLTwoProjectiveChart
variable {F : Type*} [Field F] [Finite F]

theorem exists_generating_powers (hp : (Nat.card F).Prime) (hodd : Odd (Nat.card F))
    (s : Fˣ) (hs : (s : F) + 1 ≠ 0) (hns : ¬ IsSquare (s : F))
    (hgen : ∀ g : SLTwo.SL2 F, g.val 0 1 ≠ 0 → g.val 1 0 ≠ 0 →
      g.val 0 0 ≠ 0 ∨ g.val 1 1 ≠ 0 →
      Subgroup.closure ({SLTwo.tor s, g} : Set (SLTwo.SL2 F)) = ⊤)
    (c : Q F) (hc : c ∈ projectiveGoodSet) :
    ∃ α β : Q F, Subgroup.closure ({α, β} : Set (Q F)) = ⊤ ∧
      ∃ m n : ℕ, IsConj α (c ^ m) ∧ IsConj β (c ^ n) := by
  obtain ⟨C, hC, rfl⟩ := hc
  let t := C.val.trace
  have hleft : (left s t).val.trace = C.val.trace := trace_left s hs t
  have hright : (right s t).val.trace = C.val.trace := trace_right s hs t
  refine ⟨quotient F (left s t), quotient F (right s t), ?_, ?_⟩
  · rw [← Set.image_pair, ← MonoidHom.map_closure,
      generates_of_matrix_criterion s hs hns hgen t hC.2.2]
    exact Subgroup.map_top_of_surjective (quotient F) (QuotientGroup.mk'_surjective _)
  · by_cases hreg : C.val.trace ^ 2 ≠ 4
    · have hl := SLTwoRegularTraceConjugacy.isConj_of_trace hodd (left s t) C hleft
        (by rwa [hleft])
      have hr := SLTwoRegularTraceConjugacy.isConj_of_trace hodd (right s t) C hright
        (by rwa [hright])
      exact ⟨1, 1, by simpa only [pow_one] using (quotient F).map_isConj hl,
        by simpa only [pow_one] using (quotient F).map_isConj hr⟩
    · have ht : C.val.trace = 2 ∨ C.val.trace = -2 := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        simpa only [show (2 : F) ^ 2 = 4 by ring] using not_ne_iff.mp hreg
      obtain ⟨m, hm⟩ := SLTwoPrimeUnipotentPowers.exists_projective_isConj_pow hp
        C (left s t) hC.1 (left_nonscalar s t) ht (by rwa [hleft])
      obtain ⟨n, hn⟩ := SLTwoPrimeUnipotentPowers.exists_projective_isConj_pow hp
        C (right s t) hC.1 (right_nonscalar s t) ht (by rwa [hright])
      exact ⟨m, n, hm.symm, hn.symm⟩

end Kourovka2135.SLTwoTracePowerPair

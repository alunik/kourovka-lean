import Kourovka2135.OddGeneratingGoodSet
import Kourovka2135.CoprimePGroupLift
import Kourovka2135.ConjugateCommutatorCorrection

/-! Actual order-preserving terminal good-set lifting. The two visible local
inputs are correction-fiber nonemptiness and quotient-difference surjectivity.
Conjugation removes the central factors and retains the original input orders.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135

theorem hasOddGeneratingGoodSetOver_of_conjugate_fibers
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) (hNΦ : N ≤ frattini G)
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (r : ℕ) (hr : Odd r)
    (B : Set (G ⧸ N)) (hB : IsGeneratingGoodSet B) (hBne : B.Nonempty)
    (horder : ∀ s ∈ B, orderOf s = r)
    (hdiff : ∀ a : G, QuotientGroup.mk' N a ∈ B →
      Function.Surjective (ConjugateCommutatorCorrection.quotientDifference N a))
    (hfiber : ∀ a b : G, Subgroup.closure ({a, b} : Set G) = ⊤ → ∀ n : N,
      QuotientGroup.mk' N (paperCommutator a b * (n : G)) ∈ B →
      orderOf (paperCommutator a b * (n : G)) = r →
      ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) =
        paperCommutator a b * (n : G)) :
    HasOddGeneratingGoodSetOver (QuotientGroup.mk' N) B := by
  let q := QuotientGroup.mk' N
  let Y : Set G := {g | q g ∈ B ∧ orderOf g = r}
  have hlift (s : G ⧸ N) (hs : s ∈ B) :
      ∃ a : G, q a = s ∧ orderOf a = r := by
    obtain ⟨a, ha, ho⟩ := exists_order_preserving_lift_of_pgroup
      Nat.prime_two N hN s (by rw [horder s hs]; exact hr.not_two_dvd_nat)
    exact ⟨a, ha, ho.trans (horder s hs)⟩
  refine ⟨Y, ?_, fun _ hg => hg.1, ?_⟩
  · intro t ht
    obtain ⟨s, hs, z, hz, hsz, hgen⟩ := hB (q t) ht.1
    obtain ⟨a, ha, hoa⟩ := hlift s hs
    obtain ⟨b, hb, hob⟩ := hlift z hz
    have habgen : Subgroup.closure ({a, b} : Set G) = ⊤ := by
      apply closure_pair_eq_top_of_quotient_generation N hNΦ
      change Subgroup.closure ({q a, q b} : Set (G ⧸ N)) = ⊤
      rw [ha, hb]
      exact hgen
    have himage : q (paperCommutator a b) = q t := by
      simpa only [paperCommutator, map_mul, map_inv, ha, hb] using hsz
    have hn : (paperCommutator a b)⁻¹ * t ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((paperCommutator a b)⁻¹ * t) = 1
      rw [map_mul, map_inv, himage, inv_mul_cancel]
    let n : N := ⟨(paperCommutator a b)⁻¹ * t, hn⟩
    have htarget : paperCommutator a b * (n : G) = t := by
      exact mul_inv_cancel_left _ _
    have hcorrection : ∃ u v : N,
        paperCommutator (a * (u : G)) (b * (v : G)) = t := by
      simpa only [htarget] using hfiber a b habgen n
        (by rw [htarget]; exact ht.1) (by rw [htarget]; exact ht.2)
    obtain ⟨a', b', hab', hoa', hob', hqa', hqb'⟩ :=
      ConjugateCommutatorCorrection.exists_inputs_of_corrections N hZ a b t
        (hdiff a (by change q a ∈ B; rw [ha]; exact hs))
        (hdiff b (by change q b ∈ B; rw [hb]; exact hz)) hcorrection
    refine ⟨a', ⟨?_, hoa'.trans hoa⟩, b', ⟨?_, hob'.trans hob⟩, hab', ?_⟩
    · rw [hqa', ha]
      exact hs
    · rw [hqb', hb]
      exact hz
    · apply closure_pair_eq_top_of_quotient_generation N hNΦ
      change Subgroup.closure ({q a', q b'} : Set (G ⧸ N)) = ⊤
      rw [hqa', hqb', ha, hb]
      exact hgen
  · obtain ⟨s, hs⟩ := hBne
    obtain ⟨a, ha, ho⟩ := hlift s hs
    refine ⟨a, ⟨?_, ho⟩, ?_⟩
    · rw [ha]
      exact hs
    · rw [ho]
      exact hr

end Kourovka2135

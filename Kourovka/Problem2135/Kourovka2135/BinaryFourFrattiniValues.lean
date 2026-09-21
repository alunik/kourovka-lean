import Kourovka2135.BinaryFourCoverUniversalValues
import Kourovka2135.BinaryFourCentralCoverModels

/-! Order-three universal values through every binary Frattini kernel over
SL2(4). The canonical central quotient is classified by the proved actual
central-extension comparison, and both concrete models are discharged. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFourFrattiniValues

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable [IsSimpleGroup (SLTwo.SL2 F)]

/-- Every such cover has one actual order-three element that is a single value of every outer word. -/
theorem exists_order_three_universal_value
    (hcard : Fintype.card F = 4)
    (hsolv : ∀ H : Subgroup (SLTwo.SL2 F), H < ⊤ → Group.IsSolvable H)
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hR : IsPGroup 2 pi.ker) (hF : pi.ker ≤ frattini G) :
    ∃ x : G, orderOf x = 3 ∧ ∀ w : OuterWord, x ∈ w.values G := by
  let J := ⁅pi.ker, (⊤ : Subgroup G)⁆
  have hJR : J ≤ pi.ker := Subgroup.commutator_le_left _ _
  let q := QuotientGroup.mk' J
  let pi' := QuotientGroup.lift J pi hJR
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective J
  have hpi' : Function.Surjective pi' :=
    QuotientGroup.lift_surjective_of_surjective J pi hpi hJR
  have hpk : pi'.ker = pi.ker.map q := QuotientGroup.ker_lift J pi hJR
  have hRp : IsPGroup 2 pi'.ker := by
    rw [hpk]
    exact hR.map q
  have hcentral : pi'.ker ≤ Subgroup.center (G ⧸ J) := by
    apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
    rw [hpk, ← Subgroup.map_top_of_surjective q hq, ← Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff J).mpr
    rw [QuotientGroup.ker_mk']
  let e := QuotientGroup.quotientKerEquivOfSurjective pi' hpi'
  rcases BinaryFourCentralCoverModels.quotient_or_matrix_cover pi'.ker hRp hcentral
      e.symm hcard with hs | hd
  · obtain ⟨j⟩ := hs
    let f := j.toMonoidHom.comp q
    have hf : Function.Surjective f := j.surjective.comp hq
    have hfk : f.ker = J := by
      exact (MonoidHom.ker_mulEquiv_comp q j).trans (QuotientGroup.ker_mk' J)
    apply BinaryFourCoverUniversalValues.of_split_cover hcard pi hpi hR hF hsolv f hf
    · rw [hfk]
      exact hJR
    · rw [hfk]
      exact commutator_top_idempotent_of_isPerfect pi.ker
  · obtain ⟨j, hj⟩ := hd
    let f := j.toMonoidHom.comp q
    have hf : Function.Surjective f := j.surjective.comp hq
    have hfk : f.ker = J := by
      exact (MonoidHom.ker_mulEquiv_comp q j).trans (QuotientGroup.ker_mk' J)
    apply BinaryFourCoverUniversalValues.of_double_cover hcard pi hpi hR hF f hf
    · apply MonoidHom.ext
      intro g
      exact hj (q g)
    · rw [hfk]
      exact commutator_top_idempotent_of_isPerfect pi.ker

end Kourovka2135.BinaryFourFrattiniValues

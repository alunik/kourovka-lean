import Kourovka2135.MinimalRankCommutatorFiber

/-! The correction operators' group commutator is exactly the action of
the original group commutator. Thus the rank criterion is on the desired output. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped IsMulCommutative
variable {G : Type*} [Group G]

theorem paperCommutator_inverse_correction_pair (a b : G) :
    paperCommutator (a * paperCommutator a b)⁻¹ ((paperCommutator a b)⁻¹ * b)⁻¹ =
      paperCommutator a b := by
  simp only [paperCommutator]
  group

theorem center_correction_operator_commutator
    (N : Subgroup G) [N.Normal] [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    (a b : G) :
    let d := centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
      (a * paperCommutator a b)⁻¹)
    let e := centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
      ((paperCommutator a b)⁻¹ * b)⁻¹)
    (d.symm * e.symm * d * e).toLinearMap =
      normalQuotientRepresentation N (Subgroup.center N) 2 (paperCommutator a b) := by
  dsimp only
  let c := paperCommutator a b
  let d₀ := a * c
  let e₀ := c⁻¹ * b
  let ρ := normalQuotientRepresentation N (Subgroup.center N) 2
  let d := centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N) d₀⁻¹)
  let e := centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N) e₀⁻¹)
  have hd (x : Additive (N ⧸ Subgroup.center N)) : d.symm x = ρ d₀ x := by
    apply d.injective
    rw [d.apply_symm_apply]
    change x = ρ d₀⁻¹ (ρ d₀ x)
    exact (ρ.inv_self_apply d₀ x).symm
  have he (x : Additive (N ⧸ Subgroup.center N)) : e.symm x = ρ e₀ x := by
    apply e.injective
    rw [e.apply_symm_apply]
    change x = ρ e₀⁻¹ (ρ e₀ x)
    exact (ρ.inv_self_apply e₀ x).symm
  have hg : d₀ * e₀ * d₀⁻¹ * e₀⁻¹ = c := by
    dsimp only [d₀, e₀, c]
    have h := paperCommutator_inverse_correction_pair a b
    simpa only [paperCommutator, inv_inv] using h
  apply LinearMap.ext
  intro x
  change (d.symm * e.symm * d * e) x = ρ c x
  simp only [LinearEquiv.mul_apply, hd, he]
  change ρ d₀ (ρ e₀ (ρ d₀⁻¹ (ρ e₀⁻¹ x))) = ρ c x
  simpa only [map_mul, Module.End.mul_apply] using congrArg (fun g : G => ρ g x) hg

theorem correction_operator_finrank_eq_output_moving_rank
    (N : Subgroup G) [N.Normal] [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    (a b : G) :
    Module.finrank (ZMod 2) (BinaryCorrection.operatorCommutator
      (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
        (a * paperCommutator a b)⁻¹))
      (centerActionLinearEquiv ((MulAut.conjNormal : G →* MulAut N)
        ((paperCommutator a b)⁻¹ * b)⁻¹))).range =
      Module.finrank (ZMod 2)
        (normalQuotientRepresentation N (Subgroup.center N) 2 (paperCommutator a b) -
          LinearMap.id).range := by
  rw [BinaryCorrection.operatorCommutator_finrank_range_eq_commutator_sub_id,
    center_correction_operator_commutator]

theorem exists_paperCommutator_mul_eq_of_minimal_moving_rank
    [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    [IsElementaryAbelian 2 (N ⧸ commutator N)]
    [IsElementaryAbelian 2 (commutator N)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hrank : 2 * Module.finrank (ZMod 2) (Additive (commutator N)) +
      2 * (Module.finrank (ZMod 2) (Additive (N ⧸ commutator N)) -
        Module.finrank (ZMod 2) (Additive (N ⧸ Subgroup.center N))) ≤
      Module.finrank (ZMod 2)
        (normalQuotientRepresentation N (Subgroup.center N) 2 (paperCommutator a b) -
          LinearMap.id).range) (t : N) :
    ∃ u v : N, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  apply exists_paperCommutator_mul_eq_of_minimal_rank N hN hmin hnonabelian a b hgen _ t
  rwa [correction_operator_finrank_eq_output_moving_rank]

end Kourovka2135

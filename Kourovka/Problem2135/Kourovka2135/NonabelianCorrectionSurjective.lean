import Kourovka2135.NonabelianCorrectionLinear

/-! Surjectivity of the actual linear correction on a moving characteristic
abelian quotient. No finiteness assumption is needed. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative commutatorElement
open AbelianDifference
variable {G : Type u} [Group G]

/-- If `[N,G] = N`, ambient conjugation moves every abelian characteristic
quotient of `N` onto itself. -/
theorem iSup_normalQuotient_moving_eq_top
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    [IsMulCommutative (N ⧸ K)] (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N) :
    (⨆ g : G, movingSubgroup (normalQuotientAut N K g)) = ⊤ := by
  let q := QuotientGroup.mk' K
  let ρ := normalQuotientAut N K
  let M := ⨆ g : G, movingSubgroup (ρ g)
  have hcomm : ⁅N, (⊤ : Subgroup G)⁆ ≤ (M.comap q).map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    let b : N := ⟨a, ha⟩
    refine ⟨b * MulAut.conjNormal g b⁻¹, ?_, ?_⟩
    · change q (b * MulAut.conjNormal g b⁻¹) ∈ M
      have hm := (le_iSup (fun g : G => movingSubgroup (ρ g)) g)
        (show delta (ρ g) (q b⁻¹) ∈ movingSubgroup (ρ g) from ⟨_, rfl⟩)
      convert hm using 1
      change q (b * MulAut.conjNormal g b⁻¹) = (q b⁻¹)⁻¹ * ρ g (q b⁻¹)
      simp only [map_mul, map_inv, inv_inv]
      rfl
    · change a * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      simp only [mul_assoc]
  rw [hmove] at hcomm
  apply top_le_iff.mp
  intro x _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
  obtain ⟨b, hb, hba⟩ := hcomm a.property
  have hba' : b = a := Subtype.ext hba
  exact hba' ▸ hb

/-- The linear part of the commutator correction on `N/Z(N)` is onto when
`a,b` generate the ambient group and `[N,G] = N`. -/
theorem correctionLinearMap_surjective_of_generating_pair
    (N : Subgroup G) [N.Normal]
    (p : ℕ) [Fact p.Prime] [IsElementaryAbelian p (N ⧸ Subgroup.center N)]
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N) :
    Function.Surjective
      (correctionLinearMap p
        ((MulAut.conjNormal : G →* MulAut N) (a * paperCommutator a b)⁻¹)
        ((MulAut.conjNormal : G →* MulAut N) ((paperCommutator a b)⁻¹ * b)⁻¹)) := by
  let ρ := normalQuotientAut N (Subgroup.center N)
  let c := paperCommutator a b
  have hpair : Subgroup.closure ({(c⁻¹ * b)⁻¹, (a * c)⁻¹} : Set G) = ⊤ := by
    rw [closure_inverse_pair, closure_commutator_correction_pair, hgen]
  intro t
  obtain ⟨x, z, hxz⟩ := exists_delta_mul_delta_of_generating_pair ρ
    (c⁻¹ * b)⁻¹ (a * c)⁻¹ hpair
    (iSup_normalQuotient_moving_eq_top N (Subgroup.center N) hmove) t.toMul
  refine ⟨(Additive.ofMul x, Additive.ofMul z⁻¹), ?_⟩
  have hh := congrArg Additive.ofMul hxz
  simp only [delta_apply, ofMul_mul, ofMul_inv] at hh
  change (Additive.ofMul (ρ (c⁻¹ * b)⁻¹ x) - Additive.ofMul x) +
      (Additive.ofMul z⁻¹ - Additive.ofMul (ρ (a * c)⁻¹ z⁻¹)) = t
  rw [(ρ ((a * c)⁻¹)).map_inv, ofMul_inv, ofMul_inv]
  convert hh using 1 <;> abel

end Kourovka2135

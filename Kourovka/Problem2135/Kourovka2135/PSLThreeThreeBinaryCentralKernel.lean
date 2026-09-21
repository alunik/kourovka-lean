import Kourovka2135.SemidihedralCentralStem
import Kourovka2135.PSLThreeThreeSemidihedralData
import Kourovka2135.CentralPGroupTransfer

/-! A finite perfect group with central binary kernel and actual quotient
PSL3(F3) has trivial kernel. Transfer and the explicit semidihedral subgroup
prove this directly; no multiplier or cohomology assumption is used. -/
set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeBinaryCentralKernel
open PSLThreeThreeSemidihedralData
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

/-- The actual special-linear quotient form of the central-kernel theorem. -/
theorem ker_eq_bot_of_specialLinear (π : G →* S) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center G) :
    π.ker = ⊥ := by
  let P := subgroup.comap π
  let φ : P →* subgroup :=
    { toFun := fun g => ⟨π g, g.property⟩
      map_one' := Subtype.ext π.map_one
      map_mul' := fun g h => Subtype.ext (π.map_mul g h) }
  have hφ : Function.Surjective φ := by
    intro s
    obtain ⟨g, hg⟩ := hπ s
    exact ⟨⟨g, by change π g ∈ subgroup; rw [hg]; exact s.property⟩, Subtype.ext hg⟩
  have hindex : Odd P.index := by
    rw [subgroup.index_comap_of_surjective hπ]
    exact subgroup_index_odd
  have htransfer := CentralPGroupTransfer.binary_le_commutator_map_of_odd_index
    π.ker hbinary hcentral P hindex
  have hc : φ.ker ≤ Subgroup.center P := by
    intro p hp
    have hpπ : π (p : G) = 1 := congrArg Subtype.val hp
    apply Subgroup.mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hpπ) q
  have hstem : φ.ker ≤ commutator P := by
    intro p hp
    have hpπ : π (p : G) = 1 := congrArg Subtype.val hp
    obtain ⟨t, ht, htp⟩ := htransfer hpπ
    have : t = p := Subtype.ext htp
    exact this ▸ ht
  obtain ⟨a, ha⟩ := hφ sx
  obtain ⟨b, hb⟩ := hφ sy
  have hk : φ.ker = ⊥ := SemidihedralCentralStem.ker_eq_bot φ hc a b
    (by rw [ha, hb]; exact subgroup_generated)
    (by rw [hb]; exact sy_pow_two)
    (by rw [ha, hb]; exact conjugate_sx)
    (by rw [ha]; exact orderOf_sx) hstem
  apply bot_unique
  intro r hr
  have hrP : r ∈ P := by change π r ∈ subgroup; rw [hr]; exact subgroup.one_mem
  have hrφ : (⟨r, hrP⟩ : P) ∈ φ.ker := Subtype.ext hr
  have hr1 : (⟨r, hrP⟩ : P) = 1 := Subgroup.mem_bot.mp (hk ▸ hrφ)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hr1)

/-- The projective quotient form, with no Frattini or simplicity premise. -/
theorem ker_eq_bot (π : G →* Q) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center G) :
    π.ker = ⊥ := by
  let ψ := projectiveEquiv.symm.toMonoidHom.comp π
  have hk : ψ.ker = π.ker := by
    ext g
    change projectiveEquiv.symm (π g) = 1 ↔ π g = 1
    exact projectiveEquiv.symm.map_eq_one_iff
  have h := ker_eq_bot_of_specialLinear ψ (projectiveEquiv.symm.surjective.comp hπ)
    (hk ▸ hbinary) (hk ▸ hcentral)
  exact hk ▸ h

/-- Any actual central binary normal subgroup with quotient PSL3(F3) is trivial. -/
theorem normal_eq_bot (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hcentral : R ≤ Subgroup.center G) (e : G ⧸ R ≃* Q) : R = ⊥ := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' R)
  have hk : π.ker = R := by
    ext g
    change e (QuotientGroup.mk' R g) = 1 ↔ g ∈ R
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  have h := ker_eq_bot π (e.surjective.comp (QuotientGroup.mk'_surjective R))
    (hk ▸ hR) (hk ▸ hcentral)
  exact hk ▸ h

end Kourovka2135.PSLThreeThreeBinaryCentralKernel

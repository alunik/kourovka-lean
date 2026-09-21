import Kourovka2135.DihedralCentralStem
import Kourovka2135.OddPSLTwoSplitDihedral
import Kourovka2135.CentralPGroupTransfer

/-! The central binary kernel bound for PSL2 over a field of cardinality
congruent to one modulo four. The proof uses actual transfer to the preimage
of the split dihedral subgroup. No multiplier or cohomology premise is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoSplitCentralKernel

open OddPSLTwoProjectiveChart

variable (F : Type*) [Field F] [Finite F]
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

/-- Every actual finite perfect central binary cover has kernel of size at
most two when the split dihedral subgroup has odd index. -/
theorem card_ker_le_two (hmod : Nat.card F % 4 = 1)
    (π : G →* Q F) (hπ : Function.Surjective π)
    (hbinary : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center G) :
    Nat.card π.ker ≤ 2 := by
  let D := OddPSLTwoSplitDihedral.subgroup F
  let P := D.comap π
  let φ : P →* D :=
    { toFun := fun g => ⟨π g, g.property⟩
      map_one' := Subtype.ext π.map_one
      map_mul' := fun g h => Subtype.ext (π.map_mul g h) }
  have hφ : Function.Surjective φ := by
    intro d
    obtain ⟨g, hg⟩ := hπ d
    exact ⟨⟨g, by change π g ∈ D; rw [hg]; exact d.property⟩, Subtype.ext hg⟩
  have hindex : Odd P.index := by
    rw [D.index_comap_of_surjective hπ]
    exact OddPSLTwoSplitDihedral.subgroup_index_odd F hmod
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
  obtain ⟨da, db, hgen, hconj⟩ := OddPSLTwoSplitDihedral.exists_subgroup_generators F
  obtain ⟨a, ha⟩ := hφ da
  obtain ⟨b, hb⟩ := hφ db
  have hcard : Nat.card φ.ker ≤ 2 := DihedralCentralStem.card_ker_le_two
    φ hc a b (by rw [ha, hb]; exact hgen) (by rw [ha, hb]; exact hconj) hstem
  let e : φ.ker ≃* π.ker :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val, by
        change π x.val ∈ D
        rw [x.property]
        exact D.one_mem⟩, Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  rwa [Nat.card_congr e.toEquiv] at hcard

/-- The normal-subgroup form, retaining an actual quotient equivalence. -/
theorem card_normal_le_two (hmod : Nat.card F % 4 = 1)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hcentral : R ≤ Subgroup.center G) (e : G ⧸ R ≃* Q F) : Nat.card R ≤ 2 := by
  let π := e.toMonoidHom.comp (QuotientGroup.mk' R)
  have hk : π.ker = R := by
    ext g
    change e (QuotientGroup.mk' R g) = 1 ↔ g ∈ R
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  have h := card_ker_le_two F hmod π (e.surjective.comp (QuotientGroup.mk'_surjective R))
    (hk ▸ hR) (hk ▸ hcentral)
  exact hk ▸ h

end Kourovka2135.OddPSLTwoSplitCentralKernel

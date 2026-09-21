import Kourovka2135.MinimalKernelStructure
import Kourovka2135.MinimalPairingRadical
import Kourovka2135.CentralCommutatorPairing

/-! Every noncentral element of a minimal noncentral normal soluble kernel moves its whole derived group. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem exists_paperCommutator_eq_of_minimal_noncentral
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G)
    (x : N) (hx : x ∉ Subgroup.center N) (t : commutator N) :
    ∃ y : N, paperCommutator x y = (t : N) := by
  have hDambient := minimal_noncentral_commutator_le_center N hmin
  have hDN : commutator N ≤ Subgroup.center N := by
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    apply Subtype.ext
    apply Subgroup.mem_center_iff.mp
    apply hDambient
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem N.subtype ha
  let f : N →* commutator N := centralCommutatorRightHom hDN x
  have hf : Function.Surjective f := by
    by_contra hns
    let i : commutator N →* G := N.subtype.comp (commutator N).subtype
    let K := f.range.map i
    have hKcenter : K ≤ Subgroup.center G := by
      rintro a ⟨z, _, rfl⟩
      apply hDambient
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map_of_mem N.subtype z.property
    let : K.Normal := ⟨by
      intro a ha g
      rw [Subgroup.mem_center_iff.mp (hKcenter ha) g, mul_assoc, mul_inv_cancel, mul_one]
      exact ha⟩
    have hDnot : ¬ ⁅N, N⁆ ≤ K := by
      intro hle
      apply hns
      apply MonoidHom.range_eq_top.mp
      apply top_le_iff.mp
      intro z _
      have hz : i z ∈ K := hle (by
        rw [← Subgroup.map_subtype_commutator]
        exact Subgroup.mem_map_of_mem N.subtype z.property)
      obtain ⟨y, hy, heq⟩ := hz
      have hyz : y = z := Subtype.ext (Subtype.ext heq)
      exact hyz ▸ hy
    have hRcenter := centralizer_mod_kernel_le_center_of_minimal_noncentral N K hDnot hmin
    have hxG : (x : G) ∈ Subgroup.center G := by
      apply hRcenter
      refine ⟨x.property, ?_⟩
      intro a ha
      obtain ⟨n, hn, rfl⟩ := ha
      let y : N := ⟨n, hn⟩
      have hcK : paperCommutator (x : G) n ∈ K := ⟨f y, ⟨y, rfl⟩, rfl⟩
      have hcomm : paperCommutator (QuotientGroup.mk' K (x : G))
          (QuotientGroup.mk' K n) = 1 := by
        have hh := (QuotientGroup.eq_one_iff _).mpr hcK
        change QuotientGroup.mk' K (paperCommutator (x : G) n) = 1 at hh
        simpa only [paperCommutator, map_mul, map_inv] using hh
      exact ((paperCommutator_eq_one_iff _ _).mp hcomm).eq.symm
    apply hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxG y)
  obtain ⟨y, hy⟩ := hf t
  exact ⟨y, congrArg Subtype.val hy⟩

end Kourovka2135

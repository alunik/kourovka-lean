import Kourovka2135.CentralPGroupH2Obstruction
import Kourovka2135.PerfectSupplement

/-! Every finite central 2-extension of a perfect binary SL2 quotient
with parameter exponent at least three has an actual group-homomorphic
section. A perfect supplement reduces this to the checked central-kernel
obstruction; no multiplier or extension-class comparison is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryCentralExtensionSplit

variable {E Q : Type} [Group E] [Finite E] [Group Q] [Group.IsPerfect Q]

/-- An actual section of an arbitrary finite central 2-extension. -/
theorem exists_section (π : E →* Q) (hπ : Function.Surjective π)
    (hkernel : IsPGroup 2 π.ker) (hcentral : π.ker ≤ Subgroup.center E)
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : SLTwo.SL2 F ≃* Q) : ∃ s : Q →* E, π.comp s = MonoidHom.id Q := by
  have htop : (⊤ : Subgroup E).map π = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective π hπ
  obtain ⟨K, _, hK, hperfect⟩ := exists_perfect_subgroup_map_top π ⊤ htop
  let : Group.IsPerfect K := hperfect
  let ψ : K →* Q := π.comp K.subtype
  have hψ : Function.Surjective ψ := by
    intro q
    have hq : q ∈ K.map π := by rw [hK]; trivial
    obtain ⟨g, hg, hgq⟩ := hq
    exact ⟨⟨g, hg⟩, hgq⟩
  let j : ψ.ker →* π.ker := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : π.ker => (z : E)) h
  have hpk : IsPGroup 2 ψ.ker := hkernel.of_injective j hj
  have hck : ψ.ker ≤ Subgroup.center K := by
    intro k hk
    apply Subgroup.mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcentral hk) (l : E)
  have hz : ψ.ker = ⊥ := CentralPGroupH2Obstruction.binary_eq_bot
    ψ.ker hpk hck F f hcard hf
    (e.trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm)
  let a : K ≃* Q := MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hz, hψ⟩
  refine ⟨K.subtype.comp a.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro q
  exact a.apply_symm_apply q

end Kourovka2135.BinaryCentralExtensionSplit

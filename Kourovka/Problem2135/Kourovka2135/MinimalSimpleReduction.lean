import Kourovka2135.MinimalDerivedVanishing
import Kourovka2135.MinimalQuotientOrder
import Kourovka2135.MinimalExistence

/-! Exact elementary reductions, without assuming a classification theorem. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G] [Finite G] {w : OuterWord} {p : ℕ}

theorem OrderMinimalException.quotient_radical_proper_subgroup_isSolvable
    (h : OrderMinimalException w p G) (hp : p.Prime)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (H : Subgroup (G ⧸ solubleRadical G)) (hne : H ≠ ⊤) : Group.IsSolvable H := by
  let q := QuotientGroup.mk' (solubleRadical G)
  let K := H.comap q
  have hKne : K ≠ ⊤ := by
    intro heq
    apply hne
    apply Subgroup.comap_injective (QuotientGroup.mk'_surjective _)
    simpa only [Subgroup.comap_top] using heq
  let : Group.IsSolvable K := h.proper_subgroup_isSolvable hp hnoncentral K hKne
  let f : K →* H := {
    toFun := fun x => ⟨q (x : G), x.property⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun _ _ => Subtype.ext (map_mul q _ _) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (solubleRadical G) (y : G ⧸ _)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change q x ∈ H
    rw [hx]
    exact y.property
  exact Group.isSolvable_of_surjective hf

end Kourovka2135

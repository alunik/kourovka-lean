import Kourovka2135.GoodClass
import Kourovka2135.GoodSetLifting

/-! A finite generating-class witness yields the full generating good set. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]

theorem isGeneratingGoodSet_conjugatesOf {c a b t : G}
    (ha : a ∈ conjugatesOf c) (hb : b ∈ conjugatesOf c)
    (ht : t ∈ conjugatesOf c) (hab : paperCommutator a b = t)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    IsGeneratingGoodSet (conjugatesOf c) := by
  intro x hx
  have htx : IsConj t x := (ht : IsConj c t).symm.trans hx
  obtain ⟨g, hg⟩ := isConj_iff.mp htx
  let f : G →* G := (MulAut.conj g).toMonoidHom
  have hfa : f a ∈ conjugatesOf c :=
    (ha : IsConj c a).trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hfb : f b ∈ conjugatesOf c :=
    (hb : IsConj c b).trans (isConj_iff.mpr ⟨g, rfl⟩)
  refine ⟨f a, hfa, f b, hfb, ?_, ?_⟩
  · calc
      paperCommutator (f a) (f b) = f (paperCommutator a b) := by
        simp only [paperCommutator, map_mul, map_inv]
      _ = f t := congrArg f hab
      _ = x := hg
  · rw [← Set.image_pair, ← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective f (MulAut.conj g).surjective

theorem isGeneratingGoodSet_conjugatesOf_of_certificate (a s t : G)
    (h : paperCommutator a (s⁻¹ * a * s) = t⁻¹ * a * t)
    (hgen : Subgroup.closure ({a, s⁻¹ * a * s} : Set G) = ⊤) :
    IsGeneratingGoodSet (conjugatesOf a) := by
  apply isGeneratingGoodSet_conjugatesOf (IsConj.refl a) ?_ ?_ h hgen
  · exact isConj_iff.mpr ⟨s⁻¹, by simp only [inv_inv]⟩
  · exact isConj_iff.mpr ⟨t⁻¹, by simp only [inv_inv]⟩

end Kourovka2135

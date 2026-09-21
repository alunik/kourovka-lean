import Kourovka2135.OddCanonicalNormalizerObstruction
import Kourovka2135.GoodSetEquiv

/-! Transport the concrete quotient-normalizer obstruction through an actual
group isomorphism. All good-set and subgroup data live in the supplied model;
the noncentral-radical hypothesis remains explicit.
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135

theorem OrderMinimalException.false_of_odd_model_normalizer_good_set
    {G : Type u} {S : Type v} [Group G] [Finite G] [Group S]
    {w : OuterWord} {p q : ℕ}
    (h : OrderMinimalException w p G) (hp : p.Prime) (hq : q.Prime)
    (hodd : p ≠ 2) (hqp : q ≠ p)
    (hnoncentral : ¬ solubleRadical G ≤ Subgroup.center G)
    (e : (G ⧸ solubleRadical G) ≃* S)
    {B : Set S} (hB : IsGeneratingGoodSet B)
    (U : Subgroup S) (hU : IsPGroup q U)
    (d x : S) (hd : d ∈ B)
    (hdnorm : d ∈ Subgroup.normalizer (U : Set S))
    (hx : x ∈ U) (hne : paperCommutator d (x⁻¹ * d * x) ≠ 1) : False := by
  have hB' : IsGeneratingGoodSet (e.toMonoidHom ⁻¹' B) :=
    hB.preimage_of_bijective e.toMonoidHom e.bijective
  have hU' : IsPGroup q (U.comap e.toMonoidHom) :=
    hU.comap_of_injective e.toMonoidHom e.injective
  apply h.false_of_odd_quotient_normalizer_good_set hp hq hodd hqp hnoncentral hB'
    (U.comap e.toMonoidHom) hU' (e.symm d) (e.symm x)
  · change e (e.symm d) ∈ B
    simpa only [e.apply_symm_apply] using hd
  · apply U.le_normalizer_comap e.toMonoidHom
    change e (e.symm d) ∈ Subgroup.normalizer (U : Set S)
    simpa only [e.apply_symm_apply] using hdnorm
  · change e (e.symm x) ∈ U
    simpa only [e.apply_symm_apply] using hx
  · intro he
    apply hne
    have hmap := congrArg e he
    simpa only [paperCommutator, map_mul, map_inv, map_one, e.apply_symm_apply] using hmap

end Kourovka2135

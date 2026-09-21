import Kourovka2135.AbelianCommutatorFiber
import Kourovka2135.PerfectSupplement
import Mathlib.GroupTheory.Frattini

/-!
Generating good sets consist of single values of every outer word. Their full
inverse images lift through abelian Frattini kernels satisfying [A,G] = A.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped commutatorElement
variable {G : Type u} [Group G]

def IsGeneratingGoodSet (B : Set G) : Prop :=
  ∀ t ∈ B, ∃ a ∈ B, ∃ b ∈ B,
    paperCommutator a b = t ∧ Subgroup.closure ({a, b} : Set G) = ⊤

theorem IsGeneratingGoodSet.subset_values {B : Set G}
    (hB : IsGeneratingGoodSet B) (w : OuterWord) : B ⊆ w.values G := by
  apply OuterWord.subset_values_of_commutator_closed B ?_ w
  intro t ht
  obtain ⟨a, ha, b, hb, hab, _⟩ := hB t ht
  exact ⟨a, ha, b, hb, hab⟩

theorem closure_pair_eq_top_of_quotient_generation [Finite G]
    (A : Subgroup G) [A.Normal] (hA : A ≤ frattini G) (a b : G)
    (hgen : Subgroup.closure
      ({QuotientGroup.mk' A a, QuotientGroup.mk' A b} : Set (G ⧸ A)) = ⊤) :
    Subgroup.closure ({a, b} : Set G) = ⊤ := by
  have hmap : (Subgroup.closure ({a, b} : Set G)).map (QuotientGroup.mk' A) = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_pair, hgen]
  have hsup := (map_quotient_eq_top_iff_sup A _).mp hmap
  apply frattini_nongenerating
  exact top_le_iff.mp (hsup ▸ sup_le_sup_left hA _)

theorem IsGeneratingGoodSet.preimage_quotient_of_abelian [Finite G]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hFrattini : A ≤ frattini G) (hA : ⁅A, (⊤ : Subgroup G)⁆ = A)
    {Y : Set (G ⧸ A)} (hY : IsGeneratingGoodSet Y) :
    IsGeneratingGoodSet ((QuotientGroup.mk' A) ⁻¹' Y) := by
  let q := QuotientGroup.mk' A
  intro t ht
  obtain ⟨α, hα, β, hβ, hαβ, hgen⟩ := hY (q t) ht
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective A α
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective A β
  change q a = α at ha
  change q b = β at hb
  have habgen : Subgroup.closure ({a, b} : Set G) = ⊤ := by
    apply closure_pair_eq_top_of_quotient_generation A hFrattini
    change Subgroup.closure ({q a, q b} : Set (G ⧸ A)) = ⊤
    rw [ha, hb]
    exact hgen
  have hc : q (paperCommutator a b) = q t := by
    simpa only [paperCommutator, map_mul, map_inv, ha, hb] using hαβ
  have hr : (paperCommutator a b)⁻¹ * t ∈ A := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((paperCommutator a b)⁻¹ * t) = 1
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  obtain ⟨u, v, huv⟩ := exists_paperCommutator_mul_eq_of_abelian A a b habgen hA
    (⟨(paperCommutator a b)⁻¹ * t, hr⟩ : A)
  have hqu : q (u : G) = 1 := (QuotientGroup.eq_one_iff _).mpr u.property
  have hqv : q (v : G) = 1 := (QuotientGroup.eq_one_iff _).mpr v.property
  have hau : q (a * u) = α := by rw [map_mul, hqu, mul_one]; exact ha
  have hbv : q (b * v) = β := by rw [map_mul, hqv, mul_one]; exact hb
  refine ⟨a * u, ?_, b * v, ?_, ?_, ?_⟩
  · change q (a * u) ∈ Y
    rw [hau]
    exact hα
  · change q (b * v) ∈ Y
    rw [hbv]
    exact hβ
  · simpa only [Subgroup.coe_mk, mul_inv_cancel_left] using huv
  · apply closure_pair_eq_top_of_quotient_generation A hFrattini
    change Subgroup.closure ({q (a * u), q (b * v)} : Set (G ⧸ A)) = ⊤
    rw [hau, hbv]
    exact hgen

end Kourovka2135

import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-! A normalizing generator of relative order dividing n enlarges a finite
subgroup by at most a factor n. This is the cardinal step for a verified
polycyclic normal form; no presentation completeness is assumed.
-/

set_option autoImplicit false
namespace Kourovka2135.FiniteAdjoinCard
open scoped Pointwise

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] (H : Subgroup G) (x : G)
    (h : ∀ g, g ∈ H → x⁻¹ * g * x ∈ H) : x ∈ Subgroup.normalizer H := by
  let f : H → H := fun g => ⟨x⁻¹ * g.val * x, h g.val g.property⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have he : x⁻¹ * a.val * x = x⁻¹ * b.val * x := congrArg (fun z : H => z.val) hab
    simpa only [mul_left_cancel_iff, mul_right_cancel_iff] using he
  have hs : Function.Surjective f := Finite.surjective_of_injective hi
  change ∀ g : G, g ∈ H ↔ x * g * x⁻¹ ∈ H
  intro g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := hs ⟨g, hg⟩
    have he : x⁻¹ * a.val * x = g := congrArg (fun z : H => z.val) ha
    have he' : a.val = x * g * x⁻¹ := by
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using
        congrArg (fun z : G => x * z * x⁻¹) he
    exact he' ▸ a.property
  · intro hg
    have hh := h (x * g * x⁻¹) hg
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh

theorem mem_normalizer_closure_of_generators [Finite G] (S : Set G) (x : G)
    (h : ∀ g, g ∈ S → x⁻¹ * g * x ∈ Subgroup.closure S) :
    x ∈ Subgroup.normalizer (Subgroup.closure S) := by
  apply mem_normalizer_of_conj_mem
  have hmap : (Subgroup.closure S).map (MulAut.conj x⁻¹).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨y, hy, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, SetLike.mem_coe]
      using h y hy
  intro g hg
  have hh := hmap (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hh

theorem exists_normalForm (H : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer H) (n : ℕ) (hn : 0 < n) (hp : x ^ n ∈ H)
    (g : ↥(H ⊔ Subgroup.zpowers x)) :
    ∃ h : H, ∃ i : Fin n, g.val = h.val * x ^ i.val := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer H := (Subgroup.zpowers_le).mpr hx
  have hmem : g.val ∈ (H : Set G) * (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left H (Subgroup.zpowers x) hle]
    exact g.property
  obtain ⟨a, ha, b, hb, he⟩ := hmem
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hz0 : 0 ≤ z % (n : ℤ) := Int.emod_nonneg _ (by omega)
  have hzn : z % (n : ℤ) < n := Int.emod_lt_of_pos _ (by omega)
  let i : Fin n := ⟨(z % (n : ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ) = z % (n : ℤ) := Int.toNat_of_nonneg hz0
  have hz : z = (n : ℤ) * (z / (n : ℤ)) + (i.val : ℤ) := by
    rw [hi]
    exact (Int.emod_add_ediv_mul z n).symm.trans (by ring)
  have hpow : x ^ z = (x ^ n) ^ (z / (n : ℤ)) * x ^ i.val := by
    calc
      x ^ z = x ^ ((n : ℤ) * (z / (n : ℤ)) + (i.val : ℤ)) := congrArg (fun t : ℤ => x ^ t) hz
      _ = (x ^ n) ^ (z / (n : ℤ)) * x ^ i.val := by
        rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast]
  refine ⟨⟨a * (x ^ n) ^ (z / (n : ℤ)), H.mul_mem ha (H.zpow_mem hp _)⟩, i, ?_⟩
  rw [← he, hpow]
  exact (mul_assoc _ _ _).symm

theorem card_le [Finite G] (H : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer H) (n : ℕ) (hn : 0 < n) (hp : x ^ n ∈ H) :
    Nat.card ↥(H ⊔ Subgroup.zpowers x) ≤ Nat.card H * n := by
  let f : H × Fin n → ↥(H ⊔ Subgroup.zpowers x) := fun z =>
    ⟨z.1.val * x ^ z.2.val, (H ⊔ Subgroup.zpowers x).mul_mem
      ((le_sup_left : H ≤ H ⊔ Subgroup.zpowers x) z.1.property)
      ((le_sup_right : Subgroup.zpowers x ≤ H ⊔ Subgroup.zpowers x)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨h, i, hi⟩ := exists_normalForm H x hx n hn hp g
    exact ⟨(h, i), Subtype.ext hi.symm⟩
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_surjective f hf

end Kourovka2135.FiniteAdjoinCard

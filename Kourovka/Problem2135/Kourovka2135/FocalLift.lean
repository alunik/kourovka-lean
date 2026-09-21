/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Quotient lifting for conjugacy-invariant sets of p-elements. -/

namespace Kourovka2135.FocalLift

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Every p-element is conjugate into a chosen Sylow p-subgroup. -/
theorem exists_conj_mem_sylow (P : Sylow p G) {x : G}
    (hx : ∃ k : ℕ, orderOf x = p ^ k) :
    ∃ g : G, g * x * g⁻¹ ∈ P := by
  obtain ⟨k, hk⟩ := hx
  have hcyclic : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (by simpa only [Nat.card_zpowers] using hk)
  obtain ⟨Q, hQ⟩ := hcyclic.exists_le_sylow
  have hxQ : x ∈ Q := hQ (Subgroup.mem_zpowers x)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hconj : g * x * g⁻¹ ∈ (g • Q : Sylow p G) := by
    change g * x * g⁻¹ ∈ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom
    exact ⟨x, hxQ, rfl⟩
  exact ⟨g, hg ▸ hconj⟩

/-- A p-element whose quotient image lies in the chosen Sylow image can be conjugated
into that Sylow subgroup by an element of the quotient kernel. -/
theorem exists_kernel_conj_mem_sylow
    (N : Subgroup G) [N.Normal] (P : Sylow p G) {x : G}
    (hx : ∃ k : ℕ, orderOf x = p ^ k)
    (hxP : (QuotientGroup.mk' N) x ∈ (P : Subgroup G).map (QuotientGroup.mk' N)) :
    ∃ n ∈ N, n * x * n⁻¹ ∈ P := by
  let K : Subgroup G := (P : Subgroup G) ⊔ N
  have hxK : x ∈ K := by
    have hxpre : x ∈ ((P : Subgroup G).map (QuotientGroup.mk' N)).comap
        (QuotientGroup.mk' N) := hxP
    simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hxpre
  let S : Sylow p K := P.subtype (show (P : Subgroup G) ≤ K from le_sup_left)
  have hxorder : ∃ k : ℕ, orderOf (⟨x, hxK⟩ : K) = p ^ k := by
    simpa only [Subgroup.orderOf_mk] using hx
  obtain ⟨k, hk⟩ := exists_conj_mem_sylow S hxorder
  have hkP : (k : G) * x * (k : G)⁻¹ ∈ P := hk
  obtain ⟨a, ha, n, hn, hkn⟩ := Subgroup.mem_sup_of_normal_right.mp k.property
  refine ⟨n, hn, ?_⟩
  have hremove : a⁻¹ * ((k : G) * x * (k : G)⁻¹) * a ∈ P :=
    P.mul_mem (P.mul_mem (P.inv_mem ha) hkP) ha
  rw [← hkn] at hremove
  simpa [mul_assoc] using hremove

/-- Alves–Shumyatsky's quotient identity for a normal set of p-elements.
Conjugacy invariance and the prime-power order condition are explicit. -/
theorem quotient_image_inter_sylow
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (X : Set G)
    (hconj : ∀ x ∈ X, ∀ g : G, g * x * g⁻¹ ∈ X)
    (hpowers : ∀ x ∈ X, ∃ k : ℕ, orderOf x = p ^ k) :
    (QuotientGroup.mk' N) '' X ∩
        ((P : Subgroup G).map (QuotientGroup.mk' N) : Set (G ⧸ N)) =
      (QuotientGroup.mk' N) '' (X ∩ (P : Set G)) := by
  ext y
  constructor
  · rintro ⟨⟨x, hxX, rfl⟩, hxP⟩
    obtain ⟨n, hn, hnP⟩ := exists_kernel_conj_mem_sylow N P (hpowers x hxX) hxP
    refine ⟨n * x * n⁻¹, ⟨hconj x hxX n, hnP⟩, ?_⟩
    have hqn : (QuotientGroup.mk' N) n = 1 :=
      (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    simp only [map_mul, map_inv, hqn, one_mul, inv_one, mul_one]
  · rintro ⟨x, ⟨hxX, hxP⟩, rfl⟩
    exact ⟨⟨x, hxX, rfl⟩, ⟨x, hxP, rfl⟩⟩

end Kourovka2135.FocalLift

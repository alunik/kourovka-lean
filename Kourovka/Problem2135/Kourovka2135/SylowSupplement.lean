import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Sylow subgroups in a normal prime-power supplement

Suppose `G = A B`, where `A` is a normal r-subgroup. A Sylow q-subgroup of `B`
embeds as a Sylow q-subgroup of `G` when `q ≠ r`; when `q = r`, its join with
`A` is Sylow. Conjugacy then gives a decomposition of every specified Sylow
subgroup. The supplement `B` need not be normal or disjoint from `A`.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135

open scoped Pointwise

variable {G : Type u} [Group G]

/-- For a normal p-subgroup and a supplement, adjoining the normal subgroup to
a Sylow p-subgroup of the supplement gives a Sylow subgroup of the ambient group. -/
theorem exists_sylow_eq_sup_of_normal_pGroup
    {p : ℕ} [Fact p.Prime] (A B : Subgroup G) [A.Normal]
    (hA : IsPGroup p A) (hsup : A ⊔ B = ⊤) (Q : Sylow p B) :
    ∃ S : Sylow p G, (S : Subgroup G) = A ⊔ (Q : Subgroup B).map B.subtype := by
  let T : Subgroup G := (Q : Subgroup B).map B.subtype
  have hT : IsPGroup p T := Q.isPGroup'.map B.subtype
  obtain ⟨S, hS⟩ := (hA.to_sup_of_normal_left hT).exists_le_sylow
  have hAS : A ≤ (S : Subgroup G) := le_sup_left.trans hS
  have hTS : T ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hcomap : (S : Subgroup G).comap B.subtype = (Q : Subgroup B) := by
    apply Q.is_maximal' S.isPGroup'.comap_subtype
    intro x hx
    exact hTS ⟨x, hx, rfl⟩
  refine ⟨S, le_antisymm ?_ hS⟩
  intro x hx
  have hxSup : x ∈ A ⊔ B := by simp [hsup]
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hxSup
  have hbS : b ∈ (S : Subgroup G) := by
    have h := S.mul_mem (S.inv_mem (hAS ha)) hx
    rw [← hab] at h
    simpa only [inv_mul_cancel_left] using h
  have hbQ : (⟨b, hb⟩ : B) ∈ Q := by
    change (⟨b, hb⟩ : B) ∈ (Q : Subgroup B)
    rw [← hcomap]
    exact hbS
  rw [← hab]
  exact Subgroup.mul_mem_sup ha ⟨⟨b, hb⟩, hbQ, rfl⟩

variable [Finite G]

/-- For distinct primes q and r, a Sylow q-subgroup of a supplement to a normal
r-subgroup embeds as a Sylow subgroup of the whole group. -/
theorem exists_sylow_eq_map_of_normal_prime_ne
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (A B : Subgroup G) [A.Normal] (hA : IsPGroup r A)
    (hsup : A ⊔ B = ⊤) (hne : q ≠ r) (Q : Sylow q B) :
    ∃ S : Sylow q G, (S : Subgroup G) = (Q : Subgroup B).map B.subtype := by
  let π : G →* G ⧸ A := QuotientGroup.mk' A
  let f : B →* G ⧸ A := π.comp B.subtype
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective A z
    have hgSup : g ∈ A ⊔ B := by simp [hsup]
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hgSup
    have hπa : π a = 1 := (QuotientGroup.eq_one_iff (N := A) a).mpr ha
    refine ⟨⟨b, hb⟩, ?_⟩
    change π b = z
    have hπg : π g = π b := by rw [← hab, map_mul, hπa, one_mul]
    exact hπg.symm.trans hg
  let T : Subgroup G := (Q : Subgroup B).map B.subtype
  let Qbar : Sylow q (G ⧸ A) := Q.mapSurjective hf
  have hT : IsPGroup q T := Q.isPGroup'.map B.subtype
  have hTmap : T.map π = (Qbar : Subgroup (G ⧸ A)) := by
    change ((Q : Subgroup B).map B.subtype).map π = _
    rw [Subgroup.map_map]
    rfl
  refine ⟨{ toSubgroup := T, isPGroup' := hT, is_maximal' := ?_ }, rfl⟩
  intro D hD hTD
  apply le_antisymm ?_ hTD
  have hDmap : D.map π = (Qbar : Subgroup (G ⧸ A)) := by
    apply Qbar.is_maximal' (hD.map π)
    rw [← hTmap]
    exact Subgroup.map_mono hTD
  have hdisjoint : Disjoint D A := IsPGroup.disjoint_of_ne q r hne D A hD hA
  intro x hx
  have hxMap : π x ∈ T.map π := by
    rw [hTmap, ← hDmap]
    exact ⟨x, hx, rfl⟩
  obtain ⟨t, ht, htx⟩ := hxMap
  have hdiffD : x * t⁻¹ ∈ D := D.mul_mem hx (D.inv_mem (hTD ht))
  have hdiffA : x * t⁻¹ ∈ A := by
    apply (QuotientGroup.eq_one_iff (N := A) _).mp
    change π (x * t⁻¹) = 1
    simp only [map_mul, map_inv, htx, mul_inv_cancel]
  have hxt : x = t := mul_inv_eq_one.mp
    (Subgroup.disjoint_def.mp hdisjoint hdiffD hdiffA)
  rw [hxt]
  exact ht

/-- Every specified Sylow subgroup has the normal-subgroup/supplement decomposition
up to conjugating a chosen Sylow subgroup of the supplement. -/
theorem exists_sylow_conjugate_decomposition
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime]
    (A B : Subgroup G) [A.Normal] (hA : IsPGroup r A)
    (hsup : A ⊔ B = ⊤) (Q : Sylow q B) (P : Sylow q G) :
    ∃ g : G, (P : Subgroup G) =
      (if q = r then A else ⊥) ⊔
        ((Q : Subgroup B).map B.subtype).map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hqr : q = r
  · have hAq : IsPGroup q A := hqr.symm ▸ hA
    obtain ⟨S, hS⟩ := exists_sylow_eq_sup_of_normal_pGroup A B hAq hsup Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
    refine ⟨g, ?_⟩
    have hg' : (P : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg]
      rfl
    rw [hS, Subgroup.smul_sup, Subgroup.Normal.conj_smul_eq_self] at hg'
    change (P : Subgroup G) = A ⊔
      ((Q : Subgroup B).map B.subtype).map (MulAut.conj g).toMonoidHom at hg'
    simpa only [ite_eq_left hqr] using hg'
  · obtain ⟨S, hS⟩ := exists_sylow_eq_map_of_normal_prime_ne A B hA hsup hqr Q
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
    refine ⟨g, ?_⟩
    have hg' : (P : Subgroup G) = MulAut.conj g • (S : Subgroup G) := by
      rw [← hg]
      rfl
    rw [hS] at hg'
    change (P : Subgroup G) =
      ((Q : Subgroup B).map B.subtype).map (MulAut.conj g).toMonoidHom at hg'
    simpa only [ite_eq_right hqr, bot_sup_eq] using hg'

end Kourovka2135

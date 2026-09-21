import Kourovka2135.CocycleGeneratorBounds
import Mathlib.RepresentationTheory.Invariants

/-! Elementary degree-one vanishing for a normal subgroup of invertible
order with no fixed coefficient vector. Averaging constructs a principal
cocycle on the subgroup; normality then forces every remaining value into
its actual fixed space. No extension or representation classification is used. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.NormalCoprimeCocycleVanishing
open groupCohomology CocycleGeneratorBounds

variable {K G V : Type u} [Field K] [Group G]
variable [AddCommGroup V] [Module K V]
variable (ρ : Representation K G V)

/-- The usual averaging argument produces the actual principal vector. -/
theorem exists_principal_of_card_ne_zero [Fintype G]
    (hcard : (Fintype.card G : K) ≠ 0) (z : cocycles₁ (Rep.of ρ)) :
    ∃ v : V, ∀ g : G, z g = ρ g v - v := by
  classical
  let s : V := ∑ g : G, z g
  refine ⟨-((Fintype.card G : K)⁻¹ • s), fun g => ?_⟩
  have hs : s = ρ g s + (Fintype.card G : K) • z g := by
    calc
      s = ∑ h : G, z (g * h) :=
        (Function.Bijective.sum_comp (Group.mulLeft_bijective g) z).symm
      _ = ρ g s + (Fintype.card G : K) • z g := by
        simp only [(mem_cocycles₁_iff z).mp z.property, Finset.sum_add_distrib,
          ← map_sum, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, s]
  have hscaled := congrArg (fun x : V => (Fintype.card G : K)⁻¹ • x) hs
  rw [smul_add, smul_smul, inv_mul_cancel₀ hcard, one_smul] at hscaled
  have hz : z g = (Fintype.card G : K)⁻¹ • s -
      (Fintype.card G : K)⁻¹ • ρ g s := by
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hscaled.symm
  simpa only [map_neg, map_smul, sub_neg_eq_add, neg_add_eq_sub] using hz

/-- A cocycle zero on a normal subgroup takes all values in its fixed space. -/
theorem eq_zero_of_zero_on_normal (H : Subgroup G) [H.Normal]
    (hfixed : Representation.invariants (ρ.comp H.subtype) = ⊥)
    (z : cocycles₁ (Rep.of ρ)) (hz : ∀ h : H, z h = 0) : z = 0 := by
  apply cocycles₁_ext
  intro g
  have hinv : z g ∈ Representation.invariants (ρ.comp H.subtype) := by
    intro h
    have hm : g⁻¹ * (h : G) * g ∈ H := by
      simpa only [inv_inv] using
        (inferInstance : H.Normal).conj_mem (h : G) h.property g⁻¹
    have he : g * (g⁻¹ * (h : G) * g) = (h : G) * g := by group
    have ha := (mem_cocycles₁_iff z).mp z.property g (g⁻¹ * (h : G) * g)
    have hb := (mem_cocycles₁_iff z).mp z.property (h : G) g
    rw [he, hz ⟨_, hm⟩, map_zero, zero_add] at ha
    rw [hz h, add_zero] at hb
    exact hb.symm.trans ha
  rw [hfixed] at hinv
  exact hinv

/-- Actual first cohomology vanishes when a normal coprime-order subgroup
has no fixed vectors. -/
theorem subsingleton_H1 (H : Subgroup G) [H.Normal] [Fintype H]
    (hcard : (Fintype.card H : K) ≠ 0)
    (hfixed : Representation.invariants (ρ.comp H.subtype) = ⊥) :
    Subsingleton (groupCohomology (Rep.of ρ) 1) := by
  have hzero : ∀ x : groupCohomology (Rep.of ρ) 1, x = 0 := by
    intro x
    induction x using H1_induction_on with
    | h z =>
      let zr : cocycles₁ (Rep.of (ρ.comp H.subtype)) :=
        ⟨fun h => z h, (mem_cocycles₁_iff _).mpr
          (fun a b => (mem_cocycles₁_iff z).mp z.property a b)⟩
      obtain ⟨v, hv⟩ := exists_principal_of_card_ne_zero (ρ.comp H.subtype) hcard zr
      have hn : z - principal ρ v = 0 := by
        apply eq_zero_of_zero_on_normal ρ H hfixed
        intro h
        change z h - (ρ h v - v) = 0
        exact sub_eq_zero.mpr (hv h)
      have he : z = principal ρ v := sub_eq_zero.mp hn
      apply (H1π_eq_zero_iff (A := Rep.of ρ) z).mpr
      exact ⟨v, congrArg Subtype.val he.symm⟩
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end Kourovka2135.NormalCoprimeCocycleVanishing

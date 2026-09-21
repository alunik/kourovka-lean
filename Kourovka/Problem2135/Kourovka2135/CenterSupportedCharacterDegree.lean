/-
The central-scalar helper is adapted from the Qiuzhen CFSG project,
https://github.com/Qiuzhen-CFSG/CFSG, Apache 2.0 license (repository LICENSE).
Source: Theory/Representation/ExtraspecialFixedPoints.lean, lines 293-319,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd,
source SHA256 76983ded3b0e6cdf4bd4dbf36583a2f915232a0dd1b24e94d3aafc0286c97157.
The degree proof uses character orthogonality directly and assumes no
extraspecial-group structure or faithful action.
-/
import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.Index

/-! An irreducible characteristic-zero character supported on the center
has degree squared equal to the index of the center. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CenterSupportedCharacterDegree

open Representation
open scoped BigOperators

theorem center_apply_eq_smul_id_of_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ]
    {z : G} (hz : z ∈ Subgroup.center G) :
    ∃ a : F, (ρ z : Module.End F V) = a • 1 := by
  let φ := Representation.IntertwiningMap.centralMul (ρ := ρ) z (by
    rw [Submonoid.mem_center_iff]
    intro g
    exact (Subgroup.mem_center_iff.mp hz) g)
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective φ
  refine ⟨a, ?_⟩
  have hlin :
      ((algebraMap F (Representation.IntertwiningMap ρ ρ) a :
          Representation.IntertwiningMap ρ ρ) : Module.End F V) =
        (φ : Module.End F V) := by
    simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => (f : Module.End F V)) ha
  calc
    (ρ z : Module.End F V) = (φ : Module.End F V) := rfl
    _ = ((algebraMap F (Representation.IntertwiningMap ρ ρ) a :
        Representation.IntertwiningMap ρ ρ) : Module.End F V) := hlin.symm
    _ = a • (1 : Module.End F V) := by
      ext v
      simp [Representation.IntertwiningMap.algebraMap_apply, LinearMap.smul_apply]

variable {k G V : Type*} [Field k] [IsAlgClosed k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (rho : Representation k G V) [IsIrreducible rho]

/-- A central element and its inverse contribute the degree squared. -/
theorem character_mul_inv_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) :
    rho.character g * rho.character g⁻¹ = (Module.finrank k V : k) ^ 2 := by
  obtain ⟨a, ha⟩ := center_apply_eq_smul_id_of_irreducible rho hg
  have hgtrace : rho.character g = a * (Module.finrank k V : k) := by
    change LinearMap.trace k V (rho g) = _
    rw [ha, map_smul, LinearMap.trace_one, smul_eq_mul]
  have hprod : a * rho.character g⁻¹ = (Module.finrank k V : k) := by
    have hm : a • rho g⁻¹ = (1 : Module.End k V) := by
      calc
        a • rho g⁻¹ = (a • (1 : Module.End k V)) * rho g⁻¹ := by simp
        _ = rho g * rho g⁻¹ := by rw [ha]
        _ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have ht := congrArg (LinearMap.trace k V) hm
    simpa only [map_smul, LinearMap.trace_one, smul_eq_mul, Representation.character] using ht
  rw [hgtrace]
  calc
    (a * (Module.finrank k V : k)) * rho.character g⁻¹ =
        (Module.finrank k V : k) * (a * rho.character g⁻¹) := by ring
    _ = (Module.finrank k V : k) ^ 2 := by rw [hprod, pow_two]

/-- Exact degree identity for an actual center-supported irreducible character. -/
theorem finrank_sq_eq_card_quotient_center [Finite G] [CharZero k]
    (hzero : ∀ g : G, g ∉ Subgroup.center G → rho.character g = 0) :
    (Module.finrank k V) ^ 2 = Nat.card (G ⧸ Subgroup.center G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hc : (Nat.card G : k) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  let : Invertible (Nat.card G : k) := invertibleOfNonzero hc
  have ho : (Nat.card G : k)⁻¹ *
      (∑ g : G, rho.character g * rho.character g⁻¹) = 1 := by
    simpa [show Nonempty (Representation.Equiv rho rho) from
      ⟨Representation.Equiv.refl rho⟩] using
      (Representation.char_orthonormal (ρ := rho) (σ := rho))
  have hs : (∑ g : G, rho.character g * rho.character g⁻¹) = (Nat.card G : k) := by
    calc
      (∑ g : G, rho.character g * rho.character g⁻¹) =
          (Nat.card G : k) * ((Nat.card G : k)⁻¹ *
            (∑ g : G, rho.character g * rho.character g⁻¹)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ = (Nat.card G : k) := by rw [ho, mul_one]
  have hz : (∑ g : G, rho.character g * rho.character g⁻¹) =
      ∑ _z : Subgroup.center G, (Module.finrank k V : k) ^ 2 := by
    let e : (Subgroup.center G : Set G) ≃ Subgroup.center G := {
      toFun := fun z => ⟨z.val, z.property⟩
      invFun := fun z => ⟨z.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have hcard := Nat.card_congr e
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_eq_nat_card, hcard] using Finset.sum_congr_set (Subgroup.center G : Set G)
      (fun g => rho.character g * rho.character g⁻¹)
      (fun _ => (Module.finrank k V : k) ^ 2)
      (fun g hg => character_mul_inv_of_mem_center rho hg)
      (fun g hg => by rw [hzero g hg, zero_mul])
  have hcast : (Nat.card G : k) =
      (Nat.card (Subgroup.center G) : k) * (Module.finrank k V : k) ^ 2 := by
    rw [← hs, hz]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card]
  have hnat : Nat.card G = Nat.card (Subgroup.center G) * (Module.finrank k V) ^ 2 := by
    exact_mod_cast hcast
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.center G))
  calc
    Nat.card (Subgroup.center G) * Module.finrank k V ^ 2 = Nat.card G := hnat.symm
    _ = Nat.card (Subgroup.center G) * Nat.card (G ⧸ Subgroup.center G) := by
      simpa only [Subgroup.index_eq_card] using (Subgroup.center G).card_mul_index.symm

end Kourovka2135.CenterSupportedCharacterDegree

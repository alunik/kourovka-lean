/-
Adapted from the Qiuzhen CFSG project (https://github.com/Qiuzhen-CFSG/CFSG).
Released under Apache 2.0 license as described in that repository's LICENSE.
Source: Theory/Representation/ExtraspecialFixedPoints.lean, lines 437-466.
Commit: 96b2a02085dc678f3e0a97b334c31ada599c55fd.
Original file SHA256: 76983ded3b0e6cdf4bd4dbf36583a2f915232a0dd1b24e94d3aafc0286c97157.
Only this generic theorem is selected; no extraspecial-group hypothesis or
representation-extension theorem is imported.
-/
import Mathlib.RepresentationTheory.Character

/-! Equal characters of finite-dimensional irreducible representations give
an actual representation equivalence over an algebraically closed field whose
characteristic does not divide the finite group order. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.IrreducibleCharacterEquiv

open Representation
open scoped BigOperators

theorem equiv_of_irreducible_char_eq
    {G : Type*} [Group G] [Finite G]
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    [IsIrreducible ρ] [IsIrreducible σ]
    (hc : ¬ ringChar F ∣ Nat.card G)
    (hchar : ρ.character = σ.character) :
    Nonempty (Equiv σ ρ) := by
  let : Fintype G := Fintype.ofFinite G
  have hcard_ne_zero : (Nat.card G : F) ≠ 0 := by
    intro hzero
    exact hc ((ringChar.spec F (Nat.card G)).1 hzero)
  let : Invertible (Nat.card G : F) := invertibleOfNonzero hcard_ne_zero
  by_cases hE : Nonempty (Equiv σ ρ)
  · exact hE
  · have horth := Representation.char_orthonormal (ρ := ρ) (σ := σ)
    have hself := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    rw [hchar] at horth
    have horth' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (0 : F) := by
      have horthσ :
          (Nat.card G : F)⁻¹ * ∑ g : G, σ.character g * σ.character g⁻¹ = (0 : F) := by
        simpa [hE] using horth
      simpa [hchar] using horthσ
    have hself' :
        (Nat.card G : F)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = (1 : F) := by
      simpa [show Nonempty (Equiv ρ ρ) from ⟨Representation.Equiv.refl ρ⟩] using hself
    exact False.elim (zero_ne_one (horth'.symm.trans hself'))

end Kourovka2135.IrreducibleCharacterEquiv

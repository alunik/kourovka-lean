import Kourovka2135.RegularCharacter
import Kourovka2135.RepresentationIrreducibleSubspace
import Kourovka2135.RepresentationInvariantComplement
import Mathlib.Data.Complex.Basic

/-! A finite family of group elements contains the identity if its sums
against every actual irreducible character have nonnegative real part.
The proof uses actual invariant complements and the constant line inside the
actual regular representation. No character enumeration, completeness or
Fourier inversion theorem is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CharacterPositivity

open scoped BigOperators
attribute [local instance] Fintype.ofFinite

variable {G ι : Type} [Group G] [Finite G] [Finite ι]

def sumCharacter {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (X : ι → G) : ℂ := ∑ i : ι, ρ.character (X i)

def IrreducibleNonnegative (X : ι → G) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V), ρ.IsIrreducible → 0 ≤ (sumCharacter ρ X).re

omit [Finite G] in
theorem sumCharacter_eq_add
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W U : Subrepresentation ρ)
    (hWU : IsCompl W.toSubmodule U.toSubmodule) (X : ι → G) :
    sumCharacter ρ X = sumCharacter W.toRepresentation X + sumCharacter U.toRepresentation X := by
  unfold sumCharacter
  simp_rw [RepresentationInvariantComplement.character_eq_add ρ W U hWU]
  exact Finset.sum_add_distrib

/-- Dimension induction transfers the actual irreducible inequalities to every representation. -/
theorem nonnegative_of_irreducible (X : ι → G) (hX : IrreducibleNonnegative X)
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) : 0 ≤ (sumCharacter ρ X).re := by
  let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  have aux : ∀ n : ℕ, ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
      [FiniteDimensional ℂ W] (σ : Representation ℂ G W),
      Module.finrank ℂ W = n → 0 ≤ (sumCharacter σ X).re := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ σ hdim
      by_cases hn : n = 0
      · let : Subsingleton W := Module.finrank_zero_iff.mp (hdim.trans hn)
        have hchar (g : G) : σ.character g = 0 := by
          change LinearMap.trace ℂ W (σ g) = 0
          rw [Subsingleton.elim (σ g) 0, map_zero]
        simp only [sumCharacter, hchar, Finset.sum_const_zero, Complex.zero_re, le_refl]
      · let : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℂ) (M := W) (by omega)
        obtain ⟨P, hP, hPirred⟩ := RepresentationIrreducibleSubspace.exists_irreducible_subrepresentation σ
        obtain ⟨Q, hPQ⟩ := RepresentationInvariantComplement.exists_isCompl σ P
        have hlt : Module.finrank ℂ Q.toSubmodule < n := by
          rw [← hdim]
          exact RepresentationInvariantComplement.finrank_right_lt σ P Q hPQ hP
        have hQ := ih (Module.finrank ℂ Q.toSubmodule) hlt Q.toSubmodule Q.toRepresentation rfl
        have hposP := hX P.toSubmodule P.toRepresentation hPirred
        rw [sumCharacter_eq_add σ P Q hPQ, Complex.add_re]
        exact add_nonneg hposP hQ
  exact aux (Module.finrank ℂ V) V ρ rfl

/-- Positivity on actual irreducibles detects an identity among any nonempty finite family. -/
theorem exists_eq_one_of_irreducible_nonnegative [Nonempty ι]
    (X : ι → G) (hX : IrreducibleNonnegative X) : ∃ i : ι, X i = 1 := by
  classical
  by_contra hnone
  have hne : ∀ i : ι, X i ≠ 1 := by simpa only [not_exists] using hnone
  let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  let ρ := RegularCharacter.regular ℂ G
  let P := RegularCharacter.constants ℂ G
  obtain ⟨Q, hPQ⟩ := RepresentationInvariantComplement.exists_isCompl ρ P
  have hQ := nonnegative_of_irreducible X hX Q.toRepresentation
  have hsplit := sumCharacter_eq_add ρ P Q hPQ X
  have hreg : sumCharacter ρ X = 0 := by
    simp [sumCharacter, ρ, RegularCharacter.regular_character, hne]
  have hconst : sumCharacter P.toRepresentation X = (Nat.card ι : ℂ) := by
    simp [sumCharacter, P, RegularCharacter.constants_character, Nat.card_eq_fintype_card]
  rw [hreg, hconst] at hsplit
  have hre := congrArg Complex.re hsplit
  simp only [Complex.zero_re, Complex.add_re, Complex.natCast_re] at hre
  have hcard : (0 : ℝ) < Nat.card ι := by exact_mod_cast Nat.card_pos (α := ι)
  linarith

end Kourovka2135.CharacterPositivity

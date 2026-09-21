/-
Adapted from the Qiuzhen CFSG project (https://github.com/Qiuzhen-CFSG/CFSG).
Released under Apache 2.0 license as described in that repository's LICENSE.
Source: Theory/Representation/Induction.lean, lines 298-453.
Commit: 96b2a02085dc678f3e0a97b334c31ada599c55fd.
Original file SHA256: 07c6ad6a77fb0a96a454ccbd608712e271a1ede8fabf7385012e0f5f8f6425a1.
Only right-coset coordinates and their actual trace formula are selected.
The complex scalar field is generalized to an arbitrary field; no character
extension or irreducibility theorem is imported.
-/
import Kourovka2135.MonomialTrace
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Character

/-! Actual right-coset coordinates for a coinduced representation.
The action is `f(x) ↦ f(x*g)`, matching mathlib's coinduced convention.
At a fixed right coset, the coefficient is the original representation at
`out(q)*g*out(q)⁻¹`, so no inverse-character convention is introduced. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.CoinducedCharacterFormula
open Representation MonomialTrace
open scoped BigOperators
attribute [local instance] Fintype.ofFinite

variable {k G A : Type*} [Field k] [Group G]
variable [AddCommGroup A] [Module k A]

abbrev RightCosets (S : Subgroup G) := Quotient (QuotientGroup.rightRel S)

instance rightCosetsFintype [Finite G] (S : Subgroup G) : Fintype (RightCosets S) := by
  letI : Fintype (G ⧸ S) := Fintype.ofFinite (G ⧸ S)
  exact QuotientGroup.fintypeQuotientRightRel (s := S)

def rightCosetOut (S : Subgroup G) (g : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel S) g)

theorem rightCosetOut_spec (S : Subgroup G) (g : G) :
    g * (rightCosetOut S g)⁻¹ ∈ S := by
  simpa [rightCosetOut, QuotientGroup.rightRel_apply] using
    (Quotient.mk_out (s := QuotientGroup.rightRel S) g)

theorem rightCosetOut_eq_of_mk_eq (S : Subgroup G) {g h : G}
    (eq : Quotient.mk (QuotientGroup.rightRel S) g =
      Quotient.mk (QuotientGroup.rightRel S) h) :
    rightCosetOut S g = rightCosetOut S h := by
  exact congrArg Quotient.out eq

theorem rightCosetOut_out (S : Subgroup G) (q : RightCosets S) :
    rightCosetOut S (Quotient.out q) = Quotient.out q := by
  exact congrArg Quotient.out (Quotient.out_eq q)

def rightCosetCorrection (S : Subgroup G) (g : G) : S :=
  ⟨g * (rightCosetOut S g)⁻¹, rightCosetOut_spec S g⟩

theorem rightCoset_mk_smul (S : Subgroup G) (s : S) (g : G) :
    Quotient.mk (QuotientGroup.rightRel S) ((s : G) * g) =
      Quotient.mk (QuotientGroup.rightRel S) g := by
  apply Quotient.sound
  change (QuotientGroup.rightRel S).r ((s : G) * g) g
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev, s.2]

theorem rightCosetCorrection_smul (S : Subgroup G) (s : S) (g : G) :
    rightCosetCorrection S ((s : G) * g) = s * rightCosetCorrection S g := by
  apply Subtype.ext
  change ((s : G) * g) * (rightCosetOut S ((s : G) * g))⁻¹ =
    (s : G) * (g * (rightCosetOut S g)⁻¹)
  rw [rightCosetOut_eq_of_mk_eq S (rightCoset_mk_smul S s g)]
  simp [mul_assoc]

theorem subgroupSubtype_correction_mul_out (S : Subgroup G) (g : G) :
    ((rightCosetCorrection S g : S) : G) * rightCosetOut S g = g := by
  simp [rightCosetCorrection, mul_assoc]

theorem rightCosetCorrection_out (S : Subgroup G) (q : RightCosets S) :
    rightCosetCorrection S (Quotient.out q) = 1 := by
  apply Subtype.ext
  change Quotient.out q * (rightCosetOut S (Quotient.out q))⁻¹ = (1 : G)
  rw [rightCosetOut_out]
  simp

def fixedConjugate (S : Subgroup G) (q : RightCosets S) (g : G)
    (h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q) : S :=
  ⟨Quotient.out q * g * (Quotient.out q)⁻¹, by
    have hrel := Quotient.exact (s := QuotientGroup.rightRel S)
      (h.trans (Quotient.out_eq q).symm)
    change (QuotientGroup.rightRel S).r (Quotient.out q * g) (Quotient.out q) at hrel
    rw [QuotientGroup.rightRel_apply] at hrel
    simpa [mul_inv_rev, mul_assoc] using (S.inv_mem hrel)⟩

theorem rightCosetCorrection_fixed (S : Subgroup G) (q : RightCosets S) (g : G)
    (h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q) :
    rightCosetCorrection S (Quotient.out q * g) = fixedConjugate S q g h := by
  apply Subtype.ext
  have hout : rightCosetOut S (Quotient.out q * g) = Quotient.out q := by
    exact congrArg Quotient.out h
  change (Quotient.out q * g) * (rightCosetOut S (Quotient.out q * g))⁻¹ =
    Quotient.out q * g * (Quotient.out q)⁻¹
  rw [hout]

noncomputable def coindVEquivQuotient
    (S : Subgroup G) (ρ : Representation k S A) :
    Representation.coindV S.subtype ρ ≃ₗ[k] (RightCosets S → A) where
  toFun f q := f.1 (Quotient.out q)
  invFun x := by
    refine ⟨fun g => ρ (rightCosetCorrection S g)
      (x (Quotient.mk (QuotientGroup.rightRel S) g)), ?_⟩
    intro s h
    have hq := rightCoset_mk_smul S s h
    have hc := rightCosetCorrection_smul S s h
    simp [hq, hc]
  map_add' f f' := by
    ext q
    rfl
  map_smul' a f := by
    ext q
    rfl
  left_inv f := by
    ext g
    change ρ (rightCosetCorrection S g) (f.1 (rightCosetOut S g)) = f.1 g
    rw [← f.2 (rightCosetCorrection S g) (rightCosetOut S g)]
    simpa using congrArg f.1 (subgroupSubtype_correction_mul_out S g)
  right_inv x := by
    ext q
    change ρ (rightCosetCorrection S (Quotient.out q))
        (x (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q))) = x q
    rw [rightCosetCorrection_out S q, Quotient.out_eq q]
    simp

def coindCoordinateEnd (S : Subgroup G) (ρ : Representation k S A) (g : G) :
    (RightCosets S → A) →ₗ[k] (RightCosets S → A) :=
  (coindVEquivQuotient S ρ).conj ((Representation.coind S.subtype ρ) g)

theorem coindCoordinateEnd_apply (S : Subgroup G) (ρ : Representation k S A) (g : G)
    (x : RightCosets S → A) (q : RightCosets S) :
    coindCoordinateEnd S ρ g x q =
      ρ (rightCosetCorrection S (Quotient.out q * g))
        (x (Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g))) := by
  rfl

variable [Finite G] [FiniteDimensional k A]

theorem coindCoordinateEnd_trace_formula
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation k S A) (g : G) :
    LinearMap.trace k (RightCosets S → A) (coindCoordinateEnd S ρ g) =
      ∑ q : RightCosets S,
        if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
          ρ.character (fixedConjugate S q g h)
        else
          0 := by
  classical
  let κ := Module.Free.ChooseBasisIndex k A
  let b : Module.Basis κ k A := Module.Free.chooseBasis k A
  rw [trace_pi_map_perm b
    (fun q : RightCosets S => Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g))
    (fun q : RightCosets S => ρ (rightCosetCorrection S (Quotient.out q * g)))
    (coindCoordinateEnd S ρ g)]
  · refine Finset.sum_congr rfl ?_
    intro q hq
    by_cases h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q
    · simp [h, rightCosetCorrection_fixed S q g h, Representation.character]
    · simp [h]
  · intro x q
    exact coindCoordinateEnd_apply S ρ g x q

theorem coind_character_formula
    (S : Subgroup G) [DecidablePred (· ∈ S)] (ρ : Representation k S A) (g : G) :
    (Representation.coind S.subtype ρ).character g =
      ∑ q : RightCosets S,
        if h : Quotient.mk (QuotientGroup.rightRel S) (Quotient.out q * g) = q then
          ρ.character (fixedConjugate S q g h)
        else
          0 := by
  classical
  rw [Representation.character, ← coindCoordinateEnd_trace_formula S ρ g]
  exact (LinearMap.trace_conj'
    ((Representation.coind S.subtype ρ) g) (coindVEquivQuotient S ρ)).symm

end Kourovka2135.CoinducedCharacterFormula

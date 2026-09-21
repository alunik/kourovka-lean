import Kourovka2135.Vendor.CFSG.Frattini.Core
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Every nontrivial finite p-group admits an actual surjective character
to the additive group of the prime field. No commutativity premise is
needed: the character factors through the checked elementary abelian
Frattini quotient. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.FinitePGroupCharacter

open scoped IsMulCommutative

/-- A nontrivial finite group has a proper Frattini subgroup. -/
theorem frattini_ne_top (P : Type*) [Group P] [Finite P] [Nontrivial P] :
    frattini P ≠ ⊤ := by
  intro h
  have hb : (⊥ : Subgroup P) = ⊤ :=
    frattini_nongenerating (by simpa only [bot_sup_eq] using h)
  exact bot_ne_top hb

/-- A nonzero elementary abelian group has a surjective prime-field
character, without any finite-dimensionality assumption. -/
theorem exists_surjective_of_elementaryAbelian (p : ℕ) [Fact p.Prime]
    (A : Type*) [Group A] [Nontrivial A] [IsElementaryAbelian p A] :
    ∃ χ : A →* Multiplicative (ZMod p), Function.Surjective χ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : Additive A)
  obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hx
  let χ : A →* Multiplicative (ZMod p) := {
    toFun := fun a => Multiplicative.ofAdd (ell (Additive.ofMul a))
    map_one' := by
      change ell 0 = 0
      exact map_zero ell
    map_mul' := fun a b => by
      change ell (Additive.ofMul a + Additive.ofMul b) =
        ell (Additive.ofMul a) + ell (Additive.ofMul b)
      exact map_add ell _ _ }
  refine ⟨χ, fun y => ⟨(y.toAdd • x).toMul, ?_⟩⟩
  change Multiplicative.ofAdd (ell (y.toAdd • x)) = y
  rw [map_smul, hell, smul_eq_mul, mul_one]
  rfl

/-- Every nontrivial finite p-group has a surjective homomorphism to the
additive group of ZMod p. The input group need not be abelian. -/
theorem exists_surjective (p : ℕ) (hp : p.Prime)
    (P : Type*) [Group P] [Finite P] [Nontrivial P] (hP : IsPGroup p P) :
    ∃ χ : P →* Multiplicative (ZMod p), Function.Surjective χ := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (IsPGroup p P) := ⟨hP⟩
  let : IsElementaryAbelian p (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini
  let : Nontrivial (P ⧸ frattini P) :=
    QuotientGroup.nontrivial_iff.mpr (frattini_ne_top P)
  obtain ⟨χ, hχ⟩ := exists_surjective_of_elementaryAbelian p (P ⧸ frattini P)
  exact ⟨χ.comp (QuotientGroup.mk' (frattini P)),
    hχ.comp (QuotientGroup.mk'_surjective (frattini P))⟩

/-- The character can be recorded as both nontrivial and surjective. -/
theorem exists_nontrivial_surjective (p : ℕ) (hp : p.Prime)
    (P : Type*) [Group P] [Finite P] [Nontrivial P] (hP : IsPGroup p P) :
    ∃ χ : P →* Multiplicative (ZMod p), χ ≠ 1 ∧ Function.Surjective χ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨χ, hχ⟩ := exists_surjective p hp P hP
  refine ⟨χ, ?_, hχ⟩
  intro h
  obtain ⟨x, hx⟩ := hχ (Multiplicative.ofAdd (1 : ZMod p))
  rw [h] at hx
  change (0 : ZMod p) = 1 at hx
  exact zero_ne_one hx

end Kourovka2135.FinitePGroupCharacter

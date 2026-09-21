import Kourovka2135.Vendor.CFSG.PCore.PPrimeCore
import Mathlib.GroupTheory.Index

/-!
# Quotienting by the p′-core

The cardinality of a subgroup preimage is the product of the kernel and subgroup
cardinalities. Coprimality therefore passes to preimages when the kernel has
coprime cardinality, proving that the quotient by the p′-core has trivial p′-core.
-/

set_option autoImplicit false
universe u v

namespace Kourovka2135

/-- The cardinality formula for the preimage of a subgroup under a surjective homomorphism.
The formula uses `Nat.card` and is valid without finiteness assumptions. -/
theorem card_comap_eq_card_ker_mul
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) f.ker (K.comap f)
    bot_le (Subgroup.ker_le_comap f K)
  simpa only [Subgroup.relIndex_bot_left, Subgroup.relIndex_ker,
    Subgroup.map_comap_eq_self_of_surjective hf] using h.symm

/-- Coprimality of kernel and subgroup cardinalities passes to the preimage. -/
theorem coprime_card_comap_of_surjective
    {G : Type u} {H : Type v} [Group G] [Group H] {p : ℕ}
    (f : G →* H) (hf : Function.Surjective f) (K : Subgroup H)
    (hker : p.Coprime (Nat.card f.ker)) (hK : p.Coprime (Nat.card K)) :
    p.Coprime (Nat.card (K.comap f)) := by
  rw [card_comap_eq_card_ker_mul f hf K]
  exact hker.mul_right hK

/-- The quotient of a finite group by its p′-core has trivial p′-core. -/
theorem pPrimeCore_quotient_eq_bot
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
  apply pPrimeCore_eq_bot_iff.mpr
  intro K hKnormal hKcoprime
  let C : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective C
  have hker : p.Coprime (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using
      (pPrimeCore_coprime_card (G := G) (p := p))
  have hpreCoprime : p.Coprime (Nat.card (K.comap q)) :=
    coprime_card_comap_of_surjective q hq K hker hKcoprime
  have hpreNormal : (K.comap q).Normal := hKnormal.comap q
  have hpreLe : K.comap q ≤ C :=
    le_sSup ⟨hpreNormal, hpreCoprime⟩
  have hpreImage : (K.comap q).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hpreLe
  rw [Subgroup.map_comap_eq_self_of_surjective hq] at hpreImage
  exact hpreImage

end Kourovka2135

import Kourovka2135.Complement
import Kourovka2135.Vendor.CFSG.PCore.PPrimeCore
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Normal complements in a group with trivial p′-core

A normal p-complement consists exactly of the elements whose orders are coprime
to p. It is therefore unique and characteristic. Its image from a normal
subgroup into the ambient group is normal, so a trivial ambient p′-core forces
the complement to be trivial and the subgroup to be a p-group.

The cardinality and index hypotheses already supply the needed finiteness;
no solubility assumption or finite ambient-group instance is used.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135

variable {G : Type u} [Group G] {p : ℕ}

/-- Membership in a normal p-complement is characterized by element order. -/
theorem mem_normalPComplement_iff_orderOf_coprime (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hcard : (Nat.card N).Coprime p)
    (hindex : ∃ n : ℕ, N.index = p ^ n) (x : G) :
    x ∈ N ↔ (orderOf x).Coprime p := by
  constructor
  · intro hx
    exact Nat.Coprime.of_dvd_left (N.orderOf_dvd_natCard hx) hcard
  · intro hx
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hindex
    let f : G →* G ⧸ N := QuotientGroup.mk' N
    have hquot : IsPGroup p (G ⧸ N) := IsPGroup.of_card (by
      rw [← N.index_eq_card]
      exact hn)
    apply (QuotientGroup.eq_one_iff x).mp
    change f x = 1
    by_contra hne
    have hd : p ∣ orderOf x :=
      (hquot.dvd_orderOf hne).trans (orderOf_map_dvd f x)
    exact (hp.coprime_iff_not_dvd.mp hx.symm) hd

/-- The normal p-complement, when it exists, is unique. -/
theorem normalPComplement_unique (hp : p.Prime)
    (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNcard : (Nat.card N).Coprime p) (hNindex : ∃ n : ℕ, N.index = p ^ n)
    (hMcard : (Nat.card M).Coprime p) (hMindex : ∃ n : ℕ, M.index = p ^ n) :
    N = M := by
  ext x
  exact (mem_normalPComplement_iff_orderOf_coprime hp N hNcard hNindex x).trans
    (mem_normalPComplement_iff_orderOf_coprime hp M hMcard hMindex x).symm

/-- Every automorphism preserves the normal p-complement. -/
theorem normalPComplement_characteristic (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hcard : (Nat.card N).Coprime p)
    (hindex : ∃ n : ℕ, N.index = p ^ n) : N.Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro φ x hx
  obtain ⟨y, hy, rfl⟩ := hx
  apply (mem_normalPComplement_iff_orderOf_coprime hp N hcard hindex (φ y)).mpr
  rw [φ.orderOf_eq]
  exact (mem_normalPComplement_iff_orderOf_coprime hp N hcard hindex y).mp hy

/-- A normal subgroup with a normal p-complement is a p-group when the ambient
p′-core is trivial. No solubility or ambient finiteness assumption is needed. -/
theorem isPGroup_of_normal_hasNormalPComplement_of_pPrimeCore_eq_bot
    (hp : p.Prime) (H : Subgroup G) [H.Normal]
    (hH : HasNormalPComplement p H) (hcore : pPrimeCore p G = ⊥) :
    IsPGroup p H := by
  obtain ⟨N, hN, hcard, n, hindex⟩ := hH
  let : N.Normal := hN
  let : N.Characteristic := normalPComplement_characteristic hp N hcard ⟨n, hindex⟩
  have hmapCoprime : p.Coprime (Nat.card (N.map H.subtype)) := by
    simpa only [Subgroup.card_subtype] using hcard.symm
  have hmapBot : N.map H.subtype = ⊥ :=
    (pPrimeCore_eq_bot_iff.mp hcore) _ inferInstance hmapCoprime
  have hNbot : N = ⊥ := Subgroup.map_injective H.subtype_injective (by
    simpa only [Subgroup.map_bot] using hmapBot)
  apply IsPGroup.of_card (n := n)
  simpa only [hNbot, Subgroup.index_bot] using hindex

end Kourovka2135

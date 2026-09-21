/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Kourovka2135.Vendor.CFSG.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.PUnit

/-! Ordinary Hall subgroup interfaces obtained from the proven CFSG source closure. -/

namespace Kourovka2135.Hall

universe u

open scoped Pointwise

variable {G : Type u} [Group G] [Finite G]

/-- A π-subgroup of a finite soluble group is contained in a Hall π-subgroup. -/
theorem exists_hall_containing (hsolv : Group.IsSolvable G) (π : Set Nat.Primes)
    (K : Subgroup G) (hK : IsPiSubgroup π K) :
    ∃ H : Subgroup G, IsHallSubgroup π H ∧ K ≤ H := by
  let : MulDistribMulAction PUnit.{1} G := {
    smul := fun _ g => g
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcoprime : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card G) := by simp
  have hInv : IsInvariant PUnit.{1} G K := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨H, hHall, _, hKH⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (A := PUnit.{1}) hsolv hcoprime π K hK hInv
  exact ⟨H, hHall, hKH⟩

/-- Hall π-subgroups exist in finite soluble groups. -/
theorem exists_hall (hsolv : Group.IsSolvable G) (π : Set Nat.Primes) :
    ∃ H : Subgroup G, IsHallSubgroup π H := by
  have hbot : IsPiSubgroup π (⊥ : Subgroup G) := by
    intro p hp
    exact False.elim (p.property.not_dvd_one (by simpa using hp))
  obtain ⟨H, hH, _⟩ := exists_hall_containing hsolv π ⊥ hbot
  exact ⟨H, hH⟩

/-- Hall π-subgroups of a finite soluble group are conjugate. -/
theorem hall_conjugate (hsolv : Group.IsSolvable G) {π : Set Nat.Primes}
    {H₁ H₂ : Subgroup G} (h₁ : IsHallSubgroup π H₁) (h₂ : IsHallSubgroup π H₂) :
    ∃ g : G, H₂ = H₁.map (MulAut.conj g).toMonoidHom :=
  exists_conj_eq_of_isHallSubgroup_of_solvable hsolv h₁ h₂

/-- Every π-subgroup lies in a conjugate of any chosen Hall π-subgroup. -/
theorem exists_le_conjugate_hall (hsolv : Group.IsSolvable G) {π : Set Nat.Primes}
    (K H : Subgroup G) (hK : IsPiSubgroup π K) (hH : IsHallSubgroup π H) :
    ∃ g : G, K ≤ H.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨L, hL, hKL⟩ := exists_hall_containing hsolv π K hK
  obtain ⟨g, hg⟩ := hall_conjugate hsolv hH hL
  exact ⟨g, hg ▸ hKL⟩

/-- If a normal subgroup and a chosen Hall subgroup generate the ambient group,
the Hall containment conjugator can be chosen in that normal subgroup. -/
theorem exists_le_conjugate_hall_by_normal_subgroup
    (hsolv : Group.IsSolvable G) {π : Set Nat.Primes}
    (K H P : Subgroup G) [P.Normal]
    (hK : IsPiSubgroup π K) (hH : IsHallSubgroup π H) (hsup : P ⊔ H = ⊤) :
    ∃ g ∈ P, K ≤ H.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_le_conjugate_hall hsolv K H hK hH
  have hgSup : g ∈ P ⊔ H := by simp [hsup]
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hgSup
  have hconj : H.map (MulAut.conj (a * b)).toMonoidHom =
      H.map (MulAut.conj a).toMonoidHom := by
    change MulAut.conj (a * b) • H = MulAut.conj a • H
    rw [map_mul, mul_smul, Subgroup.conj_smul_eq_self_of_mem hb]
  exact ⟨a, ha, hconj ▸ hg⟩

end Kourovka2135.Hall

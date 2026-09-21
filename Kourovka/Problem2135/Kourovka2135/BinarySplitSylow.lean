import Kourovka2135.SLTwoUnipotent
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-! Actual cyclic Sylow subgroups at odd split primes of SL2(F).

A cyclic subgroup of prime-to-p index supplies an actual cyclic Sylow
p-subgroup. For the split torus in SL2(F), the index is q(q+1), prime to
any odd prime dividing q-1. No subgroup classification is assumed.
The proof works over every finite field, so characteristic two is not
needed as an additional premise.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinarySplitSylow

section Generic

variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A cyclic subgroup of p-prime index makes every actual Sylow p-subgroup cyclic. -/
theorem isCyclic_sylow_of_cyclic_index
    (H : Subgroup G) [IsCyclic H] (hindex : ¬ p ∣ H.index) (P : Sylow p G) :
    IsCyclic P := by
  let Q : Sylow p H := Sylow.nonempty.some
  let T : Subgroup G := (Q : Subgroup H).map H.subtype
  have hT : IsPGroup p T := Q.isPGroup'.map H.subtype
  have hTindex : ¬ p ∣ T.index := by
    dsimp [T]
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul Q.not_dvd_index hindex
  let P₀ : Sylow p G := hT.toSylow hTindex
  let : IsCyclic T :=
    isCyclic_of_surjective (H.subtype.subgroupMap (Q : Subgroup H))
      (H.subtype.subgroupMap_surjective (Q : Subgroup H))
  let : IsCyclic P₀ := by change IsCyclic T; infer_instance
  exact isCyclic_of_surjective (P₀.equiv P).toMonoidHom (P₀.equiv P).surjective

/-- Every actual p-subgroup also inherits cyclicity. -/
theorem isCyclic_pSubgroup_of_cyclic_index
    (H : Subgroup G) [IsCyclic H] (hindex : ¬ p ∣ H.index)
    (S : Subgroup G) (hS : IsPGroup p S) : IsCyclic S := by
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  let : IsCyclic P := isCyclic_sylow_of_cyclic_index H hindex P
  exact Subgroup.isCyclic_of_le hSP

end Generic

section SplitTorus

variable (F : Type*) [Field F] [Finite F]

omit [Finite F] in
/-- The actual split torus is the actual multiplicative group of F. -/
def torusEquiv : Fˣ ≃* SLTwo.Torus F :=
  MonoidHom.ofInjective (SLTwo.torHom_injective (K := F))

theorem torus_isCyclic : IsCyclic (SLTwo.Torus F) :=
  isCyclic_of_surjective (torusEquiv F).toMonoidHom (torusEquiv F).surjective

theorem card_torus : Nat.card (SLTwo.Torus F) = Nat.card F - 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  calc
    Nat.card (SLTwo.Torus F) = Nat.card Fˣ :=
      (Nat.card_congr (torusEquiv F).toEquiv).symm
    _ = Nat.card F - 1 := by
      simpa only [Nat.card_eq_fintype_card] using Fintype.card_units F

theorem one_lt_card_field : 1 < Nat.card F := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

/-- The index is computed in the actual determinant-one matrix group. -/
theorem index_torus : (SLTwo.Torus F).index = Nat.card F * (Nat.card F + 1) := by
  have hq := one_lt_card_field F
  have hmul := (SLTwo.Torus F).card_mul_index
  rw [card_torus, SLTwo.sl2_card_formula] at hmul
  have hfactor : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have hsub : Nat.card F - 1 + 1 = Nat.card F := Nat.sub_add_cancel (by omega)
    have hsq : 1 ≤ Nat.card F ^ 2 := by nlinarith
    have hsqsub : Nat.card F ^ 2 - 1 + 1 = Nat.card F ^ 2 := Nat.sub_add_cancel hsq
    nlinarith
  apply Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt hq)
  calc
    (Nat.card F - 1) * (SLTwo.Torus F).index =
        Nat.card F * (Nat.card F ^ 2 - 1) := hmul
    _ = (Nat.card F - 1) * (Nat.card F * (Nat.card F + 1)) := by
      rw [hfactor]
      ring

variable {r : ℕ} [Fact r.Prime]

/-- An odd split prime is prime to the actual torus index. -/
theorem not_dvd_index_torus (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1) :
    ¬ r ∣ (SLTwo.Torus F).index := by
  have hq := one_lt_card_field F
  have hrq : ¬ r ∣ Nat.card F := by
    intro h
    have hdiv : r ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub h hrSplit
    have heq : Nat.card F - (Nat.card F - 1) = 1 := by omega
    rw [heq] at hdiv
    exact (Fact.out : r.Prime).not_dvd_one hdiv
  have hrqp : ¬ r ∣ Nat.card F + 1 := by
    intro h
    have hdiv : r ∣ Nat.card F + 1 - (Nat.card F - 1) := Nat.dvd_sub h hrSplit
    have heq : Nat.card F + 1 - (Nat.card F - 1) = 2 := by omega
    rw [heq] at hdiv
    have hrone : r = 1 :=
      Nat.eq_one_of_dvd_coprimes hrOdd.coprime_two_right (dvd_refl r) hdiv
    exact (Fact.out : r.Prime).ne_one hrone
  rw [index_torus]
  exact (Fact.out : r.Prime).not_dvd_mul hrq hrqp

/-- Every actual Sylow subgroup at an odd split prime is cyclic. -/
theorem sylow_isCyclic (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (P : Sylow r (SLTwo.SL2 F)) : IsCyclic P := by
  let : IsCyclic (SLTwo.Torus F) := torus_isCyclic F
  exact isCyclic_sylow_of_cyclic_index (SLTwo.Torus F)
    (not_dvd_index_torus F hrOdd hrSplit) P

/-- The same conclusion for every actual r-subgroup, without maximality. -/
theorem pSubgroup_isCyclic (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (S : Subgroup (SLTwo.SL2 F)) (hS : IsPGroup r S) : IsCyclic S := by
  let : IsCyclic (SLTwo.Torus F) := torus_isCyclic F
  exact isCyclic_pSubgroup_of_cyclic_index (SLTwo.Torus F)
    (not_dvd_index_torus F hrOdd hrSplit) S hS

/-- Sylow subgroups of an actual subgroup inherit cyclicity through the actual inclusion. -/
theorem subgroup_sylow_isCyclic (hrOdd : Odd r) (hrSplit : r ∣ Nat.card F - 1)
    (H : Subgroup (SLTwo.SL2 F)) (P : Sylow r H) : IsCyclic P := by
  let : IsCyclic ((P : Subgroup H).map H.subtype) :=
    pSubgroup_isCyclic F hrOdd hrSplit ((P : Subgroup H).map H.subtype)
      (P.isPGroup'.map H.subtype)
  apply isCyclic_of_injective (H.subtype.subgroupMap (P : Subgroup H))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ((P : Subgroup H).map H.subtype) => (z : SLTwo.SL2 F)) h

end SplitTorus

end Kourovka2135.BinarySplitSylow

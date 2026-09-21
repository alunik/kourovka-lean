import Kourovka2135.GoodSetLifting
import Mathlib.Tactic.Group

/-! Generic reflector identities produce actual single values of every outer word.

If u³=1 and a inverts u, then [a,u⁻¹au]=u in the paper convention.
Universal single-value membership of a therefore gives that of u. A
commutator of two members of a generating-good set is such a universal
single-value element. No multiplication closure of word values is used.
-/

set_option autoImplicit false

namespace Kourovka2135.UniversalWordReflector

variable {G : Type*} [Group G]

/-- The generic identity needs u³=1 and inversion, but no order condition on a. -/
theorem paperCommutator_conjugate_of_cube_eq_one (u a : G)
    (hu : u ^ 3 = 1) (ha : a⁻¹ * u * a = u⁻¹) :
    paperCommutator a (u⁻¹ * a * u) = u := by
  have hu' : u * u * u = 1 := by simpa [pow_succ] using hu
  calc
    paperCommutator a (u⁻¹ * a * u) =
        a⁻¹ * u⁻¹ * (a⁻¹ * u * a) * u⁻¹ * a * u := by
      unfold paperCommutator
      group
    _ = a⁻¹ * (u * u * u)⁻¹ * a * u := by rw [ha]; group
    _ = u := by rw [hu']; simp

/-- A commutator of two universal single-value elements is again universal. -/
theorem universal_commutator (b c : G)
    (hb : ∀ w : OuterWord, b ∈ w.values G)
    (hc : ∀ w : OuterWord, c ∈ w.values G) :
    ∀ w : OuterWord, paperCommutator b c ∈ w.values G := by
  intro w
  cases w with
  | leaf => exact ⟨(paperCommutator b c : G), rfl⟩
  | bracket left right =>
      exact (OuterWord.mem_values_bracket left right _).mpr
        ⟨b, hb left, c, hc right, rfl⟩

/-- Universal membership of the actual inverter gives universal membership of u. -/
theorem universal_of_inverter (u a : G)
    (hu : u ^ 3 = 1) (ha : a⁻¹ * u * a = u⁻¹)
    (haValues : ∀ w : OuterWord, a ∈ w.values G) :
    ∀ w : OuterWord, u ∈ w.values G := by
  intro w
  cases w with
  | leaf => exact ⟨u, rfl⟩
  | bracket left right =>
      exact (OuterWord.mem_values_bracket left right u).mpr
        ⟨a, haValues left, u⁻¹ * a * u,
          right.conj_mem_values (haValues right) u,
          paperCommutator_conjugate_of_cube_eq_one u a hu ha⟩

/-- Actual generating-good-set inputs supply every required single-word value.
The resulting commutator need not itself belong to the given set Y. -/
theorem universal_of_good_set_commutator
    (Y : Set G) (hY : IsGeneratingGoodSet Y)
    (b : G) (hb : b ∈ Y) (c : G) (hc : c ∈ Y) (u : G)
    (hu : u ^ 3 = 1)
    (ha : (paperCommutator b c)⁻¹ * u * paperCommutator b c = u⁻¹) :
    ∀ w : OuterWord, u ∈ w.values G :=
  universal_of_inverter u (paperCommutator b c) hu ha
    (universal_commutator b c (fun w => hY.subset_values w hb)
      (fun w => hY.subset_values w hc))

/-- The order-three form used by the reflector induction. -/
theorem universal_of_good_set_commutator_order_three
    (Y : Set G) (hY : IsGeneratingGoodSet Y)
    (b : G) (hb : b ∈ Y) (c : G) (hc : c ∈ Y) (u : G)
    (hu : orderOf u = 3)
    (ha : (paperCommutator b c)⁻¹ * u * paperCommutator b c = u⁻¹) :
    ∀ w : OuterWord, u ∈ w.values G := by
  apply universal_of_good_set_commutator Y hY b hb c hc u ?_ ha
  rw [← hu]
  exact pow_orderOf_eq_one u

end Kourovka2135.UniversalWordReflector

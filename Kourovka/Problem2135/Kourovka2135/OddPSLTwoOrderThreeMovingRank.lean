import Kourovka2135.OddPSLTwoTorusMovingRank

/-! Two independent three-cycles for an actual split torus element.

The six vectors are actual translates of a nonzero root-character vector.
Their parameters have distinct squares: cubing a possible cross-cycle
equality would force the second representative to have sixth power one.
Thus the actual moving operator has four independent differences.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.OddPSLTwoOrderThreeMovingRank

open OddPSLTwoProjectiveChart OddPSLTwoPermutationHeart OddPSLTwoCharacterOrbit
open OddPSLTwoTorusMovingRank

variable (F : Type u) [Field F]

def cycleParameter (r s : Fˣ) (i : Bool × Fin 3) : Fˣ :=
  (if i.1 then s else 1) * r ^ i.2.val

theorem square_cube (r a : Fˣ) (hr : r ^ 3 = 1) (j : ℕ) :
    ((a * r ^ j) ^ 2) ^ 3 = a ^ 6 := by
  rw [mul_pow, mul_pow, ← pow_mul a, pow_right_comm (r ^ j) 2 3,
    pow_right_comm r j 3, hr]
  simp

theorem cycleParameter_squares_injective (r s : Fˣ)
    (hr : orderOf r = 3) (hs : s ^ 6 ≠ 1) :
    Function.Injective (fun i : Bool × Fin 3 => cycleParameter F r s i ^ 2) := by
  have hr3 : r ^ 3 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hr2 : orderOf (r ^ 2) = 3 := by
    rw [orderOf_pow' r (by decide : (2 : ℕ) ≠ 0), hr]
    decide
  have hp : Function.Injective (fun i : Fin 3 => (r ^ i.val) ^ 2) := by
    intro i j he
    apply Fin.ext
    change (r ^ i.val) ^ 2 = (r ^ j.val) ^ 2 at he
    rw [pow_right_comm r i.val 2, pow_right_comm r j.val 2] at he
    exact pow_injOn_Iio_orderOf (by simpa only [Set.mem_Iio, hr2] using i.isLt)
      (by simpa only [Set.mem_Iio, hr2] using j.isLt) he
  rintro ⟨b, i⟩ ⟨c, j⟩ he
  change cycleParameter F r s (b, i) ^ 2 = cycleParameter F r s (c, j) ^ 2 at he
  have hc : (if b then s else 1) ^ 6 = (if c then s else 1) ^ 6 := by
    calc
      _ = (cycleParameter F r s (b, i) ^ 2) ^ 3 :=
        (square_cube F r _ hr3 i.val).symm
      _ = (cycleParameter F r s (c, j) ^ 2) ^ 3 := congrArg (fun a : Fˣ => a ^ 3) he
      _ = _ := square_cube F r _ hr3 j.val
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (hs (by simpa using hc.symm))
    · exact False.elim (hs (by simpa using hc))
    · rfl
  subst c
  have hij : i = j := hp (mul_left_cancel (a := (if b then s else 1) ^ 2)
    (by simpa only [cycleParameter, mul_pow] using he))
  exact Prod.ext rfl hij

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable [Fintype F] [FiniteDimensional k V]
variable (ρ : Representation k (Q F) V) (χ : Multiplicative F →* kˣ) (v : V)

/-- Two genuine three-cycles give four moving dimensions. -/
theorem four_le_finrank_moving_of_sixth_power
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ)
    (r s : Fˣ) (hr : orderOf r = 3) (hs : s ^ 6 ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (ρ (projectiveTorusHom F r) - LinearMap.id)) := by
  classical
  let w (i : Bool × Fin 3) : V := translate F ρ v (cycleParameter F r s i)
  let rep (i : Bool × Fin 3) : Bool × Fin 3 := (i.1, 0)
  have hli : LinearIndependent k w :=
    translates_linearIndependent F ρ χ v hcard hχ hv hweight
      (cycleParameter F r s) (cycleParameter_squares_injective F r s hr hs)
  have he := IndependentOrbitMovingRank.card_le_finrank
    (ρ (projectiveTorusHom F r)) w hli rep (fun _ => rfl)
    (fun i => ⟨i.2.val, by
      dsimp only [w, rep, cycleParameter]
      rw [Fin.val_zero, pow_zero, mul_one, iterate_translate]⟩)
  have hcardrep : Fintype.card {i : Bool × Fin 3 // rep i ≠ i} = 4 := by
    change Fintype.card {i : Bool × Fin 3 // (i.1, (0 : Fin 3)) ≠ i} = 4
    decide +kernel
  rw [hcardrep] at he
  exact he

omit [AddCommGroup V] [Module k V] [FiniteDimensional k V] in
theorem exists_sixth_power_ne_one (hsize : 7 < Fintype.card F) :
    ∃ s : Fˣ, s ^ 6 ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨s, fun he => ?_⟩
  have hord : orderOf s = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card, Fintype.card_units]
  have hle : orderOf s ≤ 6 := Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one he)
  omega

/-- Every actual split element represented by an order-three unit has
moving rank at least four once the field has more than seven elements. -/
theorem four_le_finrank_moving
    (hcard : (Fintype.card F : k) ≠ 0) (hχ : χ ≠ 1) (hv : v ≠ 0)
    (hweight : v ∈ weightSpace (ρ.comp (unipotentHom F)) χ)
    (hsize : 7 < Fintype.card F) (r : Fˣ) (hr : orderOf r = 3) :
    4 ≤ Module.finrank k (LinearMap.range (ρ (projectiveTorusHom F r) - LinearMap.id)) := by
  obtain ⟨s, hs⟩ := exists_sixth_power_ne_one F hsize
  exact four_le_finrank_moving_of_sixth_power F ρ χ v hcard hχ hv hweight r s hr hs

end Kourovka2135.OddPSLTwoOrderThreeMovingRank

import Kourovka2135.BinaryWalshBound
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Dimension form of the binary quadratic surjectivity criterion. -/
set_option autoImplicit false
namespace Kourovka2135.BinaryFourier
open Classical
variable {V Z : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup Z] [Module (ZMod 2) Z] [Fintype V] [Fintype Z]

/-- Polar rank at least twice the target dimension fills every target, even
when the scalar polar forms have different radicals. -/
theorem quadratic_surjective_of_polar_rank (Q : QuadraticMap (ZMod 2) V Z)
    (hr : ∀ ell : Module.Dual (ZMod 2) Z, ell ≠ 0 →
      2 * Module.finrank (ZMod 2) Z ≤
        Module.finrank (ZMod 2) (ell.compQuadraticMap Q).polarBilin.range) :
    Function.Surjective Q := by
  classical
  letI : Finite (Module.Dual (ZMod 2) Z) :=
    Finite.of_injective (fun ell : Module.Dual (ZMod 2) Z => (ell : Z → ZMod 2))
      DFunLike.coe_injective
  letI : Fintype (Module.Dual (ZMod 2) Z) := Fintype.ofFinite _
  apply quadratic_surjective_of_radical_card_bound
  intro ell hell
  let B := (ell.compQuadraticMap Q).polarBilin
  letI : Fintype B.ker := Fintype.ofFinite _
  have he (h : V) : h ∈ B.ker ↔ ∀ x : V, ell (Q.polarBilin h x) = 0 := by
    rw [LinearMap.mem_ker, LinearMap.ext_iff]
    simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.compQuadraticMap_apply, map_sub, LinearMap.zero_apply]
  have hc : (Finset.univ.filter fun h : V => ∀ x : V, ell (Q.polarBilin h x) = 0).card =
      Fintype.card B.ker := by
    rw [Fintype.card_subtype]
    simp only [he]
  rw [hc, Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) Z),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := B.ker),
    Module.card_eq_pow_finrank (K := ZMod 2) (V := V)]
  simp only [ZMod.card, Subspace.dual_finrank_eq]
  rw [← pow_mul, ← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hd := B.finrank_range_add_finrank_ker
  have hh : 2 * Module.finrank (ZMod 2) Z ≤ Module.finrank (ZMod 2) B.range := hr ell hell
  omega

end Kourovka2135.BinaryFourier

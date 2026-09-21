import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Fixed vectors detected by diagonal coordinates.

An injective equivariant coordinate map identifies fixed vectors with a
subspace of the coordinates of weight one. This elementary statement does
not assume any group-cohomology comparison or representation classification.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.DiagonalFixedCoordinates

variable {k : Type u} [Field k]
variable {ι : Type v} {V : Type w} [AddCommGroup V] [Module k V]

/-- The indices whose diagonal eigenvalue is one. -/
abbrev FixedIndex (χ : ι → k) := {i : ι // χ i = 1}

instance fixedIndexFintype [Finite ι] (χ : ι → k) : Fintype (FixedIndex χ) :=
  Fintype.ofFinite _

variable (T : V →ₗ[k] V) (q : V →ₗ[k] (ι → k)) (χ : ι → k)

/-- Restrict the coordinates of a fixed vector to its weight-one indices. -/
def fixedCoordinate : (T - LinearMap.id).ker →ₗ[k] (FixedIndex χ → k) where
  toFun v i := q v.val i.val
  map_add' v z := by ext i; simp
  map_smul' c v := by ext i; simp

@[simp] theorem fixedCoordinate_apply (v : (T - LinearMap.id).ker) (i : FixedIndex χ) :
    fixedCoordinate T q χ v i = q v.val i.val := rfl

theorem apply_eq_self (v : (T - LinearMap.id).ker) : T v.val = v.val := by
  have hv := v.property
  change T v.val - v.val = 0 at hv
  exact sub_eq_zero.mp hv

/-- Equivariance forces every non-unit-weight coordinate of a fixed vector to vanish. -/
theorem coordinate_eq_zero_of_ne_one
    (hdiag : ∀ v : V, ∀ i : ι, q (T v) i = χ i * q v i)
    (v : (T - LinearMap.id).ker) (i : ι) (hi : χ i ≠ 1) : q v.val i = 0 := by
  have he := hdiag v.val i
  rw [apply_eq_self T v] at he
  have hm : (χ i - 1) * q v.val i = 0 := by
    rw [sub_mul, one_mul, ← he, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hi)

/-- Restricting to the weight-one coordinates is injective on the fixed subspace. -/
theorem fixedCoordinate_injective (hq : Function.Injective q)
    (hdiag : ∀ v : V, ∀ i : ι, q (T v) i = χ i * q v i) :
    Function.Injective (fixedCoordinate T q χ) := by
  intro x y hxy
  apply Subtype.ext
  apply hq
  funext i
  by_cases hi : χ i = 1
  · exact congrFun hxy ⟨i, hi⟩
  · rw [coordinate_eq_zero_of_ne_one T q χ hdiag x i hi,
      coordinate_eq_zero_of_ne_one T q χ hdiag y i hi]

/-- A finite diagonal coordinate set implies finite-dimensional fixed vectors. -/
theorem finiteDimensional_fixed [Finite ι] (hq : Function.Injective q)
    (hdiag : ∀ v : V, ∀ i : ι, q (T v) i = χ i * q v i) :
    FiniteDimensional k (T - LinearMap.id).ker :=
  FiniteDimensional.of_injective (fixedCoordinate T q χ)
    (fixedCoordinate_injective T q χ hq hdiag)

/-- The fixed-space dimension is bounded by the number of weight-one coordinates. -/
theorem finrank_fixed_le [Finite ι] (hq : Function.Injective q)
    (hdiag : ∀ v : V, ∀ i : ι, q (T v) i = χ i * q v i) :
    Module.finrank k (T - LinearMap.id).ker ≤ Fintype.card (FixedIndex χ) := by
  calc
    Module.finrank k (T - LinearMap.id).ker ≤ Module.finrank k (FixedIndex χ → k) :=
      LinearMap.finrank_le_finrank_of_injective (fixedCoordinate_injective T q χ hq hdiag)
    _ = Fintype.card (FixedIndex χ) := Module.finrank_fintype_fun_eq_card k

/-- If no coordinate has weight one, the fixed subspace is zero. -/
theorem fixedSpace_eq_bot_of_no_weight_one (hq : Function.Injective q)
    (hdiag : ∀ v : V, ∀ i : ι, q (T v) i = χ i * q v i)
    (hχ : ∀ i : ι, χ i ≠ 1) : (T - LinearMap.id).ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  apply hq
  ext i
  simpa using coordinate_eq_zero_of_ne_one T q χ hdiag ⟨v, hv⟩ i (hχ i)

end Kourovka2135.DiagonalFixedCoordinates

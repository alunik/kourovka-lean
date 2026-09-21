/-
Selected elementary matrix/Frobenius proofs adapted from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Sources: BenderSuzuki/External/Huppert/XI/lemma_3_1.lean:897–943,1068–1095
and theorem_3_3.lean:30–56. See Vendor/CFSG/LICENSE.
The concrete matrix definitions retain their existing vendor provenance.
-/
import Kourovka2135.Vendor.CFSG.MatrixGroups.Suzuki
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The actual natural four-dimensional Suzuki representation and the
fixed-point-free action of every nonidentity split-torus element.
This does not assume or prove a classification of irreducible modules,
first-cohomology support, good-set existence, or central-cover recognition. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTorusMovingRank

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Matrix MatrixGroups

abbrev K (m : ℕ) := BinaryGaloisField (2 * m + 1)
abbrev G (m : ℕ) := SuzukiMatrixGroup m
abbrev V (m : ℕ) := Fin 4 → K m

theorem card_field (m : ℕ) : Nat.card (K m) = 2 ^ (2 * m + 1) :=
  GaloisField.card 2 (2 * m + 1) (by omega)

def tits (m : ℕ) : K m ≃+* K m := iterateFrobeniusEquiv (K m) 2 (m + 1)

theorem tits_apply (m : ℕ) (x : K m) : tits m x = x ^ (2 ^ (m + 1)) :=
  iterateFrobeniusEquiv_def (K m) 2 (m + 1) x

theorem field_pow_card (m : ℕ) (x : K m) : x ^ (2 ^ (2 * m + 1)) = x := by
  let : Fintype (K m) := Fintype.ofFinite (K m)
  rw [← card_field m, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem tits_sq (m : ℕ) (x : K m) : tits m (tits m x) = x ^ 2 := by
  calc
    _ = (x ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) := by rw [tits_apply, tits_apply]
    _ = x ^ (2 ^ (m + 1 + (m + 1))) := by rw [← pow_mul, ← pow_add]
    _ = x ^ (2 ^ ((2 * m + 1) + 1)) := by congr 2; omega
    _ = (x ^ (2 ^ (2 * m + 1))) ^ 2 := by rw [pow_succ, pow_mul]
    _ = x ^ 2 := by rw [field_pow_card]

/-- The vendor's middle coordinate is the inverse Frobenius iterate to Tits. -/
theorem tits_middle (m : ℕ) (x : K m) : tits m (x ^ (2 ^ m)) = x := by
  rw [tits_apply, ← pow_mul, ← pow_add]
  rw [show m + (m + 1) = 2 * m + 1 by omega]
  exact field_pow_card m x

/-- The twisted norm is one only at one, proved by scalar cancellation. -/
theorem twisted_norm_eq_one_iff (m : ℕ) (x : K m) (hx : x ≠ 0) :
    x * tits m x = 1 ↔ x = 1 := by
  constructor
  · intro hn
    have ht := congrArg (tits m) hn
    simp only [map_mul, map_one, tits_sq] at ht
    have htn : tits m x ≠ 0 := (map_ne_zero (tits m)).2 hx
    have hs : x ^ 2 = x := by
      apply mul_left_cancel₀ htn
      calc
        tits m x * x ^ 2 = 1 := ht
        _ = tits m x * x := by simpa [mul_comm] using hn.symm
    apply mul_left_cancel₀ hx
    simpa [pow_two] using hs
  · rintro rfl
    simp

theorem torus_one (m : ℕ) : SuzukiTorusGL m 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SuzukiTorusGL, SuzukiTorusMatrix]

theorem torus_mul (m : ℕ) (x y : (K m)ˣ) :
    SuzukiTorusGL m x * SuzukiTorusGL m y = SuzukiTorusGL m (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, mul_pow, mul_comm]

/-- An actual homomorphism into the concrete generated Suzuki group. -/
def torusHom (m : ℕ) : (K m)ˣ →* G m where
  toFun x := ⟨SuzukiTorusGL m x, Subgroup.subset_closure (Or.inr (Or.inl ⟨x, rfl⟩))⟩
  map_one' := Subtype.ext (torus_one m)
  map_mul' x y := Subtype.ext (torus_mul m x y).symm

theorem torusHom_injective (m : ℕ) : Function.Injective (torusHom m) := by
  intro x y hxy
  apply Units.ext
  let frob : K m ≃+* K m := iterateFrobeniusEquiv (K m) 2 m
  apply frob.injective
  have he := congrArg
    (fun g : G m => ((g.val : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) 1 1) hxy
  simpa [frob, iterateFrobeniusEquiv_def, iterateFrobenius_def,
    torusHom, SuzukiTorusGL, SuzukiTorusMatrix] using he

theorem orderOf_torus (m : ℕ) (x : (K m)ˣ) : orderOf (torusHom m x) = orderOf x :=
  orderOf_injective (torusHom m) (torusHom_injective m) x

/-- The actual defining representation, by the matrix entries of each element. -/
def natural (m : ℕ) : Representation (K m) (G m) (V m) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) (K m) ≃ₐ[K m] Module.End (K m) (V m)).toMonoidHom.comp
    ((Units.coeHom (Matrix (Fin 4) (Fin 4) (K m))).comp (SuzukiMatrixSubgroup m).subtype)

theorem natural_apply (m : ℕ) (g : G m) (v : V m) (i : Fin 4) :
    natural m g v i = ∑ j : Fin 4,
      ((g.val : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) i j * v j := by
  change (Matrix.toLin' _ v) i = _
  rw [Matrix.toLin'_apply]
  rfl

def torusWeights (m : ℕ) (x : (K m)ˣ) : Fin 4 → K m :=
  ![(x : K m) ^ (1 + 2 ^ m), (x : K m) ^ (2 ^ m),
    ((x : K m) ^ (2 ^ m))⁻¹, ((x : K m) ^ (1 + 2 ^ m))⁻¹]

theorem natural_torus_apply (m : ℕ) (x : (K m)ˣ) (v : V m) (i : Fin 4) :
    natural m (torusHom m x) v i = torusWeights m x i * v i := by
  rw [natural_apply]
  fin_cases i <;>
    simp [torusHom, SuzukiTorusGL, SuzukiTorusMatrix, torusWeights, Fin.sum_univ_four]

theorem middle_ne_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    (x : K m) ^ (2 ^ m) ≠ 1 := by
  intro he
  apply hx
  apply Units.ext
  apply (iterateFrobeniusEquiv (K m) 2 m).injective
  simpa [iterateFrobeniusEquiv_def, iterateFrobenius_def] using he

theorem outer_ne_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    (x : K m) ^ (1 + 2 ^ m) ≠ 1 := by
  intro he
  apply middle_ne_one m x hx
  apply (twisted_norm_eq_one_iff m _ (pow_ne_zero _ x.ne_zero)).mp
  rw [tits_middle]
  simpa [pow_add, mul_comm] using he

theorem torusWeights_ne_one (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) (i : Fin 4) :
    torusWeights m x i ≠ 1 := by
  have hm := middle_ne_one m x hx
  have ho := outer_ne_one m x hx
  fin_cases i
  · simpa [torusWeights] using ho
  · simpa [torusWeights] using hm
  · simpa [torusWeights] using hm
  · simpa [torusWeights] using ho

/-- No natural fixed vector is assumed: each coordinate is killed by an
explicit nonzero diagonal difference. -/
theorem ker_natural_torus_sub_id_eq_bot (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    (natural m (torusHom m x) - LinearMap.id).ker = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have he : natural m (torusHom m x) v = v := sub_eq_zero.mp hv
  funext i
  have hi := congrFun he i
  rw [natural_torus_apply] at hi
  have hz : (torusWeights m x i - 1) * v i = 0 := by
    simpa [sub_mul] using sub_eq_zero.mpr hi
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (torusWeights_ne_one m x hx i))

theorem finrank_natural_torus_moving_eq_four (m : ℕ) (x : (K m)ˣ) (hx : x ≠ 1) :
    Module.finrank (K m) (natural m (torusHom m x) - LinearMap.id).range = 4 := by
  have h := (natural m (torusHom m x) - LinearMap.id).finrank_range_add_finrank_ker
  rw [ker_natural_torus_sub_id_eq_bot m x hx] at h
  simpa [V] using h

end Kourovka2135.SuzukiTorusMovingRank

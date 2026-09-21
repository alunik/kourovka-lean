import Kourovka2135.BinaryExteriorCharacter
import Kourovka2135.BinaryWeights
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A finite binary additive group algebra in squarefree coordinates.

The parameter field F has order `2^f` and embeds in the characteristic-two
coefficient field k. The explicit character determines the algebra map.
Its coefficient matrix is square Vandermonde after indexing subsets by their
binary sums, so it is injective; equality of dimensions gives the equivalence.
No representation classification or cohomological assertion is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryExteriorGroupAlgebra

open Kourovka2135.BinaryExteriorAlgebra
open Kourovka2135.BinaryExteriorCharacter
open scoped CharTwo IsMulCommutative

/-- The ordinary natural-number weight of a binary subset. -/
def subsetWeight (f : ℕ) (I : Finset (Fin f)) : ℕ :=
  ∑ i ∈ I, 2 ^ i.val

theorem subsetWeight_lt (f : ℕ) (I : Finset (Fin f)) :
    subsetWeight f I < 2 ^ f := by
  have h : (∑ j ∈ I.map Fin.valEmbedding, 2 ^ j) < 2 ^ f := by
    apply Nat.geomSum_lt (by decide)
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    exact i.isLt
  simpa [subsetWeight] using h

theorem subsetWeight_injective (f : ℕ) : Function.Injective (subsetWeight f) := by
  intro I J h
  apply Finset.map_injective Fin.valEmbedding
  apply Finset.geomSum_injective (n := 2) (by decide)
  simpa [subsetWeight] using h

/-- A binary subset, viewed as a bounded exponent. -/
def subsetExponent (f : ℕ) (I : Finset (Fin f)) : Fin (2 ^ f) :=
  ⟨subsetWeight f I, subsetWeight_lt f I⟩

theorem subsetExponent_bijective (f : ℕ) : Function.Bijective (subsetExponent f) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro I J h
    exact subsetWeight_injective f (congrArg Fin.val h)
  · simp

/-- All exponents from zero through `2^f−1` occur exactly once. -/
def subsetExponentEquiv (f : ℕ) : Finset (Fin f) ≃ Fin (2 ^ f) :=
  Equiv.ofBijective (subsetExponent f) (subsetExponent_bijective f)

@[simp] theorem subsetExponentEquiv_apply_val (f : ℕ) (I : Finset (Fin f)) :
    (subsetExponentEquiv f I).val = subsetWeight f I := rfl

@[simp] theorem subsetWeight_equiv_symm (f : ℕ) (n : Fin (2 ^ f)) :
    subsetWeight f ((subsetExponentEquiv f).symm n) = n.val :=
  congrArg Fin.val ((subsetExponentEquiv f).apply_symm_apply n)

variable (k : Type*) [Field k] [CharP k 2] (f : ℕ)
variable {F : Type*} [Field F] (σ : F →+* k)

/-- Restrict the unipotent parameter to the embedded field F. -/
def parameterHom : Multiplicative F →* Carrier k f :=
  (characterHom k f).comp σ.toAddMonoidHom.toMultiplicative

@[simp] theorem parameterHom_apply (t : Multiplicative F) :
    parameterHom k f σ t = character k f (σ t.toAdd) := rfl

/-- The actual algebra homomorphism determined by the product character. -/
def algebraHom : AddMonoidAlgebra k F →ₐ[k] Carrier k f :=
  AddMonoidAlgebra.lift k (Carrier k f) F (parameterHom k f σ)

@[simp] theorem algebraHom_single (t : F) (a : k) :
    algebraHom k f σ (AddMonoidAlgebra.single t a) =
      a • character k f (σ t) := by
  simp [algebraHom]

variable [Fintype F]

/-- The coefficient map is the transpose Vandermonde moment map. -/
theorem algebraHom_coeff (z : AddMonoidAlgebra k F) (I : Finset (Fin f)) :
    (basis k f).repr (algebraHom k f σ z) I =
      ∑ t : F, z.coeff t * (σ t) ^ subsetWeight f I := by
  rw [algebraHom, AddMonoidAlgebra.lift_apply]
  change (basis k f).repr
    (z.coeff.sum (fun t a => a • character k f (σ t))) I = _
  rw [z.coeff.sum_fintype (fun t a => a • character k f (σ t))
    (fun _ => zero_smul k _)]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    character_coeff, smul_eq_mul, subsetWeight]

/-- Distinct field parameters give an invertible square Vandermonde matrix. -/
theorem algebraHom_injective (hcard : Fintype.card F = 2 ^ f) :
    Function.Injective (algebraHom k f σ) := by
  change Function.Injective (algebraHom k f σ).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  have hz' : algebraHom k f σ z = 0 := hz
  have hm (I : Finset (Fin f)) :
      (∑ t : F, z.coeff t * (σ t) ^ subsetWeight f I) = 0 := by
    rw [← algebraHom_coeff k f σ z I, hz']
    simp
  let e : Fin (2 ^ f) ≃ F := (Fintype.equivFinOfCardEq hcard).symm
  let v : Fin (2 ^ f) → k := fun j => z.coeff (e j)
  have hv : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun j : Fin (2 ^ f) => σ (e j)) (v := v)
      (σ.injective.comp e.injective)
    intro n
    calc
      (∑ j : Fin (2 ^ f), v j * (σ (e j)) ^ n.val) =
          ∑ t : F, z.coeff t * (σ t) ^ n.val :=
        e.sum_comp (fun t : F => z.coeff t * (σ t) ^ n.val)
      _ = 0 := by
        simpa only [subsetWeight_equiv_symm] using
          hm ((subsetExponentEquiv f).symm n)
  apply AddMonoidAlgebra.coeff_injective
  ext t
  have ht := congrFun hv (e.symm t)
  simpa [v] using ht

theorem algebraHom_bijective (hcard : Fintype.card F = 2 ^ f) :
    Function.Bijective (algebraHom k f σ) := by
  let : FiniteDimensional k (AddMonoidAlgebra k F) :=
    (AddMonoidAlgebra.basis F k).finiteDimensional_of_finite
  let : FiniteDimensional k (Carrier k f) :=
    (basis k f).finiteDimensional_of_finite
  have hdim : Module.finrank k (AddMonoidAlgebra k F) =
      Module.finrank k (Carrier k f) := by
    rw [Module.finrank_eq_card_basis (AddMonoidAlgebra.basis F k),
      Module.finrank_eq_card_basis (basis k f)]
    simpa only [Fintype.card_finset, Fintype.card_fin] using hcard
  have hinj := algebraHom_injective k f σ hcard
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (algebraHom k f σ).toLinearMap) hdim).mp hinj⟩

/-- The group algebra of the finite additive parameter field, in squarefree
coordinates over any characteristic-two coefficient field containing it. -/
def equivalence (hcard : Fintype.card F = 2 ^ f) :
    AddMonoidAlgebra k F ≃ₐ[k] Carrier k f :=
  AlgEquiv.ofBijective (algebraHom k f σ) (algebraHom_bijective k f σ hcard)

@[simp] theorem equivalence_single (hcard : Fintype.card F = 2 ^ f) (t : F) (a : k) :
    equivalence k f σ hcard (AddMonoidAlgebra.single t a) =
      a • character k f (σ t) :=
  algebraHom_single k f σ t a

@[simp] theorem equivalence_coeff (hcard : Fintype.card F = 2 ^ f)
    (z : AddMonoidAlgebra k F) (I : Finset (Fin f)) :
    (basis k f).repr (equivalence k f σ hcard z) I =
      ∑ t : F, z.coeff t * (σ t) ^ subsetWeight f I :=
  algebraHom_coeff k f σ z I

/-- The same-field specialization for a finite field of order `2^f`. -/
def selfEquivalence [Fintype k] (hcard : Fintype.card k = 2 ^ f) :
    AddMonoidAlgebra k k ≃ₐ[k] Carrier k f :=
  equivalence k f (RingHom.id k) hcard

end Kourovka2135.BinaryExteriorGroupAlgebra

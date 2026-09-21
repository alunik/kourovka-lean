import Kourovka2135.SuzukiTensorFactors
import Kourovka2135.SuzukiPrincipalSeriesDimension

/-! Actual tensor principal-series maps from the last-coordinate functional.
On pure tensors the functional is the product of their fourth coordinates.
The actual root matrices fix it, and the torus acts on it by the inverse
highest weight. No tensor self-duality or model-identification premise is
needed. Reduction of the exponent uses the proved finite-field period. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiTensorPrincipalSeriesMap

open SuzukiTorusMovingRank SuzukiTensorNatural
open SuzukiGeometry (borel root q)
open SuzukiNaturalBorelFiltration SuzukiPrincipalSeriesBorel
open BenderSuzuki.MatrixGroups
open scoped Matrix MatrixGroups PiTensorProduct

variable (k : Type) [Field k] [CharP k 2] (m : ℕ)
variable (σ : K m →+* k) (I : Finset (Fin (2 * m + 1)))

def highestWeight : ℕ := (1 + 2 ^ m) * ∑ i : I, 2 ^ i.val.val

def functional : Module.Dual k (TensorSpace k m I) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra k I k).compLinearMap
    (fun _ : I => LinearMap.proj (3 : Fin 4)))

omit [CharP k 2] in
@[simp] theorem functional_tprod (v : I → Fin 4 → k) :
    functional k m I (PiTensorProduct.tprod k v) = ∏ i : I, v i 3 := by
  simp only [functional, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]

omit [CharP k 2] in
@[simp] theorem functional_lowest : functional k m I (lowest k m I) = 1 := by
  rw [lowest_eq_tprod, functional_tprod]
  simp only [Pi.basisFun_apply, Pi.single_eq_same, Finset.prod_const_one]

omit [CharP k 2] in
theorem functional_ne_zero : functional k m I ≠ 0 := by
  intro he
  have hv := LinearMap.congr_fun he (lowest k m I)
  rw [functional_lowest] at hv
  exact one_ne_zero hv

theorem naturalTwist_root_last (i : ℕ) (a b : K m) (v : Fin 4 → k) :
    naturalTwist k m σ i (rootElement m a b) v 3 = v 3 := by
  simp [naturalTwist_apply, matrixHom, rootElement, SuzukiRootGL,
    SuzukiRootMatrix, Fin.sum_univ_four]

theorem naturalTwist_torus_last (i : ℕ) (a : (K m)ˣ) (v : Fin 4 → k) :
    naturalTwist k m σ i (torusHom m a) v 3 =
      (σ ((a⁻¹ : (K m)ˣ) : K m) ^ (1 + 2 ^ m)) ^ (2 ^ i) * v 3 := by
  simp [naturalTwist_apply, matrixHom, torusHom, SuzukiTorusGL,
    SuzukiTorusMatrix, Fin.sum_univ_four, map_inv₀, map_pow, inv_pow]

theorem functional_root (a b : K m) (v : TensorSpace k m I) :
    functional k m I (SuzukiTensorNatural.representation k m I σ (rootElement m a b) v) =
      functional k m I v := by
  have he : (functional k m I).comp
      (SuzukiTensorNatural.representation k m I σ (rootElement m a b)) = functional k m I := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change functional k m I
      (SuzukiTensorNatural.representation k m I σ (rootElement m a b)
        (PiTensorProduct.tprod k x)) = functional k m I (PiTensorProduct.tprod k x)
    simp only [representation_tprod, functional_tprod,
      naturalTwist_root_last]
  exact LinearMap.congr_fun he v

theorem functional_torus (a : (K m)ˣ) (v : TensorSpace k m I) :
    functional k m I (SuzukiTensorNatural.representation k m I σ (torusHom m a) v) =
      σ ((a⁻¹ : (K m)ˣ) : K m) ^ highestWeight m I * functional k m I v := by
  have he : (functional k m I).comp
      (SuzukiTensorNatural.representation k m I σ (torusHom m a)) =
      σ ((a⁻¹ : (K m)ˣ) : K m) ^ highestWeight m I • functional k m I := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change functional k m I
      (SuzukiTensorNatural.representation k m I σ (torusHom m a) (PiTensorProduct.tprod k x)) =
      σ ((a⁻¹ : (K m)ˣ) : K m) ^ highestWeight m I *
        functional k m I (PiTensorProduct.tprod k x)
    simp only [representation_tprod, functional_tprod, naturalTwist_torus_last,
      Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
    rfl
  exact LinearMap.congr_fun he v

theorem functional_borel (b : borel m) (v : TensorSpace k m I) :
    functional k m I (SuzukiTensorNatural.representation k m I σ (b : G m) v) =
      (character m σ (highestWeight m I) b : k) * functional k m I v := by
  obtain ⟨a, c, u, hu⟩ := exists_root_torus m b
  let r : root m :=
    ⟨rootElement m a c, Subgroup.subset_closure ⟨a, c, rfl⟩⟩
  have hb : b = rootInBorel m r * torusInBorel m u := by
    apply Subtype.ext
    apply Subtype.ext
    exact hu
  rw [hb]
  change functional k m I
    (SuzukiTensorNatural.representation k m I σ (rootElement m a c * torusHom m u) v) = _
  rw [map_mul, Module.End.mul_apply, functional_root, functional_torus]
  simp only [map_mul, character_root, one_mul, character_torus]

omit [CharP k 2] in
/-- Equal reduced exponents give the same actual Borel character. -/
theorem character_eq_of_modEq (a b : ℕ) (hab : Nat.ModEq (Nat.card (K m) - 1) a b) :
    character m σ a = character m σ b := by
  apply MonoidHom.ext
  intro g
  let u := (parameter m g)⁻¹
  have hu : u ^ (Nat.card (K m) - 1) = 1 := by
    rw [← Nat.card_units]
    exact pow_card_eq_one'
  have he := pow_eq_pow_of_modEq hab hu
  have hem := congrArg (Units.map σ.toMonoidHom) he
  simpa only [character, MonoidHom.comp_apply, powMonoidHom_apply, invMonoidHom_apply,
    map_inv, map_pow, inv_pow, u] using hem

variable (n : ℕ) (hweight : Nat.ModEq (Nat.card (K m) - 1) (highestWeight m I) n)

include hweight in
theorem functional_borel_reduced (b : borel m) (v : TensorSpace k m I) :
    functional k m I (SuzukiTensorNatural.representation k m I σ (b : G m) v) =
      (character m σ n b : k) * functional k m I v := by
  rw [functional_borel, character_eq_of_modEq k m σ _ _ hweight]

/-- The actual tensor-to-principal-series intertwiner. -/
def embedding : (SuzukiTensorNatural.representation k m I σ).IntertwiningMap
    (SuzukiPrincipalSeries.representation m σ n) :=
  SuzukiPrincipalSeries.embedding m σ n (SuzukiTensorNatural.representation k m I σ)
    (functional k m I) (functional_borel_reduced k m σ I n hweight)

theorem embedding_ne_zero : embedding k m σ I n hweight ≠ 0 :=
  SuzukiPrincipalSeries.embedding_ne_zero m σ n _ _ _ (functional_ne_zero k m I)

theorem embedding_injective : Function.Injective (embedding k m σ I n hweight) := by
  let : (SuzukiTensorNatural.representation k m I σ).IsIrreducible :=
    SuzukiTensorFactors.isIrreducible k m I σ
  exact (Representation.IsIrreducible.injective_or_eq_zero
    (embedding k m σ I n hweight)).resolve_right (embedding_ne_zero k m σ I n hweight)

omit [CharP k 2] in
theorem tensor_finrank_le : Module.finrank k (TensorSpace k m I) ≤ (q m) ^ 2 := by
  rw [finrank_tensor]
  have hc : I.card ≤ 2 * m + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ I
  calc
    4 ^ I.card ≤ 4 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) hc
    _ = (q m) ^ 2 := by
      change (2 ^ 2) ^ (2 * m + 1) = (2 ^ (2 * m + 1)) ^ 2
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (2 * m + 1)]

theorem embedding_range_ne_top : (embedding k m σ I n hweight).range ≠ ⊤ :=
  SuzukiPrincipalSeriesDimension.range_ne_top_of_finrank_le m σ n
    (embedding k m σ I n hweight) (tensor_finrank_le k m I)

end Kourovka2135.SuzukiTensorPrincipalSeriesMap

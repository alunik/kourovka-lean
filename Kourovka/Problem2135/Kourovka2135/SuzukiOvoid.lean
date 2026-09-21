/-
Selected proofs adapted from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Sources: BenderSuzuki/External/Huppert/XI/lemma_3_1.lean and theorem_3_3.lean.
See Vendor/CFSG/LICENSE and verification/suzuki-geometry/provenance.json.
This selective port retains the actual concrete SuzukiMatrixGroup; no
classification, recognition, simplicity, or cohomology premise is imported.
-/
import Kourovka2135.SuzukiRootCoordinates
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiGeometry

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Matrix MatrixGroups LinearAlgebra.Projectivization Pointwise

-- Selected from theorem_3_3.lean:30.
theorem binaryGaloisField_tits_formula_sq
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    ∀ x, pi (pi x) = x ^ 2 := by
  let K := BinaryGaloisField (2 * m + 1)
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  intro x
  let fintype : Fintype K := Fintype.ofFinite K
  calc
    pi (pi x) = (pi x) ^ (2 ^ (m + 1)) := hpi (pi x)
    _ = (x ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) := by rw [hpi]
    _ = x ^ (2 ^ (m + 1 + (m + 1))) := by rw [← pow_mul, ← pow_add]
    _ = x ^ (2 ^ ((2 * m + 1) + 1)) := by
      congr 2
      omega
    _ = (x ^ (2 ^ (2 * m + 1))) ^ 2 := by rw [pow_succ, pow_mul]
    _ = x ^ 2 := by
      have hx_card : x ^ Nat.card K = x := by
        have hpow : x ^ (@Fintype.card K fintype) = x :=
          @FiniteField.pow_card K (inferInstance : GroupWithZero K) fintype x
        simpa only [@Fintype.card_eq_nat_card K fintype] using hpow
      rw [← hK_card, hx_card]

-- Selected from theorem_3_3.lean:58.
theorem suzukiOvoidPoint_injective
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    Function.Injective (fun z : K × K =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  change Function.Injective p
  intro z w hzw
  dsimp only [p] at hzw
  rw [Projectivization.mk_eq_mk_iff] at hzw
  rcases hzw with ⟨c, hc⟩
  have hc_one : (c : K) = 1 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simpa [Units.smul_def] using hc3
  apply Prod.ext
  · have hc2 := congrFun hc (2 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc2.symm
  · have hc1 := congrFun hc (1 : Fin 4)
    simpa [Units.smul_def, hc_one] using hc1.symm

-- Selected from theorem_3_3.lean:87.
theorem suzukiOvoidInfinity_not_mem_range
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K × K → ℙ K (Fin 4 → K) := fun z =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)
    pinf ∉ Set.range p := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  change pinf ∉ Set.range p
  intro hpinf
  rcases hpinf with ⟨z, hz⟩
  dsimp only [pinf, p] at hz
  rw [Projectivization.mk_eq_mk_iff] at hz
  rcases hz with ⟨c, hc⟩
  have hc_zero : (c : K) = 0 := by
    have hc3 := congrFun hc (3 : Fin 4)
    simp at hc3
  exact c.ne_zero hc_zero

-- Selected from theorem_3_3.lean:118.
theorem suzukiOvoid_card
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K × K → ℙ K (Fin 4 → K) := fun z =>
      Projectivization.mk K
        ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
        (by simp)
    let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range p
    Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K × K → ℙ K (Fin 4 → K) := fun z =>
    Projectivization.mk K
      ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
      (by simp)
  let O : Set (ℙ K (Fin 4 → K)) := {pinf} ∪ Set.range p
  change Nat.card {z // z ∈ O} = (2 ^ (2 * m + 1)) ^ 2 + 1
  have hp_inj : Function.Injective p :=
    suzukiOvoidPoint_injective m pi
  have hpinf : pinf ∉ Set.range p :=
    suzukiOvoidInfinity_not_mem_range m pi
  let toO : Option (K × K) → {z // z ∈ O}
    | none => ⟨pinf, Or.inl (Set.mem_singleton pinf)⟩
    | some z => ⟨p z, Or.inr ⟨z, rfl⟩⟩
  have htoO_inj : Function.Injective toO := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        exfalso
        exact hpinf ⟨v, (congrArg Subtype.val huv).symm⟩
    | some u =>
      cases v with
      | none =>
        exfalso
        exact hpinf ⟨u, congrArg Subtype.val huv⟩
      | some v =>
        exact congrArg Option.some (hp_inj (congrArg Subtype.val huv))
  have htoO_surj : Function.Surjective toO := by
    intro z
    rcases z with ⟨z, hz⟩
    change z ∈ {pinf} ∪ Set.range p at hz
    rcases hz with hz | ⟨w, hw⟩
    · have hz_eq : z = pinf := by simpa using hz
      subst z
      exact ⟨none, rfl⟩
    · subst z
      exact ⟨some w, rfl⟩
  let e : Option (K × K) ≃ {z // z ∈ O} :=
    Equiv.ofBijective toO ⟨htoO_inj, htoO_surj⟩
  have hK_card : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  calc
    Nat.card {z // z ∈ O} = Nat.card (Option (K × K)) :=
      Nat.card_congr e.symm
    _ = Nat.card (K × K) + 1 := Finite.card_option
    _ = Nat.card K * Nat.card K + 1 := by rw [Nat.card_prod]
    _ = (2 ^ (2 * m + 1)) ^ 2 + 1 := by rw [hK_card, pow_two]

-- Selected from theorem_3_3.lean:187.
theorem tits_add_eq_one_impossible
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    ¬ ∃ z : BinaryGaloisField (2 * m + 1), pi z + z = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  let toAlg : (K ≃+* K) → (K ≃ₐ[ZMod 2] K) := fun e =>
    AlgEquiv.ofRingEquiv (f := e) (fun x => by
      have hcomp : e.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  have hfinrank : Module.finrank (ZMod 2) K = 2 * m + 1 := by
    simpa [K, BinaryGaloisField] using
      GaloisField.finrank 2 (show 2 * m + 1 ≠ 0 by omega)
  have hcast : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    exact Or.inl (CharP.cast_eq_zero (ZMod 2) 2)
  rintro ⟨z, hz⟩
  have htrace_pi :
      Algebra.trace (ZMod 2) K (pi z) = Algebra.trace (ZMod 2) K z := by
    exact Algebra.trace_eq_of_algEquiv (toAlg pi) z
  have htrace_one :
      Algebra.trace (ZMod 2) K (1 : K) =
        (Module.finrank (ZMod 2) K : ZMod 2) := by
    simpa using
      (Algebra.trace_algebraMap (R := ZMod 2) (S := K) (1 : ZMod 2))
  have htrace := congrArg (Algebra.trace (ZMod 2) K) hz
  rw [map_add, htrace_pi, htrace_one, hfinrank] at htrace
  rw [CharTwo.add_self_eq_zero, hcast] at htrace
  exact zero_ne_one htrace

-- Selected from theorem_3_3.lean:219.
theorem suzukiOvoidNorm_eq_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    x * y + pi x * x ^ 2 + pi y = 0 ↔ x = 0 ∧ y = 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  constructor
  · intro hnorm
    by_cases hx : x = 0
    · subst x
      simp only [zero_mul, map_zero, zero_mul, zero_add] at hnorm
      exact ⟨rfl, pi.injective (by simpa using hnorm)⟩
    · exfalso
      have hpix : pi x ≠ 0 := (map_ne_zero pi).2 hx
      let c : K := x * pi x
      let z : K := c⁻¹ * y
      have hc : c ≠ 0 := mul_ne_zero hx hpix
      have hy : y = c * z := by
        dsimp only [z]
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      have hpi_c : pi c = pi x * x ^ 2 := by
        dsimp only [c]
        rw [map_mul, hpi_sq]
      have hpi_y : pi y = pi c * pi z := by
        rw [hy, map_mul]
      have hfactor : x ^ 2 * pi x * (pi z + z + 1) = 0 := by
        calc
          x ^ 2 * pi x * (pi z + z + 1) =
              x * y + pi x * x ^ 2 + pi y := by
            rw [hpi_y, hy, hpi_c]
            dsimp only [c]
            ring
          _ = 0 := hnorm
      have hprefactor : x ^ 2 * pi x ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hx) hpix
      have hzsum : pi z + z + 1 = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left hprefactor
      have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
      have hz : pi z + z = 1 := by
        linear_combination hzsum - htwo
      exact tits_add_eq_one_impossible m pi ⟨z, hz⟩
  · rintro ⟨rfl, rfl⟩
    simp

-- Selected from theorem_3_3.lean:267.
theorem suzukiOvoidNorm_inv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (n⁻¹ * y) * (n⁻¹ * x) +
          pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹ := by
  let K := BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (n⁻¹ * y) * (n⁻¹ * x) +
        pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have hpi_n : pi n = pi x * pi y + x ^ 2 * (pi x) ^ 2 + y ^ 2 := by
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hcore :
      pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 = pi n * n := by
    rw [hpi_n]
    dsimp only [n]
    linear_combination
      (pi x * pi y * x * y + (pi x) ^ 2 * x ^ 3 * y) * htwo
  simp only [map_mul, map_inv₀]
  have hd : pi n * n ^ 2 ≠ 0 := mul_ne_zero hpin (pow_ne_zero _ hn)
  apply mul_left_cancel₀ hd
  calc
    (pi n * n ^ 2) *
        ((n⁻¹ * y) * (n⁻¹ * x) +
          (pi n)⁻¹ * pi y * (n⁻¹ * y) ^ 2 + (pi n)⁻¹ * pi x) =
        pi n * (x * y) + pi y * y ^ 2 + pi x * n ^ 2 := by
      field_simp [hn, hpin]
    _ = pi n * n := hcore
    _ = (pi n * n ^ 2) * n⁻¹ := by
      field_simp [hn, hpin]

-- Selected from theorem_3_3.lean:310.
theorem suzukiWeyl_smul_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv • pinf =
      p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiWeylGL m)).toLinearEquiv • pinf = p 0 0
  dsimp only [pinf, p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

-- Selected from theorem_3_3.lean:340.
theorem suzukiWeyl_smul_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv • p 0 0 =
      pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiWeylGL m)).toLinearEquiv • p 0 0 = pinf
  dsimp only [pinf, p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

-- Selected from theorem_3_3.lean:370.
theorem suzukiWeyl_smul_finite_of_norm_ne_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    let n := x * y + pi x * x ^ 2 + pi y
    n ≠ 0 →
      (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv •
        p x y = p (n⁻¹ * y) (n⁻¹ * x) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  dsimp only
  let n : K := x * y + pi x * x ^ 2 + pi y
  change n ≠ 0 →
    (Matrix.GeneralLinearGroup.toLin (SuzukiWeylGL m)).toLinearEquiv •
      p x y = p (n⁻¹ * y) (n⁻¹ * x)
  intro hn
  have hnorm_inv :
      (n⁻¹ * y) * (n⁻¹ * x) +
          pi (n⁻¹ * y) * (n⁻¹ * y) ^ 2 + pi (n⁻¹ * x) = n⁻¹ := by
    exact suzukiOvoidNorm_inv m pi hpi_sq x y hn
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨n, ?_⟩
  have hncancel (z : K) : n * (n⁻¹ * z) = z := by
    rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  funext i
  fin_cases i
  · rw [hnorm_inv]
    simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    exact mul_inv_cancel₀ hn
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, hncancel]
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, hncancel]
  · simp [SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, n]

-- Selected from theorem_3_3.lean:417.
theorem suzukiRoot_smul_infinity
    (m : ℕ)
    (a b : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiRootGL m a b)).toLinearEquiv •
        pinf = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m a b)).toLinearEquiv • pinf = pinf
  dsimp only [pinf]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

-- Selected from theorem_3_3.lean:440.
theorem suzukiRoot_smul_finite
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiRootGL m a b)).toLinearEquiv •
        p x y = p (x + a) (y + b + pi a * (x + a)) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m a b)).toLinearEquiv • p x y =
      p (x + a) (y + b + pi a * (x + a))
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  have hpow (z : K) : z ^ (2 ^ (m + 1)) = pi z :=
    (hpi_formula z).symm
  have hpow_one (z : K) : z ^ (1 + 2 ^ (m + 1)) = z * pi z := by
    rw [pow_add, hpow, pow_one]
  have hpow_two (z : K) : z ^ (2 + 2 ^ (m + 1)) = z ^ 2 * pi z := by
    rw [pow_add, hpow]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  funext i
  fin_cases i <;>
    simp [SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      hpow, hpow_one, hpow_two, map_add, map_mul, hpi_sq,
      CharTwo.add_self_eq_zero]
  linear_combination
    (x ^ 2 * pi a + 2 * x * a * pi a + x * a * pi x +
      a ^ 2 * pi a + a ^ 2 * pi x) * htwo
  ring

-- Selected from theorem_3_3.lean:482.
theorem suzukiTorus_smul_infinity
    (m : ℕ)
    (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiTorusGL m u)).toLinearEquiv •
        pinf = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiTorusGL m u)).toLinearEquiv • pinf = pinf
  dsimp only [pinf]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨(u : K) ^ (1 + 2 ^ m), ?_⟩
  funext i
  fin_cases i <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]

-- Selected from theorem_3_3.lean:505.
theorem suzukiTorus_smul_finite
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (u : (BinaryGaloisField (2 * m + 1))ˣ)
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun v w =>
      Projectivization.mk K
        ![v * w + pi v * v ^ 2 + pi w, w, v, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin (SuzukiTorusGL m u)).toLinearEquiv •
        p x y = p ((u : K) * x) ((u : K) * pi (u : K) * y) := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun v w =>
    Projectivization.mk K
      ![v * w + pi v * v ^ 2 + pi w, w, v, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiTorusGL m u)).toLinearEquiv • p x y =
      p ((u : K) * x) ((u : K) * pi (u : K) * y)
  dsimp only [p]
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨((u : K) ^ (1 + 2 ^ m))⁻¹, ?_⟩
  have hu : (u : K) ≠ 0 := u.ne_zero
  let s : K := (u : K) ^ (2 ^ m)
  have hs : (u : K) ^ (2 ^ m) = s := rfl
  have hs_ne : s ≠ 0 := by
    rw [← hs]
    exact pow_ne_zero _ hu
  have huouter : (u : K) ^ (1 + 2 ^ m) ≠ 0 := pow_ne_zero _ hu
  have hpi_u : pi (u : K) = s ^ 2 := by
    calc
      pi (u : K) = ((u : K) ^ (2 ^ m)) ^ 2 := by
        rw [hpi_formula, pow_succ, pow_mul]
      _ = s ^ 2 := by rw [hs]
  have huouter_formula :
      (u : K) ^ (1 + 2 ^ m) = (u : K) * s := by
    rw [pow_add, pow_one, hs]
  funext i
  fin_cases i <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      map_mul, hpi_sq]
  · rw [hpi_u, huouter_formula]
    have hus_ne : (u : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    have hinner :
        (u : K) * x * ((u : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((u : K) * x) ^ 2 +
            s ^ 2 * (u : K) ^ 2 * pi y =
          ((u : K) * s) ^ 2 * (x * y + pi x * x ^ 2 + pi y) := by
      ring
    calc
      ((u : K) * s)⁻¹ *
          ((u : K) * x * ((u : K) * s ^ 2 * y) +
            s ^ 2 * pi x * ((u : K) * x) ^ 2 +
            s ^ 2 * (u : K) ^ 2 * pi y) =
          ((u : K) * s)⁻¹ * (((u : K) * s) ^ 2 *
            (x * y + pi x * x ^ 2 + pi y)) := by rw [hinner]
      _ = ((u : K) * s) * (x * y + pi x * x ^ 2 + pi y) := by
        rw [pow_two, mul_assoc]
        exact inv_mul_cancel_left₀ hus_ne _
  · rw [hpi_u, huouter_formula, hs]
    have hus_ne : (u : K) * s ≠ 0 := mul_ne_zero hu hs_ne
    rw [show (u : K) * s ^ 2 * y =
      ((u : K) * s) * (s * y) by ring]
    exact inv_mul_cancel_left₀ hus_ne (s * y)
  · rw [huouter_formula, hs, mul_inv_rev]
    rw [mul_assoc, inv_mul_cancel_left₀ hu]

-- Selected from theorem_3_3.lean:577.
theorem suzukiGenerator_smul_mem_ovoid
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ A : GL (Fin 4) K, A ∈ SuzukiMatrixGeneratorSet m →
      ∀ z, z ∈ O →
        (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ A : GL (Fin 4) K, A ∈ SuzukiMatrixGeneratorSet m →
    ∀ z, z ∈ O →
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
  intro A hA z hz
  change (∃ a b : K, A = SuzukiRootGL m a b) ∨
    (∃ u : Kˣ, A = SuzukiTorusGL m u) ∨ A = SuzukiWeylGL m at hA
  rcases hA with hroot | hrest
  · rcases hroot with ⟨a, b, rfl⟩
    rcases hz with hz | ⟨w, rfl⟩
    · have hz_eq : z = pinf := by simpa using hz
      subst z
      rw [suzukiRoot_smul_infinity]
      exact Or.inl rfl
    · rcases w with ⟨x, y⟩
      rw [suzukiRoot_smul_finite m pi hpi_sq hpi_formula]
      exact Or.inr ⟨(x + a, y + b + pi a * (x + a)), rfl⟩
  · rcases hrest with htorus | hweyl
    · rcases htorus with ⟨u, rfl⟩
      rcases hz with hz | ⟨w, rfl⟩
      · have hz_eq : z = pinf := by simpa using hz
        subst z
        rw [suzukiTorus_smul_infinity]
        exact Or.inl rfl
      · rcases w with ⟨x, y⟩
        rw [suzukiTorus_smul_finite m pi hpi_sq hpi_formula]
        exact Or.inr ⟨((u : K) * x, (u : K) * pi (u : K) * y), rfl⟩
    · subst A
      rcases hz with hz | ⟨w, rfl⟩
      · have hz_eq : z = pinf := by simpa using hz
        subst z
        rw [suzukiWeyl_smul_infinity m pi]
        exact Or.inr ⟨(0, 0), rfl⟩
      · rcases w with ⟨x, y⟩
        let n : K := x * y + pi x * x ^ 2 + pi y
        by_cases hn : n = 0
        · have hxy : x = 0 ∧ y = 0 :=
            (suzukiOvoidNorm_eq_zero m pi hpi_sq x y).1 hn
          rcases hxy with ⟨rfl, rfl⟩
          rw [suzukiWeyl_smul_zero m pi]
          exact Or.inl rfl
        · rw [suzukiWeyl_smul_finite_of_norm_ne_zero m pi hpi_sq x y hn]
          exact Or.inr ⟨(n⁻¹ * y, n⁻¹ * x), rfl⟩

-- Selected from theorem_3_3.lean:647.
theorem suzukiMatrixGroup_smul_mem_ovoid
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ g : SuzukiMatrixGroup m, ∀ z, z ∈ O →
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
  let S : Subgroup (GL (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  have hO_finite : O.Finite := Set.toFinite O
  have hgenerators : SuzukiMatrixGeneratorSet m ⊆ S := by
    intro A hA
    change Matrix.GeneralLinearGroup.toLin A ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O
    rw [MulAction.mem_stabilizer_set_iff_smul_set_subset hO_finite]
    apply Set.smul_set_subset_iff.2
    intro z hz
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv • z ∈ O
    exact suzukiGenerator_smul_mem_ovoid
      m pi hpi_sq hpi_formula A hA z hz
  have hclosure : SuzukiMatrixSubgroup m ≤ S := by
    rw [SuzukiMatrixSubgroup, Subgroup.closure_le]
    exact hgenerators
  intro g z hz
  have hgS := hclosure g.property
  change Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) ∈
    MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) O at hgS
  have hsubset :
      Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) K) • O ⊆ O :=
    (MulAction.mem_stabilizer_set_iff_smul_set_subset hO_finite).1 hgS
  have hz' := hsubset (Set.smul_mem_smul_set hz)
  change (Matrix.GeneralLinearGroup.toLin
    (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
  exact hz'

-- Selected from theorem_3_3.lean:709.
theorem suzukiRoot_smul_self_zero
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (x y : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
      Projectivization.mk K
        ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
    (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let p : K → K → ℙ K (Fin 4 → K) := fun u v =>
    Projectivization.mk K
      ![u * v + pi u * u ^ 2 + pi v, v, u, 1] (by simp)
  change (Matrix.GeneralLinearGroup.toLin
    (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
  rw [suzukiRoot_smul_finite m pi hpi_sq hpi_formula]
  have hx0 : x + x = 0 := CharTwo.add_self_eq_zero x
  have hy0 : y + y + pi x * (x + x) = 0 := by
    rw [hx0, CharTwo.add_self_eq_zero y]
    simp
  rw [hy0, hx0]

-- Selected from theorem_3_3.lean:737.
theorem suzukiOvoid_exists_smul_eq_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ z, z ∈ O → ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • z = pinf := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ z, z ∈ O → ∃ g : SuzukiMatrixGroup m,
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • z = pinf
  intro z hz
  rcases hz with hz | ⟨wxy, rfl⟩
  · have hz_eq : z = pinf := by simpa using hz
    subst z
    let r0 : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m 0 0, Subgroup.subset_closure (by
        exact Or.inl ⟨0, 0, rfl⟩)⟩
    refine ⟨r0, ?_⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m 0 0)).toLinearEquiv • pinf = pinf
    exact suzukiRoot_smul_infinity m 0 0
  · rcases wxy with ⟨x, y⟩
    let r : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m x y, Subgroup.subset_closure (by
        exact Or.inl ⟨x, y, rfl⟩)⟩
    let w : SuzukiMatrixGroup m :=
      ⟨SuzukiWeylGL m, Subgroup.subset_closure (by
        exact Or.inr (Or.inr rfl))⟩
    have hr :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • p x y = p 0 0 := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
      exact suzukiRoot_smul_self_zero m pi hpi_sq hpi_formula x y
    have hw :
        (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv • p 0 0 = pinf := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiWeylGL m)).toLinearEquiv • p 0 0 = pinf
      exact suzukiWeyl_smul_zero m pi
    refine ⟨w * r, ?_⟩
    calc
      (Matrix.GeneralLinearGroup.toLin
          ((w * r : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv •
          p x y =
        (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
            (r : GL (Fin 4) K)).toLinearEquiv • p x y) := by
              change (Matrix.GeneralLinearGroup.toLin
                ((w : GL (Fin 4) K) * (r : GL (Fin 4) K))).toLinearEquiv •
                  p x y = _
              rw [map_mul]
              change (Matrix.GeneralLinearGroup.toLin (w : GL (Fin 4) K) *
                  Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K)) • p x y =
                Matrix.GeneralLinearGroup.toLin (w : GL (Fin 4) K) •
                  (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) • p x y)
              exact mul_smul _ _ _
      _ = (Matrix.GeneralLinearGroup.toLin
          (w : GL (Fin 4) K)).toLinearEquiv • p 0 0 := by rw [hr]
      _ = pinf := hw

-- Selected from theorem_3_3.lean:819.
theorem suzukiOvoid_exists_pair_to_standard
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ a b, a ∈ O → b ∈ O → a ≠ b →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = pinf ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = p 0 0 := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ a b, a ∈ O → b ∈ O → a ≠ b →
    ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • a = pinf ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • b = p 0 0
  intro a b ha hb hab
  obtain ⟨ga, hga⟩ :=
    suzukiOvoid_exists_smul_eq_infinity m pi hpi_sq hpi_formula a ha
  have hgb_mem :
      (Matrix.GeneralLinearGroup.toLin
        (ga : GL (Fin 4) K)).toLinearEquiv • b ∈ O :=
    suzukiMatrixGroup_smul_mem_ovoid
      m pi hpi_sq hpi_formula ga b hb
  have hgb_ne :
      (Matrix.GeneralLinearGroup.toLin
        (ga : GL (Fin 4) K)).toLinearEquiv • b ≠ pinf := by
    intro hgb
    have hsame :
        (Matrix.GeneralLinearGroup.toLin
          (ga : GL (Fin 4) K)).toLinearEquiv • b =
        (Matrix.GeneralLinearGroup.toLin
          (ga : GL (Fin 4) K)).toLinearEquiv • a := hgb.trans hga.symm
    have hba : b = a := by
      change Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • b =
        Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • a at hsame
      exact smul_left_cancel _ hsame
    exact hab hba.symm
  rcases hgb_mem with hgb_inf | ⟨xy, hxy⟩
  · exact False.elim (hgb_ne (by simpa using hgb_inf))
  · rcases xy with ⟨x, y⟩
    let r : SuzukiMatrixGroup m :=
      ⟨SuzukiRootGL m x y, Subgroup.subset_closure (by
        exact Or.inl ⟨x, y, rfl⟩)⟩
    have hr_inf :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • pinf = pinf := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • pinf = pinf
      exact suzukiRoot_smul_infinity m x y
    have hr_zero :
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv • p x y = p 0 0 := by
      change (Matrix.GeneralLinearGroup.toLin
        (SuzukiRootGL m x y)).toLinearEquiv • p x y = p 0 0
      exact suzukiRoot_smul_self_zero m pi hpi_sq hpi_formula x y
    have hcomp (z : ℙ K (Fin 4 → K)) :
        (Matrix.GeneralLinearGroup.toLin
          ((r * ga : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin
          (r : GL (Fin 4) K)).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin
            (ga : GL (Fin 4) K)).toLinearEquiv • z) := by
      change (Matrix.GeneralLinearGroup.toLin
        ((r : GL (Fin 4) K) * (ga : GL (Fin 4) K))).toLinearEquiv • z = _
      rw [map_mul]
      change (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) *
          Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K)) • z =
        Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K) •
          (Matrix.GeneralLinearGroup.toLin (ga : GL (Fin 4) K) • z)
      exact mul_smul _ _ _
    refine ⟨r * ga, ?_, ?_⟩
    · rw [hcomp, hga, hr_inf]
    · rw [hcomp, ← hxy, hr_zero]

-- Selected from theorem_3_3.lean:913.
theorem suzukiOvoid_two_transitive
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
      a ≠ b → c ≠ d →
      ∃ g : SuzukiMatrixGroup m,
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
        (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • b = d := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  change ∀ a b c d, a ∈ O → b ∈ O → c ∈ O → d ∈ O →
    a ≠ b → c ≠ d →
    ∃ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • a = c ∧
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • b = d
  intro a b c d ha hb hc hd hab hcd
  obtain ⟨g₁, hg₁a, hg₁b⟩ :=
    suzukiOvoid_exists_pair_to_standard
      m pi hpi_sq hpi_formula a b ha hb hab
  obtain ⟨g₂, hg₂c, hg₂d⟩ :=
    suzukiOvoid_exists_pair_to_standard
      m pi hpi_sq hpi_formula c d hc hd hcd
  have hinv (z t : ℙ K (Fin 4 → K))
      (hzt : (Matrix.GeneralLinearGroup.toLin
        (g₂ : GL (Fin 4) K)).toLinearEquiv • z = t) :
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • t = z := by
    rw [← hzt]
    change (Matrix.GeneralLinearGroup.toLin
      ((g₂ : GL (Fin 4) K)⁻¹)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
          (g₂ : GL (Fin 4) K)).toLinearEquiv • z) = z
    rw [map_inv]
    change (Matrix.GeneralLinearGroup.toLin
      (g₂ : GL (Fin 4) K))⁻¹ •
        (Matrix.GeneralLinearGroup.toLin (g₂ : GL (Fin 4) K) • z) = z
    exact inv_smul_smul _ _
  have hback_c := hinv c pinf hg₂c
  have hback_d := hinv d (p 0 0) hg₂d
  have hcomp (z : ℙ K (Fin 4 → K)) :
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ * g₁ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv • z =
      (Matrix.GeneralLinearGroup.toLin
        ((g₂⁻¹ : SuzukiMatrixGroup m) : GL (Fin 4) K)).toLinearEquiv •
        ((Matrix.GeneralLinearGroup.toLin
          (g₁ : GL (Fin 4) K)).toLinearEquiv • z) := by
    change (Matrix.GeneralLinearGroup.toLin
      ((g₂ : GL (Fin 4) K)⁻¹ * (g₁ : GL (Fin 4) K))).toLinearEquiv • z = _
    rw [map_mul]
    change (Matrix.GeneralLinearGroup.toLin ((g₂ : GL (Fin 4) K)⁻¹) *
        Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin 4) K)) • z =
      Matrix.GeneralLinearGroup.toLin ((g₂ : GL (Fin 4) K)⁻¹) •
        (Matrix.GeneralLinearGroup.toLin (g₁ : GL (Fin 4) K) • z)
    exact mul_smul _ _ _
  refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
  · rw [hcomp, hg₁a, hback_c]
  · rw [hcomp, hg₁b, hback_d]

-- Selected from theorem_3_3.lean:998.
set_option maxHeartbeats 2000000 in
theorem suzukiRootClosure_regular_on_ovoid_complement
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : ℙ (BinaryGaloisField (2 * m + 1)) (Fin 4 →
      BinaryGaloisField (2 * m + 1)))
    (ha : a ∈ ({Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp)} ∪ Set.range (fun z :
        BinaryGaloisField (2 * m + 1) × BinaryGaloisField (2 * m + 1) =>
          Projectivization.mk (BinaryGaloisField (2 * m + 1))
            ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
            (by simp)) ))
    (hb : b ∈ ({Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp)} ∪ Set.range (fun z :
        BinaryGaloisField (2 * m + 1) × BinaryGaloisField (2 * m + 1) =>
          Projectivization.mk (BinaryGaloisField (2 * m + 1))
            ![z.1 * z.2 + pi z.1 * z.1 ^ 2 + pi z.2, z.2, z.1, 1]
            (by simp)) ))
    (ha_ne : a ≠ Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp))
    (hb_ne : b ≠ Projectivization.mk (BinaryGaloisField (2 * m + 1))
      ![1, 0, 0, 0] (by simp)) :
    ∃! r : Subgroup.closure
        {A | ∃ x y : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m x y},
      (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) (BinaryGaloisField (2 * m + 1)))).toLinearEquiv • a = b := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x y : K, A = SuzukiRootGL m x y}
  change ∃! r : F,
    (Matrix.GeneralLinearGroup.toLin (r : GL (Fin 4) K)).toLinearEquiv • a = b
  have hpi_sq : ∀ x : K, pi (pi x) = x ^ 2 :=
    binaryGaloisField_tits_formula_sq m pi hpi
  rcases ha with ha_inf | ⟨z, hz⟩
  · exfalso
    apply ha_ne
    simpa [pinf] using ha_inf
  rcases hb with hb_inf | ⟨w, hw⟩
  · exfalso
    apply hb_ne
    simpa [pinf] using hb_inf
  subst a
  subst b
  let aa : K := w.1 + z.1
  let bb : K := w.2 + z.2 + pi aa * w.1
  let r : F := ⟨SuzukiRootGL m aa bb,
    Subgroup.subset_closure ⟨aa, bb, rfl⟩⟩
  refine ⟨r, ?_, ?_⟩
  · change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m aa bb)).toLinearEquiv • p z.1 z.2 = p w.1 w.2
    rw [suzukiRoot_smul_finite m pi hpi_sq hpi]
    have hxa : z.1 + aa = w.1 := by
      calc
        z.1 + aa = z.1 + (w.1 + z.1) := rfl
        _ = (z.1 + z.1) + w.1 := by ac_rfl
        _ = w.1 := by rw [CharTwo.add_self_eq_zero, zero_add]
    have hya : z.2 + bb + pi aa * (z.1 + aa) = w.2 := by
      rw [hxa]
      dsimp [bb]
      calc
        z.2 + (w.2 + z.2 + pi aa * w.1) + pi aa * w.1 =
            w.2 + (z.2 + z.2) +
              (pi aa * w.1 + pi aa * w.1) := by ac_rfl
        _ = w.2 := by
          rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
          simp
    have hya' : z.2 + bb + pi aa * w.1 = w.2 := by
      simpa [hxa] using hya
    rw [hxa, hya']
  · intro s hs
    rcases (suzukiRootGL_mem_closure_iff m pi hpi_sq hpi
      (s : GL (Fin 4) K)).mp s.property with ⟨c, d, hcd⟩
    have hs' : p (z.1 + c) (z.2 + d + pi c * (z.1 + c)) =
        p w.1 w.2 := by
      change (Matrix.GeneralLinearGroup.toLin
        (s : GL (Fin 4) K)).toLinearEquiv • p z.1 z.2 = p w.1 w.2 at hs
      rw [hcd, suzukiRoot_smul_finite m pi hpi_sq hpi] at hs
      exact hs
    have hcoord : z.1 + c = w.1 ∧
        z.2 + d + pi c * (z.1 + c) = w.2 := by
      dsimp [p] at hs'
      rw [Projectivization.mk_eq_mk_iff] at hs'
      rcases hs' with ⟨u, hu⟩
      have hu3 := congrFun hu (3 : Fin 4)
      have hu_one : (u : K) = 1 := by
        simpa [Units.smul_def] using hu3
      constructor
      · have hu2 := congrFun hu (2 : Fin 4)
        simpa [Units.smul_def, hu_one] using hu2.symm
      · have hu1 := congrFun hu (1 : Fin 4)
        simpa [Units.smul_def, hu_one] using hu1.symm
    have hc : c = aa := by
      have h := hcoord.1
      have hc0 : c = w.1 + z.1 := by
        calc
          c = (z.1 + c) + z.1 := by
            symm
            calc
              (z.1 + c) + z.1 = c + (z.1 + z.1) := by ac_rfl
              _ = c := by rw [CharTwo.add_self_eq_zero, add_zero]
          _ = w.1 + z.1 := by rw [h]
      exact hc0
    have hd : d = bb := by
      rw [hc] at hcoord
      have hxa2 := hcoord.1
      rw [hxa2] at hcoord
      have h := hcoord.2
      have hd0 : d = w.2 + z.2 + pi aa * w.1 := by
        calc
          d = (z.2 + d + pi aa * w.1) + z.2 + pi aa * w.1 := by
            symm
            calc
              (z.2 + d + pi aa * w.1) + z.2 + pi aa * w.1 =
                  d + (z.2 + z.2) +
                    (pi aa * w.1 + pi aa * w.1) := by ac_rfl
              _ = d := by
                rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
                simp
          _ = w.2 + z.2 + pi aa * w.1 := by rw [h]
      exact hd0
    apply Subtype.ext
    calc
      (s : GL (Fin 4) K) = SuzukiRootGL m c d := hcd
      _ = SuzukiRootGL m aa bb := by rw [hc, hd]
      _ = (r : GL (Fin 4) K) := rfl

/-! The natural projective action on the actual finite ovoid. The action
construction is the elementary subtype construction from pinned Converse/Sz,
with preservation proved above rather than assumed through a package. -/

abbrev ProjectiveSpace (m : ℕ) := ℙ (K m) (Fin 4 → K m)

def infinity (m : ℕ) : ProjectiveSpace m :=
  Projectivization.mk (K m) ![1, 0, 0, 0] (by simp)

def finitePoint (m : ℕ) (z : K m × K m) : ProjectiveSpace m :=
  Projectivization.mk (K m)
    ![z.1 * z.2 + tits m z.1 * z.1 ^ 2 + tits m z.2, z.2, z.1, 1] (by simp)

def ovoidSet (m : ℕ) : Set (ProjectiveSpace m) := {infinity m} ∪ Set.range (finitePoint m)

abbrev Ovoid (m : ℕ) := {z : ProjectiveSpace m // z ∈ ovoidSet m}

def linearAction (m : ℕ) : G m →* LinearMap.GeneralLinearGroup (K m) (Fin 4 → K m) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (SuzukiMatrixSubgroup m).subtype

instance projectiveAction (m : ℕ) : MulAction (G m) (ProjectiveSpace m) :=
  MulAction.compHom _ (linearAction m)

theorem projective_smul (m : ℕ) (g : G m) (z : ProjectiveSpace m) :
    g • z = (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) (K m))).toLinearEquiv • z := rfl

theorem ovoidSet_smul_mem (m : ℕ) (g : G m) (z : ProjectiveSpace m)
    (hz : z ∈ ovoidSet m) : g • z ∈ ovoidSet m :=
  suzukiMatrixGroup_smul_mem_ovoid m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m) g z hz

instance ovoidAction (m : ℕ) : MulAction (G m) (Ovoid m) where
  smul g z := ⟨g • z.val, ovoidSet_smul_mem m g z.val z.property⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)

@[simp] theorem ovoid_smul_coe (m : ℕ) (g : G m) (z : Ovoid m) :
    ((g • z : Ovoid m) : ProjectiveSpace m) = g • (z : ProjectiveSpace m) := rfl

def infinityOvoid (m : ℕ) : Ovoid m := ⟨infinity m, Or.inl rfl⟩

def finiteOvoid (m : ℕ) (z : K m × K m) : Ovoid m :=
  ⟨finitePoint m z, Or.inr ⟨z, rfl⟩⟩

theorem finitePoint_injective (m : ℕ) : Function.Injective (finitePoint m) :=
  suzukiOvoidPoint_injective m (tits m)

theorem infinity_not_mem_finitePoint_range (m : ℕ) :
    infinity m ∉ Set.range (finitePoint m) :=
  suzukiOvoidInfinity_not_mem_range m (tits m)

theorem card_ovoid (m : ℕ) : Nat.card (Ovoid m) = (q m) ^ 2 + 1 :=
  suzukiOvoid_card m (tits m)

instance ovoid_two_pretransitive (m : ℕ) :
    MulAction.IsMultiplyPretransitive (G m) (Ovoid m) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hcd' : c.val ≠ d.val := fun h => hcd (Subtype.ext h)
  obtain ⟨g, hga, hgb⟩ := suzukiOvoid_two_transitive m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    a.val b.val c.val d.val a.property b.property c.property d.property hab' hcd'
  exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩

theorem root_fixes_infinity (m : ℕ) (r : root m) :
    (r : G m) • infinityOvoid m = infinityOvoid m := by
  apply Subtype.ext
  change (Matrix.GeneralLinearGroup.toLin
    ((rootEquiv m r : rootGL m) : GL (Fin 4) (K m))).toLinearEquiv • infinity m = infinity m
  obtain ⟨a, b, hab⟩ := (suzukiRootGL_mem_closure_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    ((rootEquiv m r : rootGL m) : GL (Fin 4) (K m))).mp (rootEquiv m r).property
  rw [hab]
  exact suzukiRoot_smul_infinity m a b

/-- The actual root subgroup acts regularly on the ovoid away from infinity. -/
theorem root_regular (m : ℕ) (a b : Ovoid m)
    (ha : a ≠ infinityOvoid m) (hb : b ≠ infinityOvoid m) :
    ∃! r : root m, (r : G m) • a = b := by
  have ha' : a.val ≠ infinity m := fun h => ha (Subtype.ext h)
  have hb' : b.val ≠ infinity m := fun h => hb (Subtype.ext h)
  obtain ⟨r, hr, hu⟩ : ∃! r : rootGL m,
      (Matrix.GeneralLinearGroup.toLin
        (r : GL (Fin 4) (K m))).toLinearEquiv • a.val = b.val :=
    suzukiRootClosure_regular_on_ovoid_complement m (tits m)
      (SuzukiTorusMovingRank.tits_apply m) a.val b.val a.property b.property ha' hb'
  refine ⟨(rootEquiv m).symm r, ?_, ?_⟩
  · apply Subtype.ext
    exact hr
  · intro s hs
    apply (rootEquiv m).injective
    rw [MulEquiv.apply_symm_apply]
    exact hu (rootEquiv m s) (congrArg Subtype.val hs)

end Kourovka2135.SuzukiGeometry

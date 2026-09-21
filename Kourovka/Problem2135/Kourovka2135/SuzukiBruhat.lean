/-
Selected proofs adapted from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Sources: BenderSuzuki/External/Huppert/XI/lemma_3_1.lean and theorem_3_3.lean.
See Vendor/CFSG/LICENSE and verification/suzuki-geometry/provenance.json.
This selective port retains the actual concrete SuzukiMatrixGroup; no
classification, recognition, simplicity, or cohomology premise is imported.
-/
import Kourovka2135.SuzukiOvoid

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiGeometry

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Matrix MatrixGroups LinearAlgebra.Projectivization Pointwise

-- Selected from theorem_3_3.lean:1837.
theorem suzukiWeylGL_mul_self (m : ℕ) :
    SuzukiWeylGL m * SuzukiWeylGL m = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply,
      Fin.sum_univ_four]

-- Selected from theorem_3_3.lean:1845.
theorem suzukiWeylGL_conj_torus
    (m : ℕ) (u : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiWeylGL m * SuzukiTorusGL m u * SuzukiWeylGL m =
      SuzukiTorusGL m u⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix, Matrix.mul_apply, Fin.sum_univ_four, inv_pow]

-- Selected from theorem_3_3.lean:1856.
theorem suzukiBruhat_torus_powers
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (n : BinaryGaloisField (2 * m + 1)) (hn : n ≠ 0) :
    let K := BinaryGaloisField (2 * m + 1)
    let uval : K := pi n * n⁻¹ ^ 2
    let u : Kˣ := Units.mk0 uval (mul_ne_zero ((map_ne_zero pi).2 hn)
      (pow_ne_zero _ (inv_ne_zero hn)))
    ((u : K) ^ (2 ^ m) = n * (pi n)⁻¹) ∧
      ((u : K) ^ (1 + 2 ^ m) = n⁻¹) := by
  let K := BinaryGaloisField (2 * m + 1)
  let uval : K := pi n * n⁻¹ ^ 2
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have huval : uval ≠ 0 :=
    mul_ne_zero hpin (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  change (uval ^ (2 ^ m) = n * (pi n)⁻¹) ∧
    (uval ^ (1 + 2 ^ m) = n⁻¹)
  have hpi_uval : pi uval = (n * (pi n)⁻¹) ^ 2 := by
    dsimp only [uval]
    simp only [map_mul, map_pow, map_inv₀, hpi_sq]
    ring
  have hq : uval ^ (2 ^ m) = n * (pi n)⁻¹ := by
    apply CharTwo.sq_injective
    calc
      (uval ^ (2 ^ m)) ^ 2 = uval ^ (2 ^ (m + 1)) := by
        rw [show 2 ^ (m + 1) = 2 ^ m * 2 by rw [pow_succ], pow_mul]
      _ = pi uval := (hpi_formula uval).symm
      _ = (n * (pi n)⁻¹) ^ 2 := hpi_uval
  refine ⟨hq, ?_⟩
  rw [pow_add, pow_one, hq]
  dsimp only [uval]
  calc
    pi n * n⁻¹ ^ 2 * (n * (pi n)⁻¹) =
        (pi n * (pi n)⁻¹) * (n⁻¹ * n) * n⁻¹ := by ring
    _ = n⁻¹ := by rw [mul_inv_cancel₀ hpin, inv_mul_cancel₀ hn]; simp

-- Selected from theorem_3_3.lean:1899.
set_option maxHeartbeats 800000 in
theorem suzukiWeyl_root_weyl_bruhat
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    let K := BinaryGaloisField (2 * m + 1)
    let n : K := a * b + pi a * a ^ 2 + pi b
    n ≠ 0 →
      ∃ c d e f : K, ∃ u : Kˣ,
        SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
          SuzukiRootGL m c d * SuzukiTorusGL m u *
            SuzukiWeylGL m * SuzukiRootGL m e f := by
  let K := BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := a * b + pi a * a ^ 2 + pi b
  change n ≠ 0 → ∃ c d e f : K, ∃ u : Kˣ,
    SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
      SuzukiRootGL m c d * SuzukiTorusGL m u *
        SuzukiWeylGL m * SuzukiRootGL m e f
  intro hn
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  let s : K := a * pi a + b
  let c : K := n⁻¹ * s
  let y0 : K := n⁻¹ * a
  let d : K := y0 + c * pi c
  let e : K := n⁻¹ * b
  let f : K := n⁻¹ * a
  let uval : K := pi n * n⁻¹ ^ 2
  have huval : uval ≠ 0 :=
    mul_ne_zero hpin (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  have hpowers := suzukiBruhat_torus_powers
    m pi hpi_sq hpi_formula n hn
  have hq : (u : K) ^ (2 ^ m) = n * (pi n)⁻¹ := hpowers.1
  have hp : (u : K) ^ (1 + 2 ^ m) = n⁻¹ := hpowers.2
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have hnorm_as : a * s + pi a * a ^ 2 + pi s = n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq]
    linear_combination (a ^ 2 * pi a) * htwo
  have hright : e * f + pi e * e ^ 2 + pi f = n⁻¹ := by
    dsimp only [e, f]
    exact suzukiOvoidNorm_inv m pi hpi_sq a b hn
  have hleft_coord : c * y0 + pi c * c ^ 2 + pi y0 = n⁻¹ := by
    have h := suzukiOvoidNorm_inv m pi hpi_sq a s
    rw [hnorm_as] at h
    exact h hn
  have hleft_s : c * pi c + d = y0 := by
    dsimp only [d]
    linear_combination (c * pi c) * htwo
  have hleft_n : c ^ 2 * pi c + c * d + pi d = n⁻¹ := by
    dsimp only [d]
    simp only [map_add, map_mul, hpi_sq]
    linear_combination hleft_coord + (c ^ 2 * pi c) * htwo
  have hleft_norm : c * d + pi c * c ^ 2 + pi d = n⁻¹ := by
    calc
      c * d + pi c * c ^ 2 + pi d =
          c ^ 2 * pi c + c * d + pi d := by ring
      _ = n⁻¹ := hleft_n
  have hc_n : c * n = s := by
    dsimp only [c]
    calc
      n⁻¹ * s * n = (n⁻¹ * n) * s := by ring
      _ = s := by rw [inv_mul_cancel₀ hn]; simp
  have hy0_n : y0 * n = a := by
    dsimp only [y0]
    calc
      n⁻¹ * a * n = (n⁻¹ * n) * a := by ring
      _ = a := by rw [inv_mul_cancel₀ hn]; simp
  have hn_e : n * e = b := by
    dsimp only [e]
    calc
      n * (n⁻¹ * b) = (n * n⁻¹) * b := by ring
      _ = b := by rw [mul_inv_cancel₀ hn]; simp
  have hn_f : n * f = a := by
    dsimp only [f]
    calc
      n * (n⁻¹ * a) = (n * n⁻¹) * a := by ring
      _ = a := by rw [mul_inv_cancel₀ hn]; simp
  have hn_explicit : a * b + a ^ 2 * pi a + pi b ≠ 0 := by
    simpa [n, mul_comm] using hn
  have hpin_explicit :
      a ^ 2 * pi a ^ 2 + pi a * pi b + b ^ 2 ≠ 0 := by
    intro hz
    apply hpin
    dsimp only [n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination hz
  have hpi_a_sq : pi (a ^ 2) = pi a ^ 2 := map_pow pi a 2
  have hpoly_d : a * pi n + s * pi s = b * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination (a * pi a * pi b + a ^ 3 * pi a ^ 2) * htwo
  have hpoly_T : b * pi b + a * pi n = s * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, map_pow, hpi_sq]
    linear_combination -(a ^ 2 * b * pi a) * htwo
  have hpoly_11 : a * b + pi s = n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq]
    ring
  have hpoly_21 : s * b + pi n = pi a * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq, hpi_a_sq]
    linear_combination (b ^ 2) * htwo
  have hpoly_22 : s * a + pi b = n := by
    dsimp only [s, n]
    ring
  have hpoly_12 : a ^ 2 * pi n + pi s * pi b + n ^ 2 = 0 := by
    dsimp only [s, n]
    simp only [map_add, map_mul, hpi_sq, hpi_a_sq]
    linear_combination
      (a ^ 2 * pi a * pi b + a ^ 4 * pi a ^ 2 +
        a ^ 2 * b ^ 2 + pi b ^ 2 + a * b * pi b +
        a ^ 2 * pi a * pi b + a ^ 3 * pi a * b) * htwo
  have hpoly_13 : a * pi n + pi s * s + n * b = 0 := by
    calc
      a * pi n + pi s * s + n * b = b * n + b * n := by
        rw [show pi s * s = s * pi s by ring, hpoly_d]
        ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have hpi_c_mul : pi c * pi n = pi s := by
    dsimp only [c]
    simp only [map_mul, map_inv₀]
    calc
      (pi n)⁻¹ * pi s * pi n = ((pi n)⁻¹ * pi n) * pi s := by ring
      _ = pi s := by rw [inv_mul_cancel₀ hpin]; simp
  have hpi_e_mul : pi e * pi n = pi b := by
    dsimp only [e]
    simp only [map_mul, map_inv₀]
    calc
      (pi n)⁻¹ * pi b * pi n = ((pi n)⁻¹ * pi n) * pi b := by ring
      _ = pi b := by rw [inv_mul_cancel₀ hpin]; simp
  have hpi_c_div : pi c = pi s * (pi n)⁻¹ := by
    calc
      pi c = pi c * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = (pi c * pi n) * (pi n)⁻¹ := by ring
      _ = pi s * (pi n)⁻¹ := by rw [hpi_c_mul]
  have hpi_e_div : pi e = pi b * (pi n)⁻¹ := by
    calc
      pi e = pi e * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = (pi e * pi n) * (pi n)⁻¹ := by ring
      _ = pi b * (pi n)⁻¹ := by rw [hpi_e_mul]
  have hd_r : d * (pi n * n⁻¹) = e := by
    have hd_mul : d * pi n * n = b * n := by
      dsimp only [d]
      calc
        (y0 + c * pi c) * pi n * n =
            (y0 * n) * pi n + (c * n) * (pi c * pi n) := by ring
        _ = a * pi n + s * pi s := by rw [hy0_n, hc_n, hpi_c_mul]
        _ = b * n := hpoly_d
    have hd_pi : d * pi n = b := by
      exact mul_right_cancel₀ hn hd_mul
    calc
      d * (pi n * n⁻¹) = (d * pi n) * n⁻¹ := by ring
      _ = b * n⁻¹ := by rw [hd_pi]
      _ = e := by dsimp only [e]; ring
  have hT : e * pi e + f = s * (pi n)⁻¹ := by
    have hT_mul : (e * pi e + f) * pi n * n = s * n := by
      calc
        (e * pi e + f) * pi n * n =
            (n * e) * (pi e * pi n) + (n * f) * pi n := by ring
        _ = b * pi b + a * pi n := by rw [hn_e, hn_f, hpi_e_mul]
        _ = s * n := hpoly_T
    have hT_pi : (e * pi e + f) * pi n = s := by
      exact mul_right_cancel₀ hn hT_mul
    calc
      e * pi e + f = (e * pi e + f) * (pi n * (pi n)⁻¹) := by
        rw [mul_inv_cancel₀ hpin, mul_one]
      _ = ((e * pi e + f) * pi n) * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ := by rw [hT_pi]
  have hc_q : c * (n * (pi n)⁻¹) = s * (pi n)⁻¹ := by
    calc
      c * (n * (pi n)⁻¹) = (c * n) * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ := by rw [hc_n]
  have h11 :
      (c * pi c + d) * n * e + pi c * (pi n * n⁻¹) = 1 := by
    rw [hleft_s]
    calc
      y0 * n * e + pi c * (pi n * n⁻¹) =
          (a * b + pi s) * n⁻¹ := by
        rw [hy0_n]
        dsimp only [e]
        rw [show pi c * (pi n * n⁻¹) = pi s * n⁻¹ by
          calc
            pi c * (pi n * n⁻¹) = (pi c * pi n) * n⁻¹ := by ring
            _ = pi s * n⁻¹ := by rw [hpi_c_mul]]
        ring
      _ = n * n⁻¹ := by rw [hpoly_11]
      _ = 1 := mul_inv_cancel₀ hn
  have h12 :
      (c * pi c + d) * n * f + pi c * (pi n * n⁻¹) * pi e +
          n * (pi n)⁻¹ = 0 := by
    rw [hleft_s, hpi_c_div, hpi_e_div]
    have hmiddle :
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
            (pi b * (pi n)⁻¹) =
          pi s * pi b * n⁻¹ * (pi n)⁻¹ := by
      calc
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (pi b * (pi n)⁻¹) =
            ((pi n)⁻¹ * pi n) *
              (pi s * pi b * n⁻¹ * (pi n)⁻¹) := by ring
        _ = pi s * pi b * n⁻¹ * (pi n)⁻¹ := by
          rw [inv_mul_cancel₀ hpin, one_mul]
    calc
      y0 * n * f +
            (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (pi b * (pi n)⁻¹) + n * (pi n)⁻¹ =
          a ^ 2 * n⁻¹ + pi s * pi b * n⁻¹ * (pi n)⁻¹ +
            n * (pi n)⁻¹ := by
        rw [hy0_n, hmiddle]
        dsimp only [f]
        ring
      _ = (a ^ 2 * pi n + pi s * pi b + n ^ 2) *
            n⁻¹ * (pi n)⁻¹ := by
        have ha_cancel :
            a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ = a ^ 2 * n⁻¹ := by
          calc
            a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ =
                (pi n * (pi n)⁻¹) * (a ^ 2 * n⁻¹) := by ring
            _ = a ^ 2 * n⁻¹ := by rw [mul_inv_cancel₀ hpin, one_mul]
        have hn_cancel :
            n ^ 2 * n⁻¹ * (pi n)⁻¹ = n * (pi n)⁻¹ := by
          calc
            n ^ 2 * n⁻¹ * (pi n)⁻¹ =
                (n * n⁻¹) * (n * (pi n)⁻¹) := by ring
            _ = n * (pi n)⁻¹ := by rw [mul_inv_cancel₀ hn, one_mul]
        symm
        calc
          (a ^ 2 * pi n + pi s * pi b + n ^ 2) *
                n⁻¹ * (pi n)⁻¹ =
              a ^ 2 * pi n * n⁻¹ * (pi n)⁻¹ +
                pi s * pi b * n⁻¹ * (pi n)⁻¹ +
                n ^ 2 * n⁻¹ * (pi n)⁻¹ := by ring
          _ = a ^ 2 * n⁻¹ + pi s * pi b * n⁻¹ * (pi n)⁻¹ +
                n * (pi n)⁻¹ := by rw [ha_cancel, hn_cancel]
      _ = 0 := by rw [hpoly_12]; simp
  have h13 :
      (c * pi c + d) * n * (e * f + pi e * e ^ 2 + pi f) +
          pi c * (pi n * n⁻¹) * (e * pi e + f) +
          n * (pi n)⁻¹ * e = 0 := by
    rw [hright, hleft_s, hT, hpi_c_div]
    have hmiddle :
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
            (s * (pi n)⁻¹) =
          pi s * s * n⁻¹ * (pi n)⁻¹ := by
      calc
        (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (s * (pi n)⁻¹) =
            ((pi n)⁻¹ * pi n) *
              (pi s * s * n⁻¹ * (pi n)⁻¹) := by ring
        _ = pi s * s * n⁻¹ * (pi n)⁻¹ := by
          rw [inv_mul_cancel₀ hpin, one_mul]
    have hne_scaled : n * (pi n)⁻¹ * e = b * (pi n)⁻¹ := by
      calc
        n * (pi n)⁻¹ * e = (n * e) * (pi n)⁻¹ := by ring
        _ = b * (pi n)⁻¹ := by rw [hn_e]
    calc
      y0 * n * n⁻¹ +
            (pi s * (pi n)⁻¹) * (pi n * n⁻¹) *
              (s * (pi n)⁻¹) + n * (pi n)⁻¹ * e =
          a * n⁻¹ + pi s * s * n⁻¹ * (pi n)⁻¹ +
            b * (pi n)⁻¹ := by
        rw [hy0_n, hmiddle, hne_scaled]
      _ = (a * pi n + pi s * s + n * b) *
            n⁻¹ * (pi n)⁻¹ := by
        field_simp [hn, hpin]
      _ = 0 := by rw [hpoly_13]; simp
  have h21 : c * n * e + pi n * n⁻¹ = pi a := by
    rw [hc_n]
    dsimp only [e]
    calc
      s * (n⁻¹ * b) + pi n * n⁻¹ = (s * b + pi n) * n⁻¹ := by ring
      _ = (pi a * n) * n⁻¹ := by rw [hpoly_21]
      _ = pi a := by rw [mul_assoc, mul_inv_cancel₀ hn, mul_one]
  have h22 : c * n * f + pi n * n⁻¹ * pi e = 1 := by
    rw [hc_n, hpi_e_div]
    dsimp only [f]
    calc
      s * (n⁻¹ * a) + pi n * n⁻¹ * (pi b * (pi n)⁻¹) =
          (s * a + pi b) * n⁻¹ := by
        have hcancel :
            pi n * n⁻¹ * (pi b * (pi n)⁻¹) = pi b * n⁻¹ := by
          calc
            pi n * n⁻¹ * (pi b * (pi n)⁻¹) =
                (pi n * (pi n)⁻¹) * (pi b * n⁻¹) := by ring
            _ = pi b * n⁻¹ := by rw [mul_inv_cancel₀ hpin, one_mul]
        rw [hcancel]
        ring
      _ = n * n⁻¹ := by
        rw [hpoly_22]
      _ = 1 := mul_inv_cancel₀ hn
  have h23 :
      c * n * (e * f + pi e * e ^ 2 + pi f) +
          pi n * n⁻¹ * (e * pi e + f) = 0 := by
    rw [hright, hT]
    calc
      c * n * n⁻¹ + pi n * n⁻¹ * (s * (pi n)⁻¹) =
          s * n⁻¹ + s * n⁻¹ := by
        rw [hc_n]
        field_simp [hn, hpin]
        ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have h01 :
      (c * d + pi c * c ^ 2 + pi d) * n * e +
          d * (pi n * n⁻¹) = 0 := by
    rw [hleft_norm, hd_r, inv_mul_cancel₀ hn, one_mul]
    exact CharTwo.add_self_eq_zero e
  have h02 :
      (c * d + pi c * c ^ 2 + pi d) * n * f +
          d * (pi n * n⁻¹) * pi e + c * (n * (pi n)⁻¹) = 0 := by
    rw [hleft_norm, hd_r, hc_q, inv_mul_cancel₀ hn, one_mul]
    calc
      f + e * pi e + s * (pi n)⁻¹ =
          (e * pi e + f) + s * (pi n)⁻¹ := by ring
      _ = s * (pi n)⁻¹ + s * (pi n)⁻¹ := by rw [hT]
      _ = 0 := CharTwo.add_self_eq_zero _
  have h03 :
      (c * d + pi c * c ^ 2 + pi d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          d * (pi n * n⁻¹) * (e * pi e + f) +
          c * (n * (pi n)⁻¹) * e + n⁻¹ = 0 := by
    rw [hleft_norm, hright, hd_r, hc_q,
      inv_mul_cancel₀ hn, one_mul, hT]
    linear_combination (n⁻¹) * htwo +
      (e * (s * (pi n)⁻¹)) * htwo
  have h00_goal :
      1 = (c * d + pi c * c ^ 2 + pi d) * n := by
    rw [hleft_norm, inv_mul_cancel₀ hn]
  have h01_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n * e +
        d * (pi n * n⁻¹) := h01.symm
  have h02_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n * f +
        d * (pi n * n⁻¹) * pi e + c * (n * (pi n)⁻¹) := h02.symm
  have h03_goal :
      0 = (c * d + pi c * c ^ 2 + pi d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          d * (pi n * n⁻¹) * (e * pi e + f) +
          c * (n * (pi n)⁻¹) * e + n⁻¹ := h03.symm
  have h10_goal : a = (c * pi c + d) * n := by
    rw [hleft_s, hy0_n]
  have h11_goal :
      1 = (c * pi c + d) * n * e + pi c * (pi n * n⁻¹) := h11.symm
  have h12_goal :
      0 = (c * pi c + d) * n * f +
        pi c * (pi n * n⁻¹) * pi e + n * (pi n)⁻¹ := h12.symm
  have h13_goal :
      0 = (c * pi c + d) * n *
            (e * f + pi e * e ^ 2 + pi f) +
          pi c * (pi n * n⁻¹) * (e * pi e + f) +
          n * (pi n)⁻¹ * e := h13.symm
  have h20_goal : a * pi a + b = c * n := by
    rw [hc_n]
  have h21_goal : pi a = c * n * e + pi n * n⁻¹ := h21.symm
  have h22_goal : 1 = c * n * f + pi n * n⁻¹ * pi e := h22.symm
  have h23_goal :
      0 = c * n * (e * f + pi e * e ^ 2 + pi f) +
        pi n * n⁻¹ * (e * pi e + f) := h23.symm
  have h30_goal : a * b + pi a * a ^ 2 + pi b = n := rfl
  have h31_goal : b = n * e := hn_e.symm
  have h32_goal : a = n * f := hn_f.symm
  have h33_goal :
      1 = n * (e * f + pi e * e ^ 2 + pi f) := by
    rw [hright, mul_inv_cancel₀ hn]
  refine ⟨c, d, e, f, u, ?_⟩
  have hroot (x y : K) :
      SuzukiRootMatrix m x y =
        !![1, x, y, x * y + pi x * x ^ 2 + pi y;
           0, 1, pi x, x * pi x + y;
           0, 0, 1, x;
           0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootMatrix, hpi_formula, pow_add]
    all_goals ring
  have htorus :
      SuzukiTorusMatrix m u =
        !![n⁻¹, 0, 0, 0;
           0, n * (pi n)⁻¹, 0, 0;
           0, 0, pi n * n⁻¹, 0;
           0, 0, 0, n] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiTorusMatrix, hq, hp]
  ext i j
  change
    (SuzukiWeylMatrix m * SuzukiRootMatrix m a b * SuzukiWeylMatrix m) i j =
      (SuzukiRootMatrix m c d * SuzukiTorusMatrix m u * SuzukiWeylMatrix m *
        SuzukiRootMatrix m e f) i j
  rw [hroot a b, hroot c d, hroot e f, htorus]
  fin_cases i <;> fin_cases j <;>
    simp (config := { zeta := false }) [SuzukiWeylMatrix,
      Matrix.mul_apply, Fin.sum_univ_four]
  all_goals assumption

-- Selected from theorem_3_3.lean:2301.
theorem suzukiTorusClosure_le_normalizer_rootClosure
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    H ≤ Subgroup.normalizer F := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  change H ≤ Subgroup.normalizer F
  intro h hh
  rcases (suzukiTorusGL_mem_closure_iff m h).mp hh with ⟨u, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    rcases (suzukiRootGL_mem_closure_iff
      m pi hpi_sq hpi_formula f).mp hf with ⟨a, b, rfl⟩
    rw [suzukiTorusGL_conj_root m pi hpi_sq hpi_formula]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩
  · intro hf
    rcases (suzukiRootGL_mem_closure_iff
      m pi hpi_sq hpi_formula
        (SuzukiTorusGL m u * f * (SuzukiTorusGL m u)⁻¹)).mp hf with
      ⟨a, b, hab⟩
    have hf_eq :
        f = SuzukiTorusGL m u⁻¹ * SuzukiRootGL m a b *
          (SuzukiTorusGL m u⁻¹)⁻¹ := by
      calc
        f = (SuzukiTorusGL m u)⁻¹ *
              (SuzukiTorusGL m u * f * (SuzukiTorusGL m u)⁻¹) *
              SuzukiTorusGL m u := by group
        _ = (SuzukiTorusGL m u)⁻¹ * SuzukiRootGL m a b *
              SuzukiTorusGL m u := by rw [hab]
        _ = SuzukiTorusGL m u⁻¹ * SuzukiRootGL m a b *
              (SuzukiTorusGL m u⁻¹)⁻¹ := by
            rw [suzukiTorusGL_inv m u, suzukiTorusGL_inv m u⁻¹]
            simp
    rw [hf_eq, suzukiTorusGL_conj_root m pi hpi_sq hpi_formula]
    exact Subgroup.subset_closure ⟨_, _, rfl⟩

-- Selected from theorem_3_3.lean:2352.
theorem natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (F H : Subgroup G)
    (hnormal : H ≤ Subgroup.normalizer F) (hdisjoint : Disjoint F H) :
    Nat.card (F ⊔ H : Subgroup G) = Nat.card F * Nat.card H := by
  let toB : F × H → ↥(F ⊔ H) := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have htoB_injective : Function.Injective toB := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have htoB_surjective : Function.Surjective toB := by
    intro b
    have hb : (b : G) ∈ (F : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F H hnormal]
      exact b.property
    rcases hb with ⟨f, hf, h, hh, hfh⟩
    refine ⟨(⟨f, hf⟩, ⟨h, hh⟩), ?_⟩
    exact Subtype.ext hfh
  calc
    Nat.card (F ⊔ H : Subgroup G) = Nat.card (F × H) :=
      Nat.card_congr
        (Equiv.ofBijective toB ⟨htoB_injective, htoB_surjective⟩).symm
    _ = Nat.card F * Nat.card H := Nat.card_prod F H

-- Selected from theorem_3_3.lean:2379.
theorem suzukiMatrixGroup_bruhat_decomposition
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    let B : Subgroup (GL (Fin 4) K) := F ⊔ H
    ∀ g : GL (Fin 4) K, g ∈ SuzukiMatrixGroup m →
      g ∈ B ∨ ∃ b f : GL (Fin 4) K,
        b ∈ B ∧ f ∈ F ∧ g = b * SuzukiWeylGL m * f := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let P : GL (Fin 4) K → Prop := fun g =>
    g ∈ B ∨ ∃ b f : GL (Fin 4) K,
      b ∈ B ∧ f ∈ F ∧ g = b * SuzukiWeylGL m * f
  change ∀ g : GL (Fin 4) K, g ∈ SuzukiMatrixGroup m → P g
  have hF_le_B : F ≤ B := le_sup_left
  have hH_le_B : H ≤ B := le_sup_right
  have hroot_mem (a b : K) : SuzukiRootGL m a b ∈ F :=
    Subgroup.subset_closure ⟨a, b, rfl⟩
  have htorus_mem (u : Kˣ) : SuzukiTorusGL m u ∈ H :=
    Subgroup.subset_closure ⟨u, rfl⟩
  have hH_normalizes_F : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hweyl_sq : SuzukiWeylGL m * SuzukiWeylGL m = 1 :=
    suzukiWeylGL_mul_self m
  have hweyl_inv : (SuzukiWeylGL m)⁻¹ = SuzukiWeylGL m := by
    symm
    exact eq_inv_of_mul_eq_one_right hweyl_sq
  have hmul_root : ∀ g : GL (Fin 4) K, P g →
      ∀ a b : K, P (g * SuzukiRootGL m a b) := by
    intro g hg a b
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inl (B.mul_mem hgB (hF_le_B (hroot_mem a b)))
    · exact Or.inr ⟨x, y * SuzukiRootGL m a b, hxB,
        F.mul_mem hyF (hroot_mem a b), by group⟩
  have hmul_torus : ∀ g : GL (Fin 4) K, P g →
      ∀ u : Kˣ, P (g * SuzukiTorusGL m u) := by
    intro g hg u
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inl (B.mul_mem hgB (hH_le_B (htorus_mem u)))
    · let y' : GL (Fin 4) K :=
        (SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u
      have hy'F : y' ∈ F :=
        (((Subgroup.mem_normalizer_iff'').mp
          (hH_normalizes_F (htorus_mem u))) y).mp hyF
      have hweyl_torus :
          SuzukiWeylGL m * SuzukiTorusGL m u =
            SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m := by
        calc
          SuzukiWeylGL m * SuzukiTorusGL m u =
              (SuzukiWeylGL m * SuzukiTorusGL m u * SuzukiWeylGL m) *
                SuzukiWeylGL m := by rw [mul_assoc, hweyl_sq, mul_one]
          _ = SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m := by
            rw [suzukiWeylGL_conj_torus]
      refine Or.inr ⟨x * SuzukiTorusGL m u⁻¹, y',
        B.mul_mem hxB (hH_le_B (htorus_mem u⁻¹)), hy'F, ?_⟩
      dsimp only [y']
      calc
        x * SuzukiWeylGL m * y * SuzukiTorusGL m u =
            x * (SuzukiWeylGL m * SuzukiTorusGL m u) *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by group
        _ = x * (SuzukiTorusGL m u⁻¹ * SuzukiWeylGL m) *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by
            rw [hweyl_torus]
        _ = (x * SuzukiTorusGL m u⁻¹) * SuzukiWeylGL m *
              ((SuzukiTorusGL m u)⁻¹ * y * SuzukiTorusGL m u) := by group
  have hmul_weyl : ∀ g : GL (Fin 4) K, P g →
      P (g * SuzukiWeylGL m) := by
    intro g hg
    rcases hg with hgB | ⟨x, y, hxB, hyF, rfl⟩
    · exact Or.inr ⟨g, 1, hgB, F.one_mem, by simp⟩
    · rcases (suzukiRootGL_mem_closure_iff
        m pi hpi_sq hpi_formula y).mp hyF with ⟨a, b, rfl⟩
      let n : K := a * b + pi a * a ^ 2 + pi b
      by_cases hn : n = 0
      · have hab : a = 0 ∧ b = 0 :=
          (suzukiOvoidNorm_eq_zero m pi hpi_sq a b).mp hn
        rcases hab with ⟨rfl, rfl⟩
        rw [suzukiRootGL_zero_zero, mul_one, mul_assoc, hweyl_sq, mul_one]
        exact Or.inl hxB
      · rcases suzukiWeyl_root_weyl_bruhat
          m pi hpi_sq hpi_formula a b hn with ⟨c, d, e, f, u, hgauss⟩
        refine Or.inr
          ⟨x * (SuzukiRootGL m c d * SuzukiTorusGL m u),
            SuzukiRootGL m e f,
            B.mul_mem hxB (B.mul_mem (hF_le_B (hroot_mem c d))
              (hH_le_B (htorus_mem u))), hroot_mem e f, ?_⟩
        calc
          x * SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
              x * (SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m) := by group
          _ = x * (SuzukiRootGL m c d * SuzukiTorusGL m u *
                SuzukiWeylGL m * SuzukiRootGL m e f) := by rw [hgauss]
          _ = x * (SuzukiRootGL m c d * SuzukiTorusGL m u) *
                SuzukiWeylGL m * SuzukiRootGL m e f := by group
  intro g hg
  exact Subgroup.closure_induction_right
    (p := fun x _ => P x)
    (Or.inl B.one_mem)
    (fun x _ A hA hx => by
      rcases hA with hroot | hrest
      · rcases hroot with ⟨a, b, rfl⟩
        exact hmul_root x hx a b
      · rcases hrest with htorus | hweyl
        · rcases htorus with ⟨u, rfl⟩
          exact hmul_torus x hx u
        · subst A
          exact hmul_weyl x hx)
    (fun x _ A hA hx => by
      rcases hA with hroot | hrest
      · rcases hroot with ⟨a, b, rfl⟩
        have hinvF : (SuzukiRootGL m a b)⁻¹ ∈ F :=
          F.inv_mem (hroot_mem a b)
        rcases (suzukiRootGL_mem_closure_iff
          m pi hpi_sq hpi_formula _).mp hinvF with ⟨c, d, hcd⟩
        rw [hcd]
        exact hmul_root x hx c d
      · rcases hrest with htorus | hweyl
        · rcases htorus with ⟨u, rfl⟩
          rw [suzukiTorusGL_inv]
          exact hmul_torus x hx u⁻¹
        · subst A
          rw [hweyl_inv]
          exact hmul_weyl x hx)
    hg

-- Selected from theorem_3_3.lean:2517.
theorem suzukiMatrixGroup_stabilizer_infinity
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let K := BinaryGaloisField (2 * m + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let F : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
    let H : Subgroup (GL (Fin 4) K) :=
      Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
    ∀ g : SuzukiMatrixGroup m,
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
        (g : GL (Fin 4) K) ∈ F ⊔ H := by
  let K := BinaryGaloisField (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  let S : Subgroup (GL (Fin 4) K) :=
    (MulAction.stabilizer
      (LinearMap.GeneralLinearGroup K (Fin 4 → K)) pinf).comap
        Matrix.GeneralLinearGroup.toLin.toMonoidHom
  change ∀ g : SuzukiMatrixGroup m,
    (Matrix.GeneralLinearGroup.toLin
      (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf ↔
      (g : GL (Fin 4) K) ∈ B
  have hF_le_S : F ≤ S := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    rintro A ⟨a, b, rfl⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiRootGL m a b)).toLinearEquiv • pinf = pinf
    exact suzukiRoot_smul_infinity m a b
  have hH_le_S : H ≤ S := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    rintro A ⟨u, rfl⟩
    change (Matrix.GeneralLinearGroup.toLin
      (SuzukiTorusGL m u)).toLinearEquiv • pinf = pinf
    exact suzukiTorus_smul_infinity m u
  have hB_le_S : B ≤ S := sup_le hF_le_S hH_le_S
  have hB_fix : ∀ b : GL (Fin 4) K, b ∈ B →
      (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • pinf = pinf := by
    intro b hb
    exact hB_le_S hb
  have hF_fix : ∀ f : GL (Fin 4) K, f ∈ F →
      (Matrix.GeneralLinearGroup.toLin f).toLinearEquiv • pinf = pinf := by
    intro f hf
    exact hB_fix f ((show F ≤ B from le_sup_left) hf)
  have hmul_smul (x y : GL (Fin 4) K) (z : ℙ K (Fin 4 → K)) :
      (Matrix.GeneralLinearGroup.toLin (x * y)).toLinearEquiv • z =
        (Matrix.GeneralLinearGroup.toLin x).toLinearEquiv •
          ((Matrix.GeneralLinearGroup.toLin y).toLinearEquiv • z) := by
    rw [map_mul]
    change ((Matrix.GeneralLinearGroup.toLin x).toLinearEquiv *
      (Matrix.GeneralLinearGroup.toLin y).toLinearEquiv) • z = _
    exact mul_smul _ _ _
  have hp_ne : p 0 0 ≠ pinf := by
    intro hp
    exact suzukiOvoidInfinity_not_mem_range m pi ⟨(0, 0), hp⟩
  intro g
  constructor
  · intro hgfix
    rcases suzukiMatrixGroup_bruhat_decomposition
      m pi hpi_sq hpi_formula (g : GL (Fin 4) K) g.property with
      hgB | ⟨b, f, hbB, hfF, hgf⟩
    · exact hgB
    · have hbfix := hB_fix b hbB
      have hffix := hF_fix f hfF
      have hbp :
          (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
            pinf := by
        calc
          (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
              (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv •
                ((Matrix.GeneralLinearGroup.toLin
                  (SuzukiWeylGL m)).toLinearEquiv • pinf) := by
                rw [suzukiWeyl_smul_infinity m pi]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m)).toLinearEquiv • pinf := by
              simp only [hmul_smul]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m)).toLinearEquiv •
                  ((Matrix.GeneralLinearGroup.toLin f).toLinearEquiv • pinf) := by
              rw [hffix]
          _ = (Matrix.GeneralLinearGroup.toLin
                (b * SuzukiWeylGL m * f)).toLinearEquiv • pinf := by
              simp only [hmul_smul]
          _ = pinf := by rw [← hgf]; exact hgfix
      have hpinf : p 0 0 = pinf := by
        have hsame :
            (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • p 0 0 =
              (Matrix.GeneralLinearGroup.toLin b).toLinearEquiv • pinf :=
          hbp.trans hbfix.symm
        change Matrix.GeneralLinearGroup.toLin b • p 0 0 =
          Matrix.GeneralLinearGroup.toLin b • pinf at hsame
        exact smul_left_cancel _ hsame
      exact False.elim (hp_ne hpinf)
  · intro hgB
    exact hB_fix (g : GL (Fin 4) K) hgB

-- Selected from theorem_3_3.lean:2885.
theorem suzukiMatrixGroup_card
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  let K := BinaryGaloisField (2 * m + 1)
  let q := 2 ^ (2 * m + 1)
  let pinf : ℙ K (Fin 4 → K) :=
    Projectivization.mk K ![1, 0, 0, 0] (by simp)
  let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
    Projectivization.mk K
      ![x * y + pi x * x ^ 2 + pi y, y, x, 1] (by simp)
  let O : Set (ℙ K (Fin 4 → K)) :=
    {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  have hK_card : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  have hF_card := suzukiRootClosure_card m pi hpi_sq hpi_formula
  obtain ⟨eH, _heH⟩ := suzukiTorusCoordinatesMulEquiv m
  have hdisjoint := suzukiRootClosure_disjoint_torusClosure m pi hpi_sq hpi_formula
  have hF_card' : Nat.card F = q ^ 2 := by
    simpa [F, q] using hF_card
  have hH_card : Nat.card H = q - 1 := by
    calc
      Nat.card H = Nat.card Kˣ := Nat.card_congr eH.symm.toEquiv
      _ = Nat.card K - 1 := Nat.card_units K
      _ = q - 1 := by rw [hK_card]
  have hnormal : H ≤ Subgroup.normalizer F :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpi_sq hpi_formula
  have hB_card : Nat.card B = q ^ 2 * (q - 1) := by
    calc
      Nat.card B = Nat.card F * Nat.card H := by
        exact natCard_sup_eq_mul_of_disjoint_of_le_normalizer
          F H hnormal hdisjoint
      _ = q ^ 2 * (q - 1) := by rw [hF_card', hH_card]
  have hF_le_G : F ≤ SuzukiMatrixGroup m := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hH_le_G : H ≤ SuzukiMatrixGroup m := by
    dsimp only [H]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hB_le_G : B ≤ SuzukiMatrixGroup m := sup_le hF_le_G hH_le_G
  let U : Subgroup (SuzukiMatrixGroup m) :=
    B.comap (SuzukiMatrixGroup m).subtype
  have hU_card : Nat.card U = q ^ 2 * (q - 1) := by
    calc
      Nat.card U = Nat.card B := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hB_le_G).toEquiv
      _ = q ^ 2 * (q - 1) := hB_card
  let rho : SuzukiMatrixGroup m →*
      LinearMap.GeneralLinearGroup K (Fin 4 → K) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (SuzukiMatrixGroup m).subtype
  let : MulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    MulAction.compHom (ℙ K (Fin 4 → K)) rho
  let Omega : SubMulAction (SuzukiMatrixGroup m) (ℙ K (Fin 4 → K)) :=
    { carrier := O
      smul_mem' := by
        intro g z hz
        change (Matrix.GeneralLinearGroup.toLin
          (g : GL (Fin 4) K)).toLinearEquiv • z ∈ O
        exact suzukiMatrixGroup_smul_mem_ovoid
          m pi hpi_sq hpi_formula g z hz }
  let pinfO : Omega := ⟨pinf, Or.inl rfl⟩
  have hU_eq_stabilizer :
      U = MulAction.stabilizer (SuzukiMatrixGroup m) pinfO := by
    ext g
    rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
    change (g : GL (Fin 4) K) ∈ B ↔
      (Matrix.GeneralLinearGroup.toLin
        (g : GL (Fin 4) K)).toLinearEquiv • pinf = pinf
    exact (suzukiMatrixGroup_stabilizer_infinity
      m pi hpi_sq hpi_formula g).symm
  have htwo :
      MulAction.IsMultiplyPretransitive (SuzukiMatrixGroup m) Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    have hab' : (a : ℙ K (Fin 4 → K)) ≠ b := by
      intro h
      exact hab (Subtype.ext h)
    have hcd' : (c : ℙ K (Fin 4 → K)) ≠ d := by
      intro h
      exact hcd (Subtype.ext h)
    rcases suzukiOvoid_two_transitive
      m pi hpi_sq hpi_formula (a : ℙ K (Fin 4 → K)) b c d
        a.property b.property c.property d.property hab' hcd' with
      ⟨g, hga, hgb⟩
    exact ⟨g, Subtype.ext hga, Subtype.ext hgb⟩
  have hOmega_card : Nat.card Omega = q ^ 2 + 1 := by
    change Nat.card {z // z ∈ O} = q ^ 2 + 1
    simpa [O, q] using suzukiOvoid_card m pi
  have hU_index : U.index = q ^ 2 + 1 := by
    have hpre : MulAction.IsPretransitive (SuzukiMatrixGroup m) Omega :=
      @MulAction.isPretransitive_of_is_two_pretransitive
        (SuzukiMatrixGroup m) Omega _ _ htwo
    rw [hU_eq_stabilizer]
    exact (@MulAction.index_stabilizer_of_transitive
      (SuzukiMatrixGroup m) Omega _ _ pinfO hpre).trans hOmega_card
  change Nat.card (SuzukiMatrixGroup m) = (q ^ 2 + 1) * q ^ 2 * (q - 1)
  calc
    Nat.card (SuzukiMatrixGroup m) = Nat.card U * U.index :=
      U.card_mul_index.symm
    _ = (q ^ 2 * (q - 1)) * (q ^ 2 + 1) := by
      rw [hU_card, hU_index]
    _ = (q ^ 2 + 1) * q ^ 2 * (q - 1) := by ring

/-! Cardinality and the actual odd-index Borel, with canonical Tits map. -/

theorem card_group (m : ℕ) :
    Nat.card (G m) = ((q m) ^ 2 + 1) * (q m) ^ 2 * (q m - 1) :=
  suzukiMatrixGroup_card m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)

theorem torusGL_le_normalizer_rootGL (m : ℕ) :
    torusGL m ≤ Subgroup.normalizer (rootGL m) :=
  suzukiTorusClosure_le_normalizer_rootClosure m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)

theorem disjoint_rootGL_torusGL (m : ℕ) : Disjoint (rootGL m) (torusGL m) :=
  suzukiRootClosure_disjoint_torusClosure m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)

theorem card_borel (m : ℕ) : Nat.card (borel m) = (q m) ^ 2 * (q m - 1) := by
  calc
    Nat.card (borel m) = Nat.card (borelGL m) := Nat.card_congr (borelEquiv m).toEquiv
    _ = Nat.card (rootGL m) * Nat.card (torusGL m) :=
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer _ _
        (torusGL_le_normalizer_rootGL m) (disjoint_rootGL_torusGL m)
    _ = Nat.card (root m) * Nat.card (torus m) := by
      rw [Nat.card_congr (rootEquiv m).symm.toEquiv,
        Nat.card_congr (torusEquiv m).symm.toEquiv]
    _ = (q m) ^ 2 * (q m - 1) := by rw [card_root, card_torus]

theorem one_lt_q (m : ℕ) : 1 < q m := by
  exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : 2 * m + 1 ≠ 0)

theorem borel_index (m : ℕ) : (borel m).index = (q m) ^ 2 + 1 := by
  have hpos : 0 < (q m) ^ 2 * (q m - 1) :=
    Nat.mul_pos (pow_pos (lt_trans Nat.zero_lt_one (one_lt_q m)) _)
      (Nat.sub_pos_of_lt (one_lt_q m))
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    ((q m) ^ 2 * (q m - 1)) * (borel m).index = Nat.card (G m) := by
      rw [← card_borel]
      exact (borel m).card_mul_index
    _ = ((q m) ^ 2 * (q m - 1)) * ((q m) ^ 2 + 1) := by rw [card_group]; ring

theorem even_q (m : ℕ) : Even (q m) := by
  refine ⟨2 ^ (2 * m), ?_⟩
  dsimp only [q]
  rw [pow_succ]
  omega

theorem odd_borel_index (m : ℕ) : Odd (borel m).index := by
  rw [borel_index]
  exact ((even_q m).pow_of_ne_zero (by decide : 2 ≠ 0)).add_one

theorem borel_eq_stabilizer_infinity (m : ℕ) :
    borel m = MulAction.stabilizer (G m) (infinityOvoid m) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, ← Subtype.coe_inj]
  change (g : GL (Fin 4) (K m)) ∈ borelGL m ↔
    (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 4) (K m))).toLinearEquiv •
      infinity m = infinity m
  exact (suzukiMatrixGroup_stabilizer_infinity m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m) g).symm

end Kourovka2135.SuzukiGeometry

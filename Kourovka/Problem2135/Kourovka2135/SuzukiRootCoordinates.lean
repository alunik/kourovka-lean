/-
Selected proofs adapted from Qiuzhen-CFSG/CFSG,
commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0.
Sources: BenderSuzuki/External/Huppert/XI/lemma_3_1.lean and theorem_3_3.lean.
See Vendor/CFSG/LICENSE and verification/suzuki-geometry/provenance.json.
This selective port retains the actual concrete SuzukiMatrixGroup; no
classification, recognition, simplicity, or cohomology premise is imported.
-/
import Kourovka2135.SuzukiTorusMovingRank
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiGeometry

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped Matrix MatrixGroups

-- Selected from lemma_3_1.lean:106.
theorem suzukiRootGL_zero_zero (m : ℕ) :
    SuzukiRootGL m 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix]

-- Selected from lemma_3_1.lean:113.
theorem suzukiRootGL_injective
    (m : ℕ) (a b a' b' : BinaryGaloisField (2 * m + 1))
    (h : SuzukiRootGL m a b = SuzukiRootGL m a' b') :
    a = a' ∧ b = b' := by
  constructor
  · have h01 := congrArg
      (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
        ((A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)))
          0 1)) h
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h01
  · have h02 := congrArg
      (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
        ((A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1)))
          0 2)) h
    simpa [SuzukiRootGL, SuzukiRootMatrix] using h02

-- Selected from lemma_3_1.lean:130.
theorem suzukiRootGL_mul
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b a' b' : BinaryGaloisField (2 * m + 1)) :
    SuzukiRootGL m a b * SuzukiRootGL m a' b' =
      SuzukiRootGL m (a + a') (b + b' + a * pi a') := by
  have hpow (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (2 ^ (m + 1)) = pi x := (hpi_formula x).symm
  have hpow_one (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (1 + 2 ^ (m + 1)) = x * pi x := by
    rw [pow_add, hpow, pow_one]
  have hpow_two (x : BinaryGaloisField (2 * m + 1)) :
      x ^ (2 + 2 ^ (m + 1)) = x ^ 2 * pi x := by
    rw [pow_add, hpow]
  have htwo : (2 : BinaryGaloisField (2 * m + 1)) = 0 :=
    CharP.cast_eq_zero _ 2
  have hthree : (3 : BinaryGaloisField (2 * m + 1)) = 1 := by
    calc
      (3 : BinaryGaloisField (2 * m + 1)) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, CharTwo.add_self_eq_zero]
  all_goals (try rw [hpow a'])
  all_goals (try rw [hpow a])
  all_goals (try rw [hpow (a + a')])
  all_goals (try rw [hpow b'])
  all_goals (try rw [hpow b])
  all_goals (try rw [hpow (b + b' + a * pi a')])
  all_goals (try rw [hpow_one a'])
  all_goals (try rw [hpow_one a])
  all_goals (try rw [hpow_one (a + a')])
  all_goals (try rw [hpow_two a'])
  all_goals (try rw [hpow_two a])
  all_goals (try rw [hpow_two (a + a')])
  all_goals (try simp only [map_add, map_mul, hpi_sq])
  all_goals ring_nf
  all_goals simp [htwo, hthree]

-- Selected from lemma_3_1.lean:175.
theorem suzukiRootGL_inv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1)) :
    (SuzukiRootGL m a b)⁻¹ =
      SuzukiRootGL m a (b + a * pi a) := by
  symm
  apply eq_inv_of_mul_eq_one_right
  rw [suzukiRootGL_mul m pi hpi_sq hpi_formula]
  have hcoord :
      b + (b + a * pi a) + a * pi a = 0 := by
    calc
      b + (b + a * pi a) + a * pi a =
          (b + b) + (a * pi a + a * pi a) := by abel
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  rw [CharTwo.add_self_eq_zero, hcoord]
  exact suzukiRootGL_zero_zero m

-- Selected from lemma_3_1.lean:198.
theorem suzukiRootGL_mem_closure_iff
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    A ∈ Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b} ↔
      ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b := by
  constructor
  · intro hA
    exact Subgroup.closure_induction
      (p := fun A _ => ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b)
      (fun _ h => h)
      ⟨0, 0, (suzukiRootGL_zero_zero m).symm⟩
      (fun _ _ _ _ hx hy => by
        rcases hx with ⟨a, b, rfl⟩
        rcases hy with ⟨a', b', rfl⟩
        exact ⟨a + a', b + b' + a * pi a',
          suzukiRootGL_mul m pi hpi_sq hpi_formula a b a' b'⟩)
      (fun _ _ hx => by
        rcases hx with ⟨a, b, rfl⟩
        exact ⟨a, b + a * pi a,
          suzukiRootGL_inv m pi hpi_sq hpi_formula a b⟩)
      hA
  · rintro ⟨a, b, rfl⟩
    exact Subgroup.subset_closure ⟨a, b, rfl⟩

-- Selected from lemma_3_1.lean:232.
noncomputable def suzukiRootCoordinatesEquiv
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    (BinaryGaloisField (2 * m + 1) ×
      BinaryGaloisField (2 * m + 1)) ≃ F := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let toF :
      BinaryGaloisField (2 * m + 1) ×
        BinaryGaloisField (2 * m + 1) → F :=
    fun z => ⟨SuzukiRootGL m z.1 z.2,
      Subgroup.subset_closure ⟨z.1, z.2, rfl⟩⟩
  exact Equiv.ofBijective toF
    ⟨by
      intro z w hzw
      have hroot := suzukiRootGL_injective m z.1 z.2 w.1 w.2
        (congrArg Subtype.val hzw)
      exact Prod.ext hroot.1 hroot.2,
    by
      intro x
      rcases (suzukiRootGL_mem_closure_iff
        m pi hpi_sq hpi_formula (x : GL (Fin 4)
          (BinaryGaloisField (2 * m + 1)))).mp x.property with
        ⟨a, b, hx⟩
      refine ⟨(a, b), ?_⟩
      exact Subtype.ext hx.symm⟩

-- Selected from lemma_3_1.lean:271.
theorem suzukiRootClosure_card
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (hpi_formula : ∀ x, pi x = x ^ (2 ^ (m + 1))) :
    Nat.card
        (Subgroup.closure
          {A | ∃ a b : BinaryGaloisField (2 * m + 1),
            A = SuzukiRootGL m a b} :
          Subgroup (GL (Fin 4) (BinaryGaloisField (2 * m + 1)))) =
      (2 ^ (2 * m + 1)) ^ 2 := by
  let F : Subgroup
      (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
    Subgroup.closure
      {A | ∃ a b : BinaryGaloisField (2 * m + 1),
        A = SuzukiRootGL m a b}
  let e := suzukiRootCoordinatesEquiv m pi hpi_sq hpi_formula
  have hK_card :
      Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    simpa [BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (by omega)
  change Nat.card F = (2 ^ (2 * m + 1)) ^ 2
  calc
    Nat.card F =
        Nat.card (BinaryGaloisField (2 * m + 1) ×
          BinaryGaloisField (2 * m + 1)) :=
      Nat.card_congr e.symm
    _ = Nat.card (BinaryGaloisField (2 * m + 1)) *
        Nat.card (BinaryGaloisField (2 * m + 1)) := Nat.card_prod _ _
    _ = (2 ^ (2 * m + 1)) ^ 2 := by rw [hK_card, pow_two]

-- Selected from lemma_3_1.lean:897.
theorem suzukiTorusGL_one (m : ℕ) :
    SuzukiTorusGL m 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix]

-- Selected from lemma_3_1.lean:904.
theorem suzukiTorusGL_mul
    (m : ℕ)
    (x y : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiTorusGL m x * SuzukiTorusGL m y = SuzukiTorusGL m (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, mul_pow, mul_comm]

-- Selected from lemma_3_1.lean:914.
noncomputable def suzukiTorusHom (m : ℕ) :
    (BinaryGaloisField (2 * m + 1))ˣ →*
      GL (Fin 4) (BinaryGaloisField (2 * m + 1)) where
  toFun := SuzukiTorusGL m
  map_one' := suzukiTorusGL_one m
  map_mul' x y := (suzukiTorusGL_mul m x y).symm

-- Selected from lemma_3_1.lean:923.
theorem suzukiTorusGL_inv
    (m : ℕ) (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    (SuzukiTorusGL m x)⁻¹ = SuzukiTorusGL m x⁻¹ :=
  ((suzukiTorusHom m).map_inv x).symm

-- Selected from lemma_3_1.lean:929.
theorem suzukiTorusHom_injective (m : ℕ) :
    Function.Injective (suzukiTorusHom m) := by
  intro x y hxy
  apply Units.ext
  let K := BinaryGaloisField (2 * m + 1)
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 m
  apply frob.injective
  have h11 := congrArg
    (fun A : GL (Fin 4) K => ((A : Matrix (Fin 4) (Fin 4) K) 1 1)) hxy
  simpa [frob, iterateFrobeniusEquiv_def, iterateFrobenius_def,
    suzukiTorusHom,
    SuzukiTorusGL, SuzukiTorusMatrix] using h11

-- Selected from lemma_3_1.lean:943.
theorem suzukiTorusGL_mem_closure_iff
    (m : ℕ)
    (A : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    A ∈ Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x} ↔
      ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
        A = SuzukiTorusGL m x := by
  constructor
  · intro hA
    exact Subgroup.closure_induction
      (p := fun A _ =>
        ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x)
      (fun _ h => h)
      ⟨1, (suzukiTorusGL_one m).symm⟩
      (fun _ _ _ _ hx hy => by
        rcases hx with ⟨x, rfl⟩
        rcases hy with ⟨y, rfl⟩
        exact ⟨x * y, suzukiTorusGL_mul m x y⟩)
      (fun _ _ hx => by
        rcases hx with ⟨x, rfl⟩
        exact ⟨x⁻¹, ((suzukiTorusHom m).map_inv x).symm⟩)
      hA
  · rintro ⟨x, rfl⟩
    exact Subgroup.subset_closure ⟨x, rfl⟩

-- Selected from lemma_3_1.lean:971.
theorem suzukiTorusCoordinatesMulEquiv (m : ℕ) :
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    ∃ e : (BinaryGaloisField (2 * m + 1))ˣ ≃* H,
      ∀ x, ((e x : H) : GL (Fin 4)
        (BinaryGaloisField (2 * m + 1))) = SuzukiTorusGL m x := by
  let K := BinaryGaloisField (2 * m + 1)
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure
      {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  let toH : Kˣ →* H := (suzukiTorusHom m).codRestrict H
    (fun x => Subgroup.subset_closure ⟨x, rfl⟩)
  have htoH_inj : Function.Injective toH := by
    intro x y hxy
    apply suzukiTorusHom_injective m
    exact congrArg Subtype.val hxy
  have htoH_surj : Function.Surjective toH := by
    intro h
    rcases (suzukiTorusGL_mem_closure_iff m
      (h : GL (Fin 4) K)).mp h.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let e : Kˣ ≃* H :=
    MulEquiv.ofBijective toH ⟨htoH_inj, htoH_surj⟩
  refine ⟨e, ?_⟩
  intro x
  rfl

-- Selected from lemma_3_1.lean:1005.
set_option maxHeartbeats 800000 in
theorem suzukiTorusGL_conj_root
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (m + 1)))
    (a b : BinaryGaloisField (2 * m + 1))
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiTorusGL m x * SuzukiRootGL m a b * (SuzukiTorusGL m x)⁻¹ =
      SuzukiRootGL m
        ((x : BinaryGaloisField (2 * m + 1)) * a)
        ((x : BinaryGaloisField (2 * m + 1)) *
          pi (x : BinaryGaloisField (2 * m + 1)) * b) := by
  rw [show (SuzukiTorusGL m x)⁻¹ = SuzukiTorusGL m x⁻¹ from
    ((suzukiTorusHom m).map_inv x).symm]
  let K := BinaryGaloisField (2 * m + 1)
  have hratio :
      (x : K) ^ (1 + 2 ^ m) * ((x : K) ^ (2 ^ m))⁻¹ = (x : K) := by
    rw [pow_add, pow_one]
    simp [pow_ne_zero _ x.ne_zero]
  have hsigma_sq :
      (x : K) ^ (2 ^ m) * (x : K) ^ (2 ^ m) =
        (x : K) ^ (2 ^ (m + 1)) := by
    rw [← pow_two, ← pow_mul, pow_succ]
  have hmiddle :
      (x : K) ^ (2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
        (x : K) * (x : K) ^ (2 ^ (m + 1)) := by
    calc
      (x : K) ^ (2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
          (x : K) ^ (2 ^ m + (1 + 2 ^ m)) := (pow_add _ _ _).symm
      _ = (x : K) ^ (1 + 2 ^ (m + 1)) := by
        congr 1
        rw [pow_succ]
        omega
      _ = (x : K) * (x : K) ^ (2 ^ (m + 1)) := by
        rw [pow_add, pow_one]
  have houter_sq :
      (x : K) ^ (1 + 2 ^ m) * (x : K) ^ (1 + 2 ^ m) =
        (x : K) ^ (2 + 2 ^ (m + 1)) := by
    rw [← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ]
    omega
  have hsigma_inv :
      (x : K) ^ (2 ^ m) * ((x : K)⁻¹) ^ (2 ^ m) = 1 := by
    rw [← mul_pow]
    simp [x.ne_zero]
  have hpi_iter :
      ((x : K) ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) = (x : K) ^ 2 := by
    calc
      ((x : K) ^ (2 ^ (m + 1))) ^ (2 ^ (m + 1)) =
          pi (pi (x : K)) := by
        rw [hpi_formula, hpi_formula]
      _ = (x : K) ^ 2 := hpi_sq (x : K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, mul_pow, hpi_formula,
      hratio, hsigma_sq, hmiddle, houter_sq, hpi_iter, inv_pow,
      mul_comm, mul_left_comm] <;> ring_nf
  all_goals rw [mul_assoc, hsigma_inv, mul_one]

-- Selected from lemma_3_1.lean:1068.
theorem binaryGaloisField_tits_norm_eq_one_iff
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    (x : BinaryGaloisField (2 * m + 1)) *
        pi (x : BinaryGaloisField (2 * m + 1)) = 1 ↔
      x = 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  constructor
  · intro hx
    have hpi_norm := congrArg pi hx
    simp only [map_mul, map_one, hpi_sq] at hpi_norm
    have hpix_ne : pi (x : K) ≠ 0 :=
      (map_ne_zero pi).2 x.ne_zero
    have hsquare : (x : K) ^ 2 = (x : K) := by
      apply mul_left_cancel₀ hpix_ne
      calc
        pi (x : K) * (x : K) ^ 2 = 1 := hpi_norm
        _ = pi (x : K) * (x : K) := by
          simpa [mul_comm] using hx.symm
    apply Units.ext
    apply mul_left_cancel₀ x.ne_zero
    simpa [pow_two] using hsquare
  · rintro rfl
    simp

-- Selected from lemma_3_1.lean:1097.
theorem suzukiRootClosure_disjoint_torusClosure
    (m : ℕ)
    (pi : BinaryGaloisField (2 * m + 1) ≃+*
      BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ z, pi (pi z) = z ^ 2)
    (hpi_formula : ∀ z, pi z = z ^ (2 ^ (m + 1))) :
    let F : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ a b : BinaryGaloisField (2 * m + 1),
          A = SuzukiRootGL m a b}
    let H : Subgroup
        (GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :=
      Subgroup.closure
        {A | ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
          A = SuzukiTorusGL m x}
    Disjoint F H := by
  let K := BinaryGaloisField (2 * m + 1)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ x : Kˣ, A = SuzukiTorusGL m x}
  change Disjoint F H
  rw [Subgroup.disjoint_def]
  intro A hAF hAH
  rcases (suzukiRootGL_mem_closure_iff
    m pi hpi_sq hpi_formula A).mp hAF with ⟨a, b, hroot⟩
  rcases (suzukiTorusGL_mem_closure_iff m A).mp hAH with ⟨x, htorus⟩
  have heq : SuzukiRootGL m a b = SuzukiTorusGL m x :=
    hroot.symm.trans htorus
  have ha_entry := congrArg
    (fun M : GL (Fin 4) K => ((M : Matrix (Fin 4) (Fin 4) K) 0 1)) heq
  have hb_entry := congrArg
    (fun M : GL (Fin 4) K => ((M : Matrix (Fin 4) (Fin 4) K) 0 2)) heq
  have ha : a = 0 := by
    simpa [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix] using ha_entry
  have hb : b = 0 := by
    simpa [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix] using hb_entry
  calc
    A = SuzukiRootGL m a b := hroot
    _ = SuzukiRootGL m 0 0 := by rw [ha, hb]
    _ = 1 := suzukiRootGL_zero_zero m

/-! Bundled subgroups of the existing concrete matrix group. -/

abbrev K (m : ℕ) := BinaryGaloisField (2 * m + 1)
abbrev G (m : ℕ) := SuzukiMatrixGroup m
abbrev q (m : ℕ) := 2 ^ (2 * m + 1)
abbrev tits (m : ℕ) := SuzukiTorusMovingRank.tits m

def rootGL (m : ℕ) : Subgroup (GL (Fin 4) (K m)) :=
  Subgroup.closure {A | ∃ a b : K m, A = SuzukiRootGL m a b}

def torusGL (m : ℕ) : Subgroup (GL (Fin 4) (K m)) :=
  Subgroup.closure {A | ∃ x : (K m)ˣ, A = SuzukiTorusGL m x}

def borelGL (m : ℕ) : Subgroup (GL (Fin 4) (K m)) := rootGL m ⊔ torusGL m

theorem rootGL_le_group (m : ℕ) : rootGL m ≤ SuzukiMatrixSubgroup m := by
  rw [rootGL, Subgroup.closure_le]
  intro A hA
  exact Subgroup.subset_closure (Or.inl hA)

theorem torusGL_le_group (m : ℕ) : torusGL m ≤ SuzukiMatrixSubgroup m := by
  rw [torusGL, Subgroup.closure_le]
  intro A hA
  exact Subgroup.subset_closure (Or.inr (Or.inl hA))

theorem borelGL_le_group (m : ℕ) : borelGL m ≤ SuzukiMatrixSubgroup m :=
  sup_le (rootGL_le_group m) (torusGL_le_group m)

def root (m : ℕ) : Subgroup (G m) :=
  (rootGL m).comap (SuzukiMatrixSubgroup m).subtype

def torus (m : ℕ) : Subgroup (G m) :=
  (torusGL m).comap (SuzukiMatrixSubgroup m).subtype

def borel (m : ℕ) : Subgroup (G m) :=
  (borelGL m).comap (SuzukiMatrixSubgroup m).subtype

def rootEquiv (m : ℕ) : root m ≃* rootGL m :=
  Subgroup.subgroupOfEquivOfLe (rootGL_le_group m)

def torusEquiv (m : ℕ) : torus m ≃* torusGL m :=
  Subgroup.subgroupOfEquivOfLe (torusGL_le_group m)

def borelEquiv (m : ℕ) : borel m ≃* borelGL m :=
  Subgroup.subgroupOfEquivOfLe (borelGL_le_group m)

theorem card_root (m : ℕ) : Nat.card (root m) = (q m) ^ 2 := by
  calc
    Nat.card (root m) = Nat.card (rootGL m) := Nat.card_congr (rootEquiv m).toEquiv
    _ = (q m) ^ 2 := suzukiRootClosure_card m (tits m)
      (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)

theorem card_torus (m : ℕ) : Nat.card (torus m) = q m - 1 := by
  obtain ⟨e, _⟩ := suzukiTorusCoordinatesMulEquiv m
  calc
    Nat.card (torus m) = Nat.card (torusGL m) := Nat.card_congr (torusEquiv m).toEquiv
    _ = Nat.card (K m)ˣ := Nat.card_congr e.symm.toEquiv
    _ = Nat.card (K m) - 1 := Nat.card_units (K m)
    _ = q m - 1 := by rw [SuzukiTorusMovingRank.card_field]

end Kourovka2135.SuzukiGeometry

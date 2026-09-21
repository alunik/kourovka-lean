import Kourovka2135.SLTwoTetrahedralObstruction
import Kourovka2135.SLTwoTraceGoodSetProjective
import Kourovka2135.Vendor.CFSG.ElementaryAbelian

/-! An actual four-group normalized by a projective tetrahedral element.

All subgroup, action and nontriviality data are derived from the concrete
quaternion matrices. In characteristic three the negative of the order-three
lift belongs to the broad trace good set and has the same projective image.
The normalizer obstruction consequently needs no order-preserving lift.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoTetrahedralNormalizer

open scoped Matrix IsMulCommutative
open SLTwoTetrahedralObstruction SLTwoNonscalarWordValues OddPSLTwoProjectiveChart

variable {F : Type*} [Field F]

theorem quaternionI_sq : (quaternionI (F := F)).val ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionI, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem quaternionJ_sq (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    (quaternionJ x y hxy).val ^ 2 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionJ, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    solve | ring | linear_combination hxy

theorem quotient_square_eq_one (A : SLTwo.SL2 F)
    (hA : A.val ^ 2 = -1) : (quotient F A) ^ 2 = 1 := by
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨-1, by simp, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem quaternion_images_commute (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    Commute (quotient F quaternionI) (quotient F (quaternionJ x y hxy)) := by
  have hi := quotient_square_eq_one quaternionI (quaternionI_sq (F := F))
  have hj := quotient_square_eq_one (quaternionJ x y hxy) (quaternionJ_sq x y hxy)
  have hij : (quotient F quaternionI * quotient F (quaternionJ x y hxy)) ^ 2 = 1 := by
    rw [← map_mul]
    exact quotient_square_eq_one (quaternionK x y hxy) (quaternionK_sq x y hxy)
  have hi' : (quotient F quaternionI)⁻¹ = quotient F quaternionI :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hi)
  have hj' : (quotient F (quaternionJ x y hxy))⁻¹ = quotient F (quaternionJ x y hxy) :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hj)
  have hij' : (quotient F quaternionI * quotient F (quaternionJ x y hxy))⁻¹ =
      quotient F quaternionI * quotient F (quaternionJ x y hxy) :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hij)
  change quotient F quaternionI * quotient F (quaternionJ x y hxy) =
    quotient F (quaternionJ x y hxy) * quotient F quaternionI
  simpa only [mul_inv_rev, hi', hj'] using hij'.symm

theorem tetrahedral_conj_i (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    tetrahedral x y hxy h2 * quaternionI * (tetrahedral x y hxy h2)⁻¹ =
      quaternionK x y hxy := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [tetrahedral_inv_val, quaternionK_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrahedral, quaternionI, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> solve | ring | linear_combination hxy | linear_combination -hxy |
      linear_combination (2 : F) * hxy | linear_combination (-2 : F) * hxy

theorem tetrahedral_inv_conj_i (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    (tetrahedral x y hxy h2)⁻¹ * quaternionI * tetrahedral x y hxy h2 =
      quaternionJ x y hxy := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [tetrahedral_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tetrahedral, quaternionI, quaternionJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> solve | ring | linear_combination hxy | linear_combination -hxy |
      linear_combination (2 : F) * hxy | linear_combination (-2 : F) * hxy

theorem tetrahedral_conj_j (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    tetrahedral x y hxy h2 * quaternionJ x y hxy * (tetrahedral x y hxy h2)⁻¹ =
      quaternionI := by
  rw [← tetrahedral_inv_conj_i x y hxy h2]
  group

theorem commutator_tetrahedral_k (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    paperCommutator (tetrahedral x y hxy h2) (quaternionK x y hxy) =
      quaternionJ x y hxy := by
  have hconj : (tetrahedral x y hxy h2)⁻¹ * quaternionK x y hxy *
      tetrahedral x y hxy h2 = quaternionI := by
    rw [← tetrahedral_conj_i x y hxy h2]
    group
  calc
    _ = ((tetrahedral x y hxy h2)⁻¹ * quaternionK x y hxy *
      tetrahedral x y hxy h2)⁻¹ * quaternionK x y hxy := by
        unfold paperCommutator
        group
    _ = quaternionI⁻¹ * quaternionK x y hxy := by rw [hconj]
    _ = quaternionJ x y hxy := by unfold quaternionK; group

def fourGroup (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) : Subgroup (Q F) :=
  Subgroup.zpowers (quotient F quaternionI) ⊔
    Subgroup.zpowers (quotient F (quaternionJ x y hxy))

theorem fourGroup_elementary (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    IsElementaryAbelian 2 (fourGroup x y hxy) := by
  let : IsElementaryAbelian 2 (Subgroup.zpowers (quotient F (quaternionI (F := F)))) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (quotient_square_eq_one _ (quaternionI_sq (F := F)))
  let : IsElementaryAbelian 2 (Subgroup.zpowers (quotient F (quaternionJ x y hxy))) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (quotient_square_eq_one _ (quaternionJ_sq x y hxy))
  apply IsElementaryAbelian.sup_of_le_centralizer
  apply Subgroup.zpowers_le.mpr
  apply Subgroup.mem_centralizer_iff.mpr
  rintro z ⟨n, rfl⟩
  exact (quaternion_images_commute x y hxy).zpow_left n |>.eq

theorem quaternionI_mem (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    quotient F quaternionI ∈ fourGroup x y hxy :=
  (show Subgroup.zpowers (quotient F quaternionI) ≤ fourGroup x y hxy from le_sup_left)
    (Subgroup.mem_zpowers _)

theorem quaternionJ_mem (x y : F) (hxy : x ^ 2 + y ^ 2 = -1) :
    quotient F (quaternionJ x y hxy) ∈ fourGroup x y hxy :=
  (show Subgroup.zpowers (quotient F (quaternionJ x y hxy)) ≤ fourGroup x y hxy
    from le_sup_right) (Subgroup.mem_zpowers _)

theorem tetrahedral_normalizes [Finite F] (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    quotient F (tetrahedral x y hxy h2) ∈ Subgroup.normalizer (fourGroup x y hxy) := by
  let a : Q F := quotient F (tetrahedral x y hxy h2)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [fourGroup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    apply sup_le <;> apply Subgroup.zpowers_le.mpr
    · change a * quotient F quaternionI * a⁻¹ ∈ _
      have he := congrArg (quotient F) (tetrahedral_conj_i x y hxy h2)
      simp only [map_mul, map_inv] at he
      change a * quotient F quaternionI * a⁻¹ = quotient F (quaternionK x y hxy) at he
      rw [he]
      change quotient F (quaternionI * quaternionJ x y hxy) ∈ _
      rw [map_mul]
      exact (fourGroup x y hxy).mul_mem (quaternionI_mem x y hxy) (quaternionJ_mem x y hxy)
    · change a * quotient F (quaternionJ x y hxy) * a⁻¹ ∈ _
      have he := congrArg (quotient F) (tetrahedral_conj_j x y hxy h2)
      simp only [map_mul, map_inv] at he
      change a * quotient F (quaternionJ x y hxy) * a⁻¹ = quotient F quaternionI at he
      rw [he]
      exact quaternionI_mem x y hxy
  · rw [Subgroup.card_map_of_injective (MulAut.conj a).injective]

theorem conjugate_commutator_ne_one (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    paperCommutator (quotient F (tetrahedral x y hxy h2))
      ((quotient F quaternionI)⁻¹ * quotient F (tetrahedral x y hxy h2) *
        quotient F quaternionI) ≠ 1 := by
  have he : paperCommutator (tetrahedral x y hxy h2)
      (quaternionI⁻¹ * tetrahedral x y hxy h2 * quaternionI) = quaternionJ x y hxy := by
    calc
      _ = paperCommutator (tetrahedral x y hxy h2)
        (paperCommutator (tetrahedral x y hxy h2) quaternionI) := by
          unfold paperCommutator
          group
      _ = quaternionJ x y hxy := by rw [commutator_tetrahedral_i, commutator_tetrahedral_k]
  have hmap := congrArg (quotient F) he
  simp only [paperCommutator, map_mul, map_inv] at hmap ⊢
  rw [hmap]
  apply image_ne_one_of_nonscalar
  exact nonscalar_of_trace_zero _ h2 (by simp [quaternionJ, Matrix.trace_fin_two])

theorem tetrahedral_projective_good (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (h2 : (2 : F) ≠ 0) :
    quotient F (tetrahedral x y hxy h2) ∈
      SLTwoTraceGoodSetProjective.projectiveGoodSet (F := F) := by
  let a := tetrahedral x y hxy h2
  have ht : a.val.trace = -1 := by
    simp [a, tetrahedral, Matrix.trace_fin_two]
    field_simp
    ring
  have hn : Nonscalar a := tetrahedral_nonscalar x y hxy h2
  by_cases h3 : (3 : F) = 0
  · let z : SLTwo.SL2 F := ⟨-1, by simp [Matrix.det_fin_two]⟩
    have hz : z ∈ Subgroup.center (SLTwo.SL2 F) := by
      apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
      exact ⟨-1, by simp, by ext i j; fin_cases i <;> fin_cases j <;> simp [z]⟩
    have hzq : quotient F z = 1 := (QuotientGroup.eq_one_iff _).mpr hz
    refine ⟨z * a, ?_, by rw [map_mul, hzq, one_mul]⟩
    have hval : (z * a).val = -a.val := by
      change (-1 : Matrix (Fin 2) (Fin 2) F) * a.val = -a.val
      simp
    have ht' : (z * a).val.trace = 1 := by rw [hval, Matrix.trace_neg, ht, neg_neg]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨r, hr⟩
      apply hn
      refine ⟨-r, ?_⟩
      rw [hval] at hr
      calc
        a.val = -Matrix.scalar (Fin 2) r := by rw [← hr, neg_neg]
        _ = Matrix.scalar (Fin 2) (-r) := by
          ext i j
          by_cases hij : i = j <;> simp [Matrix.scalar, hij]
    · rw [ht']
      intro he
      have : (1 : F) = 0 := by linear_combination -he
      exact one_ne_zero this
    · rw [ht']
      exact one_ne_zero
  · refine ⟨a, ⟨hn, ?_, ?_⟩, rfl⟩
    · rw [ht]
      intro he
      apply h3
      linear_combination -he
    · rw [ht]
      exact neg_ne_zero.mpr one_ne_zero

end Kourovka2135.OddPSLTwoTetrahedralNormalizer

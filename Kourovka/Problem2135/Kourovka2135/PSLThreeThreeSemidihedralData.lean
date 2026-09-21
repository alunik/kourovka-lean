import Kourovka2135.PSL33GoodSets
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.GroupTheory.Index

/-! A concrete semidihedral subgroup of order sixteen and odd index in the
actual special/projective special linear group of degree three over F3. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Kourovka2135.PSLThreeThreeSemidihedralData
open scoped MatrixGroups
open Matrix
abbrev S := SL(3, ZMod 3)
abbrev Q := PSL(3, ZMod 3)

def x : S := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 2], by decide⟩
def y : S := ⟨!![1, 1, 0; 0, 2, 0; 0, 0, 2], by decide⟩
def normalForm (i : Fin 8 × Fin 2) : S := x ^ i.1.val * y ^ i.2.val
def elements : Finset S := Finset.univ.image normalForm

theorem normalForm_injective : Function.Injective normalForm := by decide
theorem x_pow_eight : x ^ 8 = 1 := by decide
theorem x_pow_four_ne_one : x ^ 4 ≠ 1 := by decide
theorem y_pow_two : y ^ 2 = 1 := by decide
theorem conjugate_x : y * x * y⁻¹ = x ^ 3 := by decide
theorem orderOf_x : orderOf x = 8 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2) x_pow_four_ne_one x_pow_eight

def subgroup : Subgroup S where
  carrier := elements
  one_mem' := by decide
  mul_mem' := by
    intro a b ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact (by decide : ∀ i j : Fin 8 × Fin 2,
      normalForm i * normalForm j ∈ elements) i j
  inv_mem' := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (by decide : ∀ i : Fin 8 × Fin 2, (normalForm i)⁻¹ ∈ elements) i

def sx : subgroup := ⟨x, by change x ∈ elements; decide⟩
def sy : subgroup := ⟨y, by change y ∈ elements; decide⟩

theorem subgroup_card : Nat.card subgroup = 16 := by
  change Nat.card ↥elements = 16
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

theorem subgroup_generated : Subgroup.closure ({sx, sy} : Set subgroup) = ⊤ := by
  apply top_le_iff.mp
  intro a _
  have hm : (a : S) ∈ elements := a.property
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
  have ha : a = sx ^ i.1.val * sy ^ i.2.val := Subtype.ext hi.symm
  rw [ha]
  exact Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem orderOf_sx : orderOf sx = 8 := by
  rw [← orderOf_injective subgroup.subtype Subtype.val_injective sx]
  exact orderOf_x
theorem sy_pow_two : sy ^ 2 = 1 := Subtype.ext y_pow_two
theorem conjugate_sx : sy * sx * sy⁻¹ = sx ^ 3 := Subtype.ext conjugate_x

noncomputable def specialLinearEquivDetKernel :
    S ≃ (GeneralLinearGroup.det : GeneralLinearGroup (Fin 3) (ZMod 3) →* (ZMod 3)ˣ).ker where
  toFun A := ⟨SpecialLinearGroup.toGL A, SpecialLinearGroup.coeToGL_det A⟩
  invFun A := ⟨A.val.val, congrArg Units.val A.property⟩
  left_inv _ := rfl
  right_inv A := by apply Subtype.ext; apply Units.ext; rfl

theorem specialLinear_card : Nat.card S = 5616 := by
  let δ := (GeneralLinearGroup.det : GeneralLinearGroup (Fin 3) (ZMod 3) →* (ZMod 3)ˣ)
  have hi : δ.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective]
    rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (ZMod 3)ˣ) ≃* (ZMod 3)ˣ).toEquiv,
      Nat.card_eq_fintype_card]
    decide
  have hGL : Nat.card (GeneralLinearGroup (Fin 3) (ZMod 3)) = 11232 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have h := δ.ker.card_mul_index
  rw [hi, hGL, ← Nat.card_congr specialLinearEquivDetKernel] at h
  omega

theorem subgroup_index : subgroup.index = 351 := by
  have h := subgroup.card_mul_index
  rw [subgroup_card, specialLinear_card] at h
  omega

theorem subgroup_index_odd : Odd subgroup.index := by rw [subgroup_index]; decide

theorem center_eq_bot : Subgroup.center S = ⊥ := by
  apply bot_unique
  intro a ha
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp ha
  have hr1 : r = 1 := (by decide : ∀ r : ZMod 3, r ^ 3 = 1 → r = 1) r hr
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  simpa [hr1] using he.symm

noncomputable def projectiveEquiv : S ≃* Q :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center S))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', center_eq_bot]),
      QuotientGroup.mk'_surjective _⟩

theorem projective_card : Nat.card Q = 5616 := by
  rw [← Nat.card_congr projectiveEquiv.toEquiv, specialLinear_card]

end Kourovka2135.PSLThreeThreeSemidihedralData

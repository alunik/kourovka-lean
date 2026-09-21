import Kourovka2135.BinaryTensorCoefficient
import Mathlib.LinearAlgebra.Basis.Basic

/-! The socle of the actual squarefree coefficient algebra.

Multiplication by its generators has a one-dimensional common kernel. A
finite induction using their commuting square-zero actions shows that every
nonzero generator-stable subspace meets this kernel. These statements use
the explicit coefficient algebra, with no irreducibility hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorSocle

open BinaryTensorCoefficient
open scoped IsMulCommutative

variable (k : Type*) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

/-- Multiplication inserts a missing generator without changing its coefficient. -/
theorem generator_mul_coeff (i : I) (J : Finset I) (hi : i ∉ J)
    (v : Carrier k I) :
    (basis k I).repr (generator k I i * v) (insert i J) =
      (basis k I).repr v J := by
  classical
  suffices h : ((basis k I).coord (insert i J)).comp
      (LinearMap.mulLeft k (generator k I i)) = (basis k I).coord J by
    exact LinearMap.congr_fun h v
  apply (basis k I).ext
  intro K
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply,
    Module.Basis.coord_apply, generator_mul_basis]
  by_cases hiK : i ∈ K
  · have hKJ : K ≠ J := by intro h; exact hi (h ▸ hiK)
    simp [hiK, hKJ]
  · have heq : insert i K = insert i J ↔ K = J := by
      constructor
      · intro h
        have hh := congrArg (fun S : Finset I => S.erase i) h
        simpa only [Finset.erase_insert hiK, Finset.erase_insert hi] using hh
      · exact congrArg (insert i)
    by_cases hKJ : K = J
    · subst K
      simp [hi]
    · have hins : insert i K ≠ insert i J := fun h => hKJ (heq.mp h)
      simp [hiK, hKJ, hins]

/-- A vector killed by every generator is a scalar multiple of the top monomial. -/
theorem eq_smul_top_of_generator_mul_eq_zero (v : Carrier k I)
    (hv : ∀ i : I, generator k I i * v = 0) :
    v = (basis k I).repr v Finset.univ • basis k I Finset.univ := by
  classical
  apply (basis k I).repr.injective
  ext J
  by_cases hJ : J = Finset.univ
  · subst J
    simp
  · have hex : ∃ i : I, i ∉ J := by
      by_contra h
      apply hJ
      apply Finset.eq_univ_of_forall
      intro i
      exact not_not.mp (fun hi => h ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    have hz := generator_mul_coeff k I i J hi v
    rw [hv i, map_zero, Finsupp.zero_apply] at hz
    rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_of_ne hJ, smul_zero]
    exact hz.symm

/-- The top monomial is killed by each of the square-zero generators. -/
theorem generator_mul_top (i : I) :
    generator k I i * basis k I Finset.univ = 0 := by
  rw [generator_mul_basis]
  simp

theorem generator_mul_eq_zero_iff (v : Carrier k I) :
    (∀ i : I, generator k I i * v = 0) ↔
      ∃ a : k, v = a • basis k I Finset.univ := by
  constructor
  · intro hv
    exact ⟨_, eq_smul_top_of_generator_mul_eq_zero k I v hv⟩
  · rintro ⟨a, rfl⟩ i
    rw [mul_smul_comm, generator_mul_top, smul_zero]

/-- Commuting square-zero multiplication finds a nonzero common-kernel vector
inside every nonzero generator-stable subspace. -/
theorem exists_nonzero_annihilated (W : Submodule k (Carrier k I))
    (hW : ∃ v ∈ W, v ≠ 0)
    (hstable : ∀ (i : I) (v : Carrier k I), v ∈ W → generator k I i * v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ i : I, generator k I i * v = 0 := by
  classical
  have hind (S : Finset I) :
      ∃ v ∈ W, v ≠ 0 ∧ ∀ i ∈ S, generator k I i * v = 0 := by
    induction S using Finset.induction_on with
    | empty =>
        obtain ⟨v, hv, hne⟩ := hW
        exact ⟨v, hv, hne, by simp⟩
    | @insert i S _ ih =>
        obtain ⟨v, hv, hne, hkill⟩ := ih
        by_cases hi : generator k I i * v = 0
        · refine ⟨v, hv, hne, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact hi
          · exact hkill j hj
        · refine ⟨generator k I i * v, hstable i v hv, hi, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · rw [← mul_assoc, generator_square, zero_mul]
          · rw [mul_left_comm, hkill j hj, mul_zero]
  obtain ⟨v, hv, hne, hkill⟩ := hind Finset.univ
  exact ⟨v, hv, hne, fun i => hkill i (Finset.mem_univ i)⟩

/-- Every nonzero subspace stable under generator multiplication contains top. -/
theorem top_mem_of_generator_stable (W : Submodule k (Carrier k I))
    (hW : ∃ v ∈ W, v ≠ 0)
    (hstable : ∀ (i : I) (v : Carrier k I), v ∈ W → generator k I i * v ∈ W) :
    basis k I Finset.univ ∈ W := by
  obtain ⟨v, hv, hne, hkill⟩ := exists_nonzero_annihilated k I W hW hstable
  obtain ⟨a, ha⟩ := (generator_mul_eq_zero_iff k I v).mp hkill
  have ha0 : a ≠ 0 := by
    intro h
    apply hne
    simp [ha, h]
  have hm := W.smul_mem a⁻¹ hv
  simpa only [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul] using hm

end Kourovka2135.BinaryTensorSocle

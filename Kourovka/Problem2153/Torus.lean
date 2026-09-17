import Kourovka.Problem2153.RootSystem

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem

/-- Multiplication on nonzero binary GF8 codes, shifted down by one. -/
def indexMul : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 1, 2, 3, 4, 5, 6],
    ![1, 3, 5, 2, 0, 6, 4],
    ![2, 5, 4, 6, 3, 0, 1],
    ![3, 2, 6, 5, 1, 4, 0],
    ![4, 0, 3, 1, 6, 2, 5],
    ![5, 6, 0, 4, 2, 1, 3],
    ![6, 4, 1, 0, 5, 3, 2]]

def indexInv : Fin 7 → Fin 7 := ![0, 4, 5, 6, 1, 2, 3]

theorem torusDiag_mul : ∀ a b c d : Fin 7, ∀ i : Fin 26,
    WilsonModel.torusDiag a b i * WilsonModel.torusDiag c d i =
      WilsonModel.torusDiag (indexMul a c) (indexMul b d) i := by
  decide +kernel

theorem torus_zero_zero : torus 0 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.diagonal (WilsonModel.torusDiag 0 0) = 1
  decide +kernel

theorem torus_mul (a b c d : Fin 7) :
    torus a b * torus c d = torus (indexMul a c) (indexMul b d) := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.diagonal (WilsonModel.torusDiag a b) *
    Matrix.diagonal (WilsonModel.torusDiag c d) =
      Matrix.diagonal (WilsonModel.torusDiag (indexMul a c) (indexMul b d))
  rw [Matrix.diagonal_mul_diagonal]
  exact congrArg Matrix.diagonal (funext (torusDiag_mul a b c d))

theorem index_mul_inv (a : Fin 7) : indexMul a (indexInv a) = 0 := by
  fin_cases a <;> decide

theorem torus_inv (a b : Fin 7) : (torus a b)⁻¹ = torus (indexInv a) (indexInv b) := by
  apply inv_eq_of_mul_eq_one_right
  rw [torus_mul, index_mul_inv, index_mul_inv, torus_zero_zero]

/-- Every element of the torus closure is one of the 49 displayed diagonal matrices. -/
theorem exists_torus_of_mem_H {g : G} (hg : g ∈ H) : ∃ a b, g = torus a b := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => obtain ⟨⟨a,b⟩, rfl⟩ := hg; exact ⟨a,b,rfl⟩
  | one => exact ⟨0,0,torus_zero_zero.symm⟩
  | mul g h _ _ hg hh =>
    obtain ⟨a,b,rfl⟩ := hg
    obtain ⟨c,d,rfl⟩ := hh
    exact ⟨indexMul a c,indexMul b d,torus_mul a b c d⟩
  | inv g _ hg =>
    obtain ⟨a,b,rfl⟩ := hg
    exact ⟨indexInv a,indexInv b,torus_inv a b⟩

theorem indexMul_comm (a b : Fin 7) : indexMul a b = indexMul b a := by
  fin_cases a <;> fin_cases b <;> decide

theorem torus_commute (a b c d : Fin 7) : Commute (torus a b) (torus c d) := by
  change torus a b * torus c d = torus c d * torus a b
  rw [torus_mul, torus_mul, indexMul_comm a c, indexMul_comm b d]

theorem commute_of_mem_H {g h : G} (hg : g ∈ H) (hh : h ∈ H) : Commute g h := by
  obtain ⟨a,b,rfl⟩ := exists_torus_of_mem_H hg
  obtain ⟨c,d,rfl⟩ := exists_torus_of_mem_H hh
  exact torus_commute a b c d

def indexFourth (a : Fin 7) : Fin 7 := indexMul (indexMul a a) (indexMul a a)

theorem torus_r_entry : ∀ a b : Fin 7, ∀ i j : Fin 26,
    WilsonModel.torusDiag a b i * WilsonModel.rho i j =
      WilsonModel.rho i j *
        WilsonModel.torusDiag a (indexMul (indexFourth a) (indexInv b)) j := by
  decide +kernel

theorem torus_s_entry : ∀ a b : Fin 7, ∀ i j : Fin 26,
    WilsonModel.torusDiag a b i * WilsonModel.sigma i j =
      WilsonModel.sigma i j * WilsonModel.torusDiag b a j := by
  decide +kernel

theorem torus_r_commutation (a b : Fin 7) :
    torus a b * r = r * torus a (indexMul (indexFourth a) (indexInv b)) := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.diagonal (WilsonModel.torusDiag a b) * WilsonModel.rho =
    WilsonModel.rho * Matrix.diagonal
      (WilsonModel.torusDiag a (indexMul (indexFourth a) (indexInv b)))
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact torus_r_entry a b i j

theorem torus_s_commutation (a b : Fin 7) : torus a b * s = s * torus b a := by
  apply Subtype.ext
  apply Units.ext
  change Matrix.diagonal (WilsonModel.torusDiag a b) * WilsonModel.sigma =
    WilsonModel.sigma * Matrix.diagonal (WilsonModel.torusDiag b a)
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact torus_s_entry a b i j

theorem r_square : r * r = 1 := Subtype.ext (Units.ext WilsonModel.rho_square)
theorem s_square : s * s = 1 := Subtype.ext (Units.ext WilsonModel.sigma_square)
theorem r_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right r_square
theorem s_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right s_square

theorem torus_conj_r (a b : Fin 7) :
    rightConj (torus a b) r = torus a (indexMul (indexFourth a) (indexInv b)) := by
  rw [rightConj, r_inv, mul_assoc, torus_r_commutation, ← mul_assoc, r_square, one_mul]

theorem torus_conj_s (a b : Fin 7) : rightConj (torus a b) s = torus b a := by
  rw [rightConj, s_inv, mul_assoc, torus_s_commutation, ← mul_assoc, s_square, one_mul]

theorem rightConj_mem_H_r {g : G} (hg : g ∈ H) : rightConj g r ∈ H := by
  obtain ⟨a,b,rfl⟩ := exists_torus_of_mem_H hg
  rw [torus_conj_r]
  exact torus_mem_H _ _

theorem rightConj_mem_H_s {g : G} (hg : g ∈ H) : rightConj g s ∈ H := by
  obtain ⟨a,b,rfl⟩ := exists_torus_of_mem_H hg
  rw [torus_conj_s]
  exact torus_mem_H _ _

theorem r_mem_normalizer_H : r ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · exact rightConj_mem_H_r
  · intro hg
    have h := rightConj_mem_H_r hg
    have he : rightConj (rightConj g r) r = g := by
      unfold rightConj
      rw [r_inv]
      calc
        r * (r * g * r) * r = (r * r) * g * (r * r) := by group
        _ = g := by rw [r_square]; simp
    exact he ▸ h

theorem s_mem_normalizer_H : s ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · exact rightConj_mem_H_s
  · intro hg
    have h := rightConj_mem_H_s hg
    have he : rightConj (rightConj g s) s = g := by
      unfold rightConj
      rw [s_inv]
      calc
        s * (s * g * s) * s = (s * s) * g * (s * s) := by group
        _ = g := by rw [s_square]; simp
    exact he ▸ h

theorem W_le_normalizer_H : W ≤ Subgroup.normalizer (H : Set G) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · exact r_mem_normalizer_H
  · obtain rfl := Set.mem_singleton_iff.mp hg
    exact s_mem_normalizer_H

end Kourovka.Problem2153.RootSystem

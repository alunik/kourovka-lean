import Kourovka.Problem2153.NormalGeneration.Identities
import Kourovka.Problem2153.TorusAction

set_option autoImplicit false
set_option maxRecDepth 10000
namespace Kourovka.Problem2153.RootSystem
open scoped commutatorElement
open NormalGeneration

private def torusExponent : Fin 7 → ℕ := ![0, 1, 3, 2, 6, 4, 5]

private theorem torusExponent_correct : ∀ a : Fin 7, indexPow 1 (torusExponent a) = a := by
  decide +kernel

private theorem indexPow_zero (n : ℕ) : indexPow 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indexPow, ih]; rfl

theorem torus_mem_of_two (Q : Subgroup G) (h10 : torus 1 0 ∈ Q) (h01 : torus 0 1 ∈ Q)
    (a b : Fin 7) : torus a b ∈ Q := by
  have ha := Q.pow_mem h10 (torusExponent a)
  have hb := Q.pow_mem h01 (torusExponent b)
  rw [torus_pow, torusExponent_correct, indexPow_zero] at ha
  rw [torus_pow, torusExponent_correct, indexPow_zero] at hb
  have hh := Q.mul_mem ha hb
  rw [torus_mul] at hh
  have hleft : indexMul a 0 = a := by fin_cases a <;> decide
  have hright : indexMul 0 b = b := by fin_cases b <;> decide
  simpa only [hleft, hright] using hh

/-- Actual short matrix words show that any normal subgroup containing the central
root base contains all Wilson generators. No Bruhat or simplicity assumption is used. -/
theorem normal_eq_top_of_rootBase11 (Q : Subgroup G) [Q.Normal]
    (hz : rootBase 11 ∈ Q) : Q = ⊤ := by
  have hb := rootBase_three Q hz
  have hr : r ∈ Q := SuzukiR_identity ▸ suzukiWord_mem Q hb _
  have hx : x ∈ Q := SuzukiX_identity ▸ suzukiWord_mem Q hb _
  have hh01 : torus 0 1 ∈ Q := SuzukiH_identity ▸ suzukiWord_mem Q hb _
  have htconj : rightConj t r ∈ Q := by
    rw [← root_commutator_identity]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.inv_mem hx)
      (Q.inv_mem (rightConj_mem_normal Q hx _))) hx) (rightConj_mem_normal Q hx _)
  have ht : t ∈ Q := by
    have hh := rightConj_mem_normal Q htconj r⁻¹
    simpa only [rightConj_inv_cancel] using hh
  have hs : s ∈ Q := by
    rw [← sl2_identity]
    exact Q.mul_mem (Q.mul_mem ht (rightConj_mem_normal Q ht s)) ht
  have hh10 : torus 1 0 ∈ Q := by
    simpa only [torus_conj_s] using rightConj_mem_normal Q hh01 s
  exact eq_top_of_generators Q ht hx hr hs (torus_mem_of_two Q hh10 hh01)

/-- The actual root subgroup normally generates the concrete ambient group. -/
theorem normalClosure_Z : Subgroup.normalClosure (Z : Set G) = ⊤ := by
  apply normal_eq_top_of_rootBase11
  rw [← root_one 11]
  exact Subgroup.subset_normalClosure (Subgroup.subset_closure ⟨1, rfl⟩)

/-- A checked commutator contains the root base; its normal generation proves perfectness. -/
theorem ambient_perfect : commutator G = ⊤ := by
  apply normal_eq_top_of_rootBase11
  rw [← root_one 11, ← perfect_identity]
  have h : ⁅(root 11 6)⁻¹, (torus 1 0)⁻¹⁆ ∈ commutator G :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  simpa only [commutatorElement_def, inv_inv] using h

theorem Z_le_commutator : Z ≤ commutator G := by rw [ambient_perfect]; exact le_top

#print axioms normal_eq_top_of_rootBase11
#print axioms normalClosure_Z
#print axioms ambient_perfect
end Kourovka.Problem2153.RootSystem

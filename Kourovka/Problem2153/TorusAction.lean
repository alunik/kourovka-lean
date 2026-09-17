import Kourovka.Problem2153.Torus
import Kourovka.Problem2153.TorusAction.Data

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem
open WilsonModel

def indexPow (a : Fin 7) : ℕ → Fin 7
  | 0 => 0
  | n + 1 => indexMul (indexPow a n) a

theorem torus_pow (a b : Fin 7) (n : ℕ) :
    torus a b ^ n = torus (indexPow a n) (indexPow b n) := by
  induction n with
  | zero => exact torus_zero_zero.symm
  | succ n ih => rw [pow_succ, ih, torus_mul]; rfl

def sectionT (i : Fin 12) (a : Fin 8) : G :=
  torus (sectionParameters i a).1 (sectionParameters i a).2

def kernelT (i : Fin 12) : G :=
  torus (RootData.kernelParameters i).1 (RootData.kernelParameters i).2

theorem parameterMul_ne_zero : ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 → parameterMul a b ≠ 0 := by
  decide +kernel

theorem parameterAction_ne_zero (i : Fin 12) (c d : Fin 7) {a : Fin 8} (ha : a ≠ 0) :
    parameterAction i c d a ≠ 0 :=
  parameterMul_ne_zero a _ ha (Fin.succ_ne_zero _)

theorem parameterAction_zero (i : Fin 12) (c d : Fin 7) : parameterAction i c d 0 = 0 := by
  change Field8.code (0 * Field8.ofCode _) = 0
  rw [zero_mul]
  rfl

theorem section_multiply_parameters : ∀ i : Fin 12, ∀ a b : Fin 8, a ≠ 0 → b ≠ 0 →
    (indexMul (sectionParameters i a).1 (sectionParameters i b).1,
      indexMul (sectionParameters i a).2 (sectionParameters i b).2) =
        sectionParameters i (parameterMul a b) := by
  decide +kernel

theorem sectionT_mul (i : Fin 12) {a b : Fin 8} (ha : a ≠ 0) (hb : b ≠ 0) :
    sectionT i a * sectionT i b = sectionT i (parameterMul a b) := by
  unfold sectionT
  rw [torus_mul]
  have he := section_multiply_parameters i a b ha hb
  exact congrArg (fun p : Fin 7 × Fin 7 => torus p.1 p.2) he

theorem torus_decomposition_parameters : ∀ i : Fin 12, ∀ c d : Fin 7,
    (indexMul (indexPow (RootData.kernelParameters i).1 (kernelExponent i c d).val)
        (sectionParameters i (weightValue i c d).succ).1,
      indexMul (indexPow (RootData.kernelParameters i).2 (kernelExponent i c d).val)
        (sectionParameters i (weightValue i c d).succ).2) = (c,d) := by
  decide +kernel

theorem torus_decomposition (i : Fin 12) (c d : Fin 7) :
    torus c d = kernelT i ^ (kernelExponent i c d).val *
      sectionT i (weightValue i c d).succ := by
  unfold kernelT sectionT
  rw [torus_pow, torus_mul]
  exact (congrArg (fun p : Fin 7 × Fin 7 => torus p.1 p.2)
    (torus_decomposition_parameters i c d)).symm

/-- Every root parameter transforms by its actual torus character. The proof uses the
12 checked kernel commutations and finite scalar identities, not an assumed root action. -/
theorem root_conj_torus (i : Fin 12) (a : Fin 8) (c d : Fin 7) :
    rightConj (root i a) (torus c d) = root i (parameterAction i c d a) := by
  by_cases ha : a = 0
  · subst a
    simp [parameterAction_zero, rightConj]
  have hnonzero := parameterAction_ne_zero i c d ha
  change rightConj (if a = 0 then 1 else rightConj (rootBase i) (sectionT i a))
    (torus c d) = if parameterAction i c d a = 0 then 1 else
      rightConj (rootBase i) (sectionT i (parameterAction i c d a))
  rw [if_neg ha, if_neg hnonzero, ← rightConj_mul, torus_decomposition i c d]
  have hc : Commute (sectionT i a) (kernelT i ^ (kernelExponent i c d).val) :=
    (torus_commute _ _ _ _).pow_right _
  have hbase : Commute (rootBase i) (kernelT i ^ (kernelExponent i c d).val) :=
    (RootData.rootBase_kernel_commute i).pow_right _
  calc
    rightConj (rootBase i) (sectionT i a *
        (kernelT i ^ (kernelExponent i c d).val * sectionT i (weightValue i c d).succ)) =
      rightConj (rootBase i) (kernelT i ^ (kernelExponent i c d).val *
        (sectionT i a * sectionT i (weightValue i c d).succ)) := by
          rw [← mul_assoc, hc.eq, mul_assoc]
    _ = rightConj (rootBase i) (sectionT i a * sectionT i (weightValue i c d).succ) := by
      rw [rightConj_mul, (rightConj_fixed_iff _ _).mpr hbase]
    _ = rightConj (rootBase i) (sectionT i (parameterAction i c d a)) := by
      rw [sectionT_mul i ha (Fin.succ_ne_zero _)]
      rfl

theorem rightConj_mem_U_torus {g : G} (hg : g ∈ U) (c d : Fin 7) :
    rightConj g (torus c d) ∈ U := by
  apply Collection.rightConj_mem_closure_of_generators _ U (torus c d) ?_ hg
  rintro _ ⟨curve, hcurve, a, rfl⟩
  simp only [roots, List.mem_cons, List.not_mem_nil, or_false] at hcurve
  rcases hcurve with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change rightConj (root _ a) (torus c d) ∈ U
    rw [root_conj_torus]
    exact root_mem_U _ _

theorem H_le_normalizer_U : H ≤ Subgroup.normalizer (U : Set G) := by
  intro h hh
  obtain ⟨c,d,rfl⟩ := exists_torus_of_mem_H hh
  rw [Subgroup.mem_normalizer_iff'']
  intro g
  constructor
  · intro hg
    exact rightConj_mem_U_torus hg c d
  · intro hg
    have hi := rightConj_mem_U_torus hg (indexInv c) (indexInv d)
    change rightConj (rightConj g (torus c d)) (torus (indexInv c) (indexInv d)) ∈ U at hi
    rw [← torus_inv, rightConj_inv_cancel] at hi
    exact hi

end Kourovka.Problem2153.RootSystem

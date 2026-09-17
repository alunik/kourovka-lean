import Kourovka.Problem2153.TorusAction
import Kourovka.Problem2153.RankOne.Basic
import Mathlib.Tactic.Group

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace Kourovka.Problem2153.RootSystem.RankOne

/-- The positive roots permuted by the first simple reflection. The two
negative images are unused and guarded by explicit exclusions below. -/
def rIndex : Fin 12 → Fin 12 := ![5, 1, 4, 3, 2, 0, 6, 10, 9, 8, 7, 11]

/-- The positive roots permuted by the second simple reflection. -/
def sIndex : Fin 12 → Fin 12 := ![0, 2, 1, 7, 6, 8, 4, 3, 5, 9, 11, 10]

theorem rIndex_valid : ∀ i : Fin 12, i ≠ 1 → i ≠ 3 → rIndex i ≠ 1 ∧ rIndex i ≠ 3 := by
  decide +kernel

theorem sIndex_valid : ∀ i : Fin 12, i ≠ 0 → sIndex i ≠ 0 := by decide +kernel

theorem section_one : ∀ i : Fin 12, sectionParameters i 1 = (0, 0) := by decide +kernel

theorem root_one (i : Fin 12) : root i 1 = rootBase i := by
  rw [root, if_neg (by decide), section_one]
  simp [torus_zero_zero, rightConj]

theorem root_parameter (i : Fin 12) {a : Fin 8} (ha : a ≠ 0) :
    root i a = rightConj (root i 1) (sectionT i a) := by
  rw [root_one]
  exact if_neg ha

theorem rightConj_transport (a h n : G) :
    rightConj (rightConj a h) n = rightConj (rightConj a n) (rightConj h n) := by
  simp only [rightConj]
  group

theorem r_parameter_transport : ∀ i : Fin 12, i ≠ 1 → i ≠ 3 →
    ∀ a : Fin 8, a ≠ 0 →
      parameterAction (rIndex i) (sectionParameters i a).1
        (indexMul (indexFourth (sectionParameters i a).1)
          (indexInv (sectionParameters i a).2)) 1 = a := by decide +kernel

theorem s_parameter_transport : ∀ i : Fin 12, i ≠ 0 →
    ∀ a : Fin 8, a ≠ 0 →
      parameterAction (sIndex i) (sectionParameters i a).2 (sectionParameters i a).1 1 = a := by
  decide +kernel

/-- A single checked parameter-one identity and the proved torus action imply
the whole root-curve identity. -/
theorem root_conj_r_of_base (i : Fin 12) (hi1 : i ≠ 1) (hi3 : i ≠ 3)
    (hbase : rightConj (root i 1) r = root (rIndex i) 1) (a : Fin 8) :
    rightConj (root i a) r = root (rIndex i) a := by
  by_cases ha : a = 0
  · subst a
    simp [rightConj]
  rw [root_parameter i ha, rightConj_transport, hbase]
  change rightConj (root (rIndex i) 1)
    (rightConj (torus (sectionParameters i a).1 (sectionParameters i a).2) r) = _
  rw [torus_conj_r, root_conj_torus, r_parameter_transport i hi1 hi3 a ha]

theorem root_conj_s_of_base (i : Fin 12) (hi : i ≠ 0)
    (hbase : rightConj (root i 1) s = root (sIndex i) 1) (a : Fin 8) :
    rightConj (root i a) s = root (sIndex i) a := by
  by_cases ha : a = 0
  · subst a
    simp [rightConj]
  rw [root_parameter i ha, rightConj_transport, hbase]
  change rightConj (root (sIndex i) 1)
    (rightConj (torus (sectionParameters i a).1 (sectionParameters i a).2) s) = _
  rw [torus_conj_s, root_conj_torus, s_parameter_transport i hi a ha]

end Kourovka.Problem2153.RootSystem.RankOne

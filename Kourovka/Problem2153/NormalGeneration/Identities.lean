import Kourovka.Problem2153.NormalGeneration.Basic
import Kourovka.Problem2153.NormalGeneration.Certificates
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.NormalGeneration
open RankOne
theorem SuzukiR_identity : suzukiWord [0, 2, 0, 2, 0] = r := by
  have h := SuzukiR_checked
  simpa [suzukiWord, suzukiGenerator, wordGroup, atomGroup, rightConj,
    r_inv, root_one, rootBase, mul_assoc] using h

theorem SuzukiX_identity : suzukiWord [1, 2, 1, 2, 0, 2, 0, 1, 2, 1, 2, 0, 2, 0, 1, 2, 1, 2, 0, 2, 0, 1, 2] = x := by
  have h := SuzukiX_checked
  simpa [suzukiWord, suzukiGenerator, wordGroup, atomGroup, rightConj,
    r_inv, root_one, rootBase, mul_assoc] using h

theorem SuzukiH_identity : suzukiWord [2, 0, 2, 0, 1, 2, 1, 2, 1, 2] = torus 0 1 := by
  have h := SuzukiH_checked
  simpa [suzukiWord, suzukiGenerator, wordGroup, atomGroup, rightConj,
    r_inv, root_one, rootBase, mul_assoc] using h

theorem root_commutator_identity :
    x⁻¹ * (rightConj x (s * r))⁻¹ * x * rightConj x (s * r) = rightConj t r := by
  have hx4 : x ^ 4 = 1 := by
    apply Subtype.ext
    have h := pow_orderOf_eq_one WilsonModel.xUnit
    rw [WilsonModel.order_xUnit] at h
    exact h
  have hxi : x⁻¹ = x * x * x := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_succ, mul_assoc] using hx4
  have hyi : (rightConj x (s * r))⁻¹ =
      rightConj x (s * r) * rightConj x (s * r) * rightConj x (s * r) := by
    simp only [rightConj, mul_inv_rev, inv_inv, hxi]
    group
  rw [hxi, hyi]
  have h := RootComm_checked
  simpa [wordGroup, atomGroup, root_one, rootBase, mul_assoc] using h

theorem sl2_identity : t * rightConj t s * t = s := by
  have h := SL2_checked
  simpa [wordGroup, atomGroup, root_one, rootBase, rightConj, s_inv, mul_assoc] using h

theorem perfect_identity :
    (root 11 6)⁻¹ * (torus 1 0)⁻¹ * root 11 6 * torus 1 0 = root 11 1 := by
  have hs : root 11 6 * root 11 6 = 1 := by
    simpa [wordGroup, atomGroup] using PerfectSquare_checked
  have hi : (root 11 6)⁻¹ = root 11 6 := inv_eq_of_mul_eq_one_right hs
  have h := Perfect_checked
  simpa [wordGroup, atomGroup, hi, torus_inv, indexInv, mul_assoc] using h

end Kourovka.Problem2153.RootSystem.NormalGeneration

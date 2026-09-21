import Kourovka2135.CentralPreimageAction
import Kourovka2135.SuzukiCentralRootClassTwo
import Kourovka2135.CentralPGroupTransfer
import Kourovka2135.SuzukiBruhat

/-! The actual full-root preimage in a central Suzuki cover: torus action,
class two for q>=32, and the transfer inclusion of a central binary kernel
in its derived subgroup. The final fixed-point exclusion is separate. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiCentralPreimage

open SuzukiGeometry SuzukiRootDerivedTorus
open scoped IsMulCommutative

variable {E : Type*} [Group E]
variable (m : ℕ) (pi : E →* G m) (hpi : Function.Surjective pi)
variable (hker : pi.ker ≤ Subgroup.center E)

abbrev P := (root m).comap pi
abbrev projection := CentralPreimageAction.projection pi (root m)

def torusAction : (K m)ˣ →* MulAut (P m pi) :=
  CentralPreimageAction.action pi hpi hker (root m)
    (SuzukiTorusMovingRank.torusHom m) (rootTorusAction m)
    (rootTorusAut_coe m)

theorem torusAction_projection (u : (K m)ˣ) (x : P m pi) :
    projection m pi (torusAction m pi hpi hker u x) =
      rootTorusAut m u (projection m pi x) :=
  CentralPreimageAction.action_projection pi hpi hker (root m)
    (SuzukiTorusMovingRank.torusHom m) (rootTorusAction m) (rootTorusAut_coe m) u x

theorem torusAction_fixes_kernel (u : (K m)ˣ) (x : P m pi)
    (hx : x ∈ (projection m pi).ker) : torusAction m pi hpi hker u x = x :=
  CentralPreimageAction.action_fixes_kernel pi hpi hker (root m)
    (SuzukiTorusMovingRank.torusHom m) (rootTorusAction m) (rootTorusAut_coe m) u x hx

include hpi hker in
/-- Every actual central Suzuki cover has a class-two root preimage for q>=32. -/
theorem commutator_le_center (hm : 2 ≤ m) :
    commutator (P m pi) ≤ Subgroup.center (P m pi) :=
  SuzukiCentralRootClassTwo.commutator_le_center m hm (projection m pi)
    (CentralPreimageAction.projection_surjective pi hpi (root m))
    (CentralPreimageAction.projection_kernel_central pi hker (root m))
    (torusAction m pi hpi hker) (torusAction_projection m pi hpi hker)
    (torusAction_fixes_kernel m pi hpi hker)

/-- The full root subgroup has the exact odd index needed by transfer. -/
theorem root_index (m : ℕ) : (root m).index = (q m - 1) * ((q m) ^ 2 + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (lt_trans Nat.zero_lt_one (one_lt_q m)) 2)
  calc
    (q m) ^ 2 * (root m).index = Nat.card (G m) := by
      rw [← card_root]
      exact (root m).card_mul_index
    _ = (q m) ^ 2 * ((q m - 1) * ((q m) ^ 2 + 1)) := by rw [card_group]; ring

theorem root_index_odd (m : ℕ) : Odd (root m).index := by
  rw [root_index]
  have hq : Odd (q m - 1) := Nat.Even.sub_odd (Nat.le_of_lt (one_lt_q m)) (even_q m) (by decide)
  exact hq.mul (((even_q m).pow_of_ne_zero (by decide : 2 ≠ 0)).add_one)

include hpi in
theorem preimage_index_odd : Odd (P m pi).index := by
  change Odd ((root m).comap pi).index
  rw [(root m).index_comap_of_surjective hpi]
  exact root_index_odd m

include hpi hker in
/-- Perfectness and transfer put the whole actual central binary kernel
inside the derived subgroup of the root preimage, without a kernel-size bound. -/
theorem kernel_le_commutator_map [Finite E] [Group.IsPerfect E]
    (hbinary : IsPGroup 2 pi.ker) :
    pi.ker ≤ (commutator (P m pi)).map (P m pi).subtype :=
  CentralPGroupTransfer.binary_le_commutator_map_of_odd_index pi.ker hbinary hker
    (P m pi) (preimage_index_odd m pi hpi)

end Kourovka2135.SuzukiCentralPreimage

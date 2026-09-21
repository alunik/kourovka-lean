import Kourovka2135.SLTwoUnipotent
import Kourovka2135.DerivedCentralization

/-! Finite certificates for persistent commutator inputs in SL2(F5).
Every listed target comes with actual inputs and short words expressing
both elementary generators. Python only produces the data; ordinary Lean
decision proofs check all matrix equalities and memberships. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Kourovka2135.SLTwoFiveGoodSetData
open Matrix
open scoped MatrixGroups

abbrev S := SL(2, ZMod 5)
def upper : S := ⟨!![1, 1; 0, 1], by decide⟩
def lower : S := ⟨!![1, 0; 1, 1], by decide⟩

def letter (a b : S) : Fin 4 → S := ![a, b, a⁻¹, b⁻¹]
def eval (a b : S) : List (Fin 4) → S
  | [] => 1
  | k :: w => letter a b k * eval a b w

structure Witness where
  target : S
  left : S
  right : S
  upperWord : List (Fin 4)
  lowerWord : List (Fin 4)

def witness : Fin 44 → Witness :=
![
    ⟨⟨!![0, 1; 4, 1], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![2, 3; 2, 1], by decide⟩, [0, 3, 3, 2], [1, 2, 1]⟩,
    ⟨⟨!![0, 1; 4, 3], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![4, 1; 0, 4], by decide⟩, [1, 1, 1, 1], [0, 0, 0, 0]⟩,
    ⟨⟨!![0, 2; 2, 1], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![2, 1; 1, 1], by decide⟩, [1, 2, 2], [0, 0]⟩,
    ⟨⟨!![0, 2; 2, 3], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![4, 2; 0, 4], by decide⟩, [1, 1], [2, 2]⟩,
    ⟨⟨!![0, 3; 3, 1], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![2, 4; 4, 1], by decide⟩, [0, 0, 3], [2, 2]⟩,
    ⟨⟨!![0, 3; 3, 3], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![4, 3; 0, 4], by decide⟩, [3, 3], [0, 0]⟩,
    ⟨⟨!![0, 4; 1, 1], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![2, 2; 3, 1], by decide⟩, [0, 1, 1, 2], [3, 0, 3]⟩,
    ⟨⟨!![0, 4; 1, 3], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![4, 4; 0, 4], by decide⟩, [3, 3, 3, 3], [2, 2, 2, 2]⟩,
    ⟨⟨!![1, 1; 1, 2], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![0, 1; 4, 3], by decide⟩, [1, 2, 1, 1, 1], [0, 0, 0, 0]⟩,
    ⟨⟨!![1, 1; 4, 0], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![0, 3; 3, 3], by decide⟩, [2, 1, 1], [1, 2, 1]⟩,
    ⟨⟨!![1, 2; 2, 0], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![0, 1; 4, 3], by decide⟩, [3, 2, 2, 1], [0, 0]⟩,
    ⟨⟨!![1, 2; 3, 2], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![0, 2; 2, 3], by decide⟩, [2, 1, 1, 0], [2, 2]⟩,
    ⟨⟨!![1, 3; 2, 2], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![0, 3; 3, 3], by decide⟩, [2, 3, 3, 0], [0, 0]⟩,
    ⟨⟨!![1, 3; 3, 0], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![0, 4; 1, 3], by decide⟩, [3, 0, 0, 1], [2, 2]⟩,
    ⟨⟨!![1, 4; 1, 0], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![0, 2; 2, 3], by decide⟩, [3, 3, 0], [3, 0, 3]⟩,
    ⟨⟨!![1, 4; 4, 2], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![0, 4; 1, 3], by decide⟩, [0, 3, 0, 0, 0], [2, 2, 2, 2]⟩,
    ⟨⟨!![2, 1; 1, 1], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![1, 1; 1, 2], by decide⟩, [0, 3, 3, 3, 3], [0, 0, 0, 0]⟩,
    ⟨⟨!![2, 1; 2, 4], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![3, 3; 3, 0], by decide⟩, [1, 1, 2], [1, 2, 1]⟩,
    ⟨⟨!![2, 2; 1, 4], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![3, 1; 4, 0], by decide⟩, [1, 2, 2, 3], [0, 0]⟩,
    ⟨⟨!![2, 2; 3, 1], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![1, 2; 3, 2], by decide⟩, [3, 2, 3, 2], [2, 2]⟩,
    ⟨⟨!![2, 3; 2, 1], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![1, 3; 2, 2], by decide⟩, [0, 1, 0, 1], [0, 0]⟩,
    ⟨⟨!![2, 3; 4, 4], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![3, 4; 1, 0], by decide⟩, [1, 0, 0, 3], [2, 2]⟩,
    ⟨⟨!![2, 4; 3, 4], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![3, 2; 2, 0], by decide⟩, [0, 3, 3], [3, 0, 3]⟩,
    ⟨⟨!![2, 4; 4, 1], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![1, 4; 4, 2], by decide⟩, [1, 1, 1, 1, 2], [2, 2, 2, 2]⟩,
    ⟨⟨!![3, 1; 3, 3], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![1, 3; 2, 2], by decide⟩, [2, 3, 3, 0], [1, 2, 1]⟩,
    ⟨⟨!![3, 1; 4, 0], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![2, 1; 1, 1], by decide⟩, [1, 2, 2, 2, 2], [0, 0, 0, 0]⟩,
    ⟨⟨!![3, 2; 2, 0], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![2, 2; 3, 1], by decide⟩, [2, 3, 2, 3], [2, 2]⟩,
    ⟨⟨!![3, 2; 4, 3], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![1, 1; 1, 2], by decide⟩, [2, 2, 1], [0, 0]⟩,
    ⟨⟨!![3, 3; 1, 3], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![1, 4; 4, 2], by decide⟩, [3, 0, 0], [2, 2]⟩,
    ⟨⟨!![3, 3; 3, 0], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![2, 3; 2, 1], by decide⟩, [1, 0, 1, 0], [0, 0]⟩,
    ⟨⟨!![3, 4; 1, 0], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![2, 4; 4, 1], by decide⟩, [0, 0, 0, 0, 3], [2, 2, 2, 2]⟩,
    ⟨⟨!![3, 4; 2, 3], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![1, 2; 3, 2], by decide⟩, [2, 1, 1, 0], [3, 0, 3]⟩,
    ⟨⟨!![4, 0; 1, 4], by decide⟩, ⟨!![4, 1; 0, 4], by decide⟩, ⟨!![0, 4; 1, 3], by decide⟩, [0, 0, 0, 0], [1, 1, 1, 2, 1]⟩,
    ⟨⟨!![4, 0; 2, 4], by decide⟩, ⟨!![4, 3; 0, 4], by decide⟩, ⟨!![0, 2; 2, 3], by decide⟩, [2, 2], [0, 1, 1, 2]⟩,
    ⟨⟨!![4, 0; 3, 4], by decide⟩, ⟨!![4, 2; 0, 4], by decide⟩, ⟨!![0, 3; 3, 3], by decide⟩, [0, 0], [0, 3, 3, 2]⟩,
    ⟨⟨!![4, 0; 4, 4], by decide⟩, ⟨!![4, 4; 0, 4], by decide⟩, ⟨!![0, 1; 4, 3], by decide⟩, [2, 2, 2, 2], [0, 0, 0, 3, 0]⟩,
    ⟨⟨!![4, 1; 0, 4], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![3, 1; 4, 0], by decide⟩, [1, 1, 1, 2, 1], [0, 0, 0, 0]⟩,
    ⟨⟨!![4, 1; 2, 2], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![4, 3; 0, 4], by decide⟩, [3, 3], [1, 2, 1]⟩,
    ⟨⟨!![4, 2; 0, 4], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![3, 2; 2, 0], by decide⟩, [0, 1, 1, 2], [2, 2]⟩,
    ⟨⟨!![4, 2; 1, 2], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![4, 1; 0, 4], by decide⟩, [2, 1, 2], [0, 0]⟩,
    ⟨⟨!![4, 3; 0, 4], by decide⟩, ⟨!![4, 0; 2, 4], by decide⟩, ⟨!![3, 3; 3, 0], by decide⟩, [0, 3, 3, 2], [0, 0]⟩,
    ⟨⟨!![4, 3; 4, 2], by decide⟩, ⟨!![4, 0; 3, 4], by decide⟩, ⟨!![4, 4; 0, 4], by decide⟩, [0, 3, 0], [2, 2]⟩,
    ⟨⟨!![4, 4; 0, 4], by decide⟩, ⟨!![4, 0; 4, 4], by decide⟩, ⟨!![3, 4; 1, 0], by decide⟩, [0, 0, 0, 3, 0], [2, 2, 2, 2]⟩,
    ⟨⟨!![4, 4; 3, 2], by decide⟩, ⟨!![4, 0; 1, 4], by decide⟩, ⟨!![4, 2; 0, 4], by decide⟩, [1, 1], [3, 0, 3]⟩]

def targets : Finset S := Finset.univ.image (fun i => (witness i).target)

theorem targets_card : targets.card = 44 := by decide

/-- Every finite row carries genuine input membership and generator words. -/
theorem all_witnesses : ∀ i : Fin 44,
    (witness i).left ∈ targets ∧ (witness i).right ∈ targets ∧
    paperCommutator (witness i).left (witness i).right = (witness i).target ∧
    eval (witness i).left (witness i).right (witness i).upperWord = upper ∧
    eval (witness i).left (witness i).right (witness i).lowerWord = lower := by decide

/-- The finite list is exactly the elements of order six or ten, in power-test form. -/
theorem targets_iff_powers : ∀ g : S, g ∈ targets ↔
    (g ^ 6 = 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 2 ≠ 1) ∨
    (g ^ 10 = 1 ∧ g ^ 5 ≠ 1 ∧ g ^ 2 ≠ 1) := by decide

/-- The actual elementary root matrices are powers of the fixed generators. -/
theorem upper_transvection : ∀ c : ZMod 5,
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c =
      upper ^ c.val := by decide

theorem lower_transvection : ∀ c : ZMod 5,
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c =
      lower ^ c.val := by decide

end Kourovka2135.SLTwoFiveGoodSetData

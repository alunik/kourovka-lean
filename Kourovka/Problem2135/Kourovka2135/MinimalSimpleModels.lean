import Kourovka2135.Vendor.CFSG.MatrixGroups.Suzuki
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple

/-!
Concrete models in the minimal-simple classification used by the ordinary proof.
`MinimalSimpleClassification` is an explicit proposition to be supplied as an
assumption under the user's explicit authorization to assume Thompson's
classification of finite minimal simple groups (as well as CFSG). This file
neither proves it nor declares it as an axiom. No commutator, multiplier, module,
or lifting assertion is included in the classification proposition.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped MatrixGroups
open BenderSuzuki.PFAppendixIII BenderSuzuki.MatrixGroups

instance classificationFactPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

def IsMinimalSimpleModel (G : Type u) [Group G] : Prop :=
  (∃ f : ℕ, f.Prime ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
  (∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ Nonempty (G ≃* PSL(2, GaloisField 3 f))) ∨
  (∃ (ell : ℕ) (hp : ell.Prime), 3 < ell ∧ 5 ∣ ell ^ 2 + 1 ∧
    (letI : Fact ell.Prime := ⟨hp⟩
     Nonempty (G ≃* PSL(2, GaloisField ell 1)))) ∨
  (∃ m : ℕ, 0 < m ∧ (2 * m + 1).Prime ∧ Nonempty (G ≃* SuzukiMatrixGroup m)) ∨
  Nonempty (G ≃* PSL(3, ZMod 3))

/-- The exact classification statement needed after the minimal-simple reduction.
This is an assumption interface, not a theorem that classification has been proved. -/
def MinimalSimpleClassification : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    ¬ IsMulCommutative G →
    (∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) → IsMinimalSimpleModel G

end Kourovka2135

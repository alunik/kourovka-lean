import Kourovka2135.GeneratingGoodClass
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases

/-!
Concrete order-eight and order-thirteen generating good classes in SL(3,3).
The producer exports matrices and short words; every determinant, elementary
product, conjugacy identity and commutator identity is checked by ordinary
`decide`. Generation follows from mathlib's diagonal/transvection induction.
No GAP result or group-recognition assertion is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Kourovka2135.SL33Witnesses
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
abbrev S := SL(3, ZMod 3)

theorem inv_two : (2 : ZMod 3)⁻¹ = 2 := inv_eq_of_mul_eq_one_left (by decide)

theorem diag_one (i j : Fin 3) (hij : i ≠ j) (hc : (1 : ZMod 3) ≠ 0) :
    diag2n hij (1 : ZMod 3) hc = 1 := by
  apply Subtype.ext
  change diagonal (fun k : Fin 3 => if k = i then (1 : ZMod 3) else
    if k = j then (1 : ZMod 3)⁻¹ else 1) = 1
  simp

theorem diag_two_swap (i j : Fin 3) (hij : i ≠ j) (hc : (2 : ZMod 3) ≠ 0) :
    diag2n hij (2 : ZMod 3) hc = diag2n hij.symm (2 : ZMod 3) hc := by
  apply Subtype.ext
  change diagonal (fun k : Fin 3 => if k = i then (2 : ZMod 3) else
    if k = j then (2 : ZMod 3)⁻¹ else 1) =
    diagonal (fun k : Fin 3 => if k = j then (2 : ZMod 3) else
      if k = i then (2 : ZMod 3)⁻¹ else 1)
  simp only [inv_two]
  congr 1
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [hi, hj]

def certMatrix0 : S := ⟨!![1, 1, 2; 1, 0, 0; 1, 1, 1], by decide⟩
def certMatrix1 : S := ⟨!![2, 2, 1; 1, 0, 2; 1, 1, 0], by decide⟩
def certMatrix2 : S := ⟨!![1, 0, 2; 0, 1, 0; 0, 0, 1], by decide⟩
def certMatrix3 : S := ⟨!![2, 2, 0; 0, 1, 0; 0, 2, 2], by decide⟩
def certMatrix4 : S := ⟨!![0, 1, 0; 2, 2, 2; 1, 0, 2], by decide⟩
def certMatrix5 : S := ⟨!![1, 0, 2; 2, 0, 0; 1, 1, 1], by decide⟩
def certMatrix6 : S := ⟨!![2, 1, 1; 0, 2, 0; 0, 0, 1], by decide⟩
def certMatrix7 : S := ⟨!![0, 1, 1; 1, 1, 1; 1, 0, 2], by decide⟩
def certMatrix8 : S := ⟨!![2, 1, 2; 1, 0, 0; 1, 1, 1], by decide⟩
def certMatrix9 : S := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩
def certMatrix10 : S := ⟨!![2, 0, 0; 1, 1, 1; 1, 0, 2], by decide⟩
def certMatrix11 : S := ⟨!![2, 2, 1; 0, 2, 0; 0, 0, 1], by decide⟩
def certMatrix12 : S := ⟨!![1, 0, 0; 1, 1, 0; 1, 0, 1], by decide⟩
def certMatrix13 : S := ⟨!![1, 1, 1; 0, 0, 1; 2, 1, 2], by decide⟩
def certMatrix14 : S := ⟨!![0, 0, 1; 1, 0, 2; 1, 1, 0], by decide⟩
def certMatrix15 : S := ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩
def certMatrix16 : S := ⟨!![2, 0, 2; 0, 0, 1; 2, 1, 2], by decide⟩
def certMatrix17 : S := ⟨!![1, 1, 0; 1, 1, 1; 2, 1, 0], by decide⟩
def certMatrix18 : S := ⟨!![0, 0, 1; 1, 0, 2; 1, 1, 2], by decide⟩
def certMatrix19 : S := ⟨!![1, 1, 1; 0, 0, 1; 1, 0, 1], by decide⟩
def certMatrix20 : S := ⟨!![1, 0, 0; 1, 1, 0; 0, 0, 1], by decide⟩
def certMatrix21 : S := ⟨!![1, 1, 2; 2, 1, 2; 2, 2, 0], by decide⟩
def certMatrix22 : S := ⟨!![1, 0, 1; 2, 1, 0; 1, 2, 1], by decide⟩
def certMatrix23 : S := ⟨!![0, 0, 1; 2, 1, 1; 2, 0, 2], by decide⟩
def certMatrix24 : S := ⟨!![1, 1, 0; 0, 2, 1; 0, 0, 2], by decide⟩
def certMatrix25 : S := ⟨!![0, 2, 0; 0, 1, 1; 2, 2, 0], by decide⟩
def certMatrix26 : S := ⟨!![1, 1, 1; 0, 2, 1; 1, 0, 1], by decide⟩
def certMatrix27 : S := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩
def certMatrix28 : S := ⟨!![1, 1, 0; 1, 1, 1; 0, 2, 0], by decide⟩
def certMatrix29 : S := ⟨!![2, 0, 2; 0, 0, 1; 1, 1, 1], by decide⟩
def certMatrix30 : S := ⟨!![2, 2, 1; 1, 0, 2; 0, 0, 1], by decide⟩
def certMatrix31 : S := ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide⟩
def certMatrix32 : S := ⟨!![1, 1, 1; 2, 2, 0; 1, 0, 1], by decide⟩
def certMatrix33 : S := ⟨!![1, 0, 2; 0, 0, 2; 2, 1, 2], by decide⟩
def certMatrix34 : S := ⟨!![0, 1, 0; 2, 0, 2; 0, 1, 1], by decide⟩
def certMatrix35 : S := ⟨!![1, 0, 0; 1, 1, 0; 2, 1, 1], by decide⟩
def certMatrix36 : S := ⟨!![2, 2, 1; 0, 2, 0; 0, 2, 1], by decide⟩
def certMatrix37 : S := ⟨!![2, 0, 0; 1, 1, 1; 2, 1, 0], by decide⟩
def certMatrix38 : S := ⟨!![1, 1, 2; 1, 0, 0; 2, 1, 1], by decide⟩
def certMatrix39 : S := ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by decide⟩
def certMatrix40 : S := ⟨!![0, 1, 0; 2, 0, 2; 1, 1, 2], by decide⟩
def certMatrix41 : S := ⟨!![2, 2, 2; 2, 2, 1; 1, 0, 0], by decide⟩
def certMatrix42 : S := ⟨!![2, 0, 1; 1, 0, 0; 1, 1, 1], by decide⟩
def certMatrix43 : S := ⟨!![0, 2, 0; 1, 1, 1; 1, 0, 2], by decide⟩
def certMatrix44 : S := ⟨!![2, 0, 0; 0, 2, 0; 0, 0, 1], by decide⟩
def certMatrix45 : S := ⟨!![1, 0, 1; 1, 1, 2; 0, 2, 0], by decide⟩
def certMatrix46 : S := ⟨!![2, 1, 2; 2, 0, 0; 1, 1, 0], by decide⟩
def certMatrix47 : S := ⟨!![0, 1, 1; 2, 2, 2; 0, 0, 1], by decide⟩
def certMatrix48 : S := ⟨!![2, 1, 1; 0, 1, 0; 1, 1, 1], by decide⟩
def certMatrix49 : S := ⟨!![2, 1, 0; 2, 2, 0; 1, 0, 2], by decide⟩
def certMatrix50 : S := ⟨!![1, 1, 2; 0, 0, 2; 0, 1, 0], by decide⟩
def certMatrix51 : S := ⟨!![1, 0, 1; 2, 2, 2; 1, 0, 0], by decide⟩
def certMatrix52 : S := ⟨!![2, 1, 2; 2, 0, 1; 1, 1, 1], by decide⟩
def certMatrix53 : S := ⟨!![2, 1, 0; 0, 0, 2; 0, 2, 0], by decide⟩
def certMatrix54 : S := ⟨!![0, 2, 1; 2, 2, 2; 2, 0, 0], by decide⟩
def certMatrix55 : S := ⟨!![0, 1, 1; 2, 0, 0; 1, 1, 2], by decide⟩
def certMatrix56 : S := ⟨!![0, 2, 1; 0, 2, 0; 1, 0, 0], by decide⟩
def certMatrix57 : S := ⟨!![2, 1, 0; 1, 1, 1; 0, 1, 0], by decide⟩
def certMatrix58 : S := ⟨!![1, 1, 2; 1, 0, 2; 2, 2, 0], by decide⟩
def certMatrix59 : S := ⟨!![2, 0, 0; 0, 1, 0; 0, 0, 2], by decide⟩
def certMatrix60 : S := ⟨!![1, 1, 0; 0, 2, 0; 2, 0, 2], by decide⟩
def certMatrix61 : S := ⟨!![0, 0, 1; 1, 1, 0; 1, 2, 1], by decide⟩
def certMatrix62 : S := ⟨!![1, 1, 1; 2, 1, 2; 1, 2, 0], by decide⟩
def certMatrix63 : S := ⟨!![1, 0, 2; 0, 1, 1; 2, 2, 1], by decide⟩
def certMatrix64 : S := ⟨!![2, 1, 1; 0, 2, 1; 2, 0, 0], by decide⟩
def certMatrix65 : S := ⟨!![2, 1, 0; 2, 1, 1; 2, 2, 2], by decide⟩
def certMatrix66 : S := ⟨!![1, 1, 2; 2, 1, 0; 2, 0, 1], by decide⟩
def certMatrix67 : S := ⟨!![1, 0, 1; 0, 2, 1; 0, 0, 2], by decide⟩
def certMatrix68 : S := ⟨!![0, 0, 1; 0, 1, 1; 2, 2, 0], by decide⟩
def certMatrix69 : S := ⟨!![1, 0, 2; 0, 2, 1; 1, 0, 1], by decide⟩
def certMatrix70 : S := ⟨!![2, 1, 1; 2, 1, 0; 1, 1, 2], by decide⟩
def certMatrix71 : S := ⟨!![2, 1, 0; 1, 1, 2; 2, 0, 0], by decide⟩
def certMatrix72 : S := ⟨!![1, 1, 2; 2, 0, 0; 2, 2, 2], by decide⟩
def certMatrix73 : S := ⟨!![1, 0, 0; 0, 2, 0; 0, 0, 2], by decide⟩
def certMatrix74 : S := ⟨!![2, 2, 0; 1, 0, 1; 2, 0, 0], by decide⟩
def certMatrix75 : S := ⟨!![1, 2, 1; 2, 2, 0; 2, 2, 1], by decide⟩
def certMatrix76 : S := ⟨!![1, 2, 0; 1, 2, 1; 2, 0, 2], by decide⟩
def certMatrix77 : S := ⟨!![0, 1, 2; 1, 2, 0; 1, 1, 0], by decide⟩
def certMatrix78 : S := ⟨!![0, 2, 2; 0, 1, 2; 2, 1, 2], by decide⟩
def certMatrix79 : S := ⟨!![1, 2, 2; 0, 2, 2; 2, 1, 0], by decide⟩
def certMatrix80 : S := ⟨!![2, 0, 1; 1, 2, 2; 0, 2, 1], by decide⟩
def certMatrix81 : S := ⟨!![0, 0, 2; 2, 0, 1; 0, 1, 1], by decide⟩
def certMatrix82 : S := ⟨!![2, 2, 2; 0, 0, 2; 2, 1, 1], by decide⟩
def certMatrix83 : S := ⟨!![2, 1, 1; 0, 0, 1; 0, 1, 2], by decide⟩
def certMatrix84 : S := ⟨!![1, 2, 0; 1, 1, 2; 0, 0, 2], by decide⟩
def certMatrix85 : S := ⟨!![2, 0, 1; 2, 0, 2; 2, 1, 1], by decide⟩
def certMatrix86 : S := ⟨!![1, 2, 2; 2, 0, 1; 1, 0, 1], by decide⟩
def certMatrix87 : S := ⟨!![2, 2, 1; 0, 1, 1; 0, 1, 0], by decide⟩
def certMatrix88 : S := ⟨!![0, 2, 0; 1, 2, 0; 1, 2, 1], by decide⟩
def certMatrix89 : S := ⟨!![0, 0, 2; 2, 1, 0; 2, 2, 2], by decide⟩
def certMatrix90 : S := ⟨!![0, 2, 1; 1, 2, 0; 1, 1, 2], by decide⟩
def certMatrix91 : S := ⟨!![2, 2, 0; 0, 1, 1; 2, 0, 0], by decide⟩
def certMatrix92 : S := ⟨!![1, 0, 1; 0, 2, 1; 1, 1, 2], by decide⟩
def certMatrix93 : S := ⟨!![1, 2, 2; 2, 2, 0; 2, 0, 0], by decide⟩
def certMatrix94 : S := ⟨!![2, 0, 0; 1, 0, 1; 1, 1, 2], by decide⟩
def certMatrix95 : S := ⟨!![2, 1, 0; 1, 2, 2; 2, 0, 0], by decide⟩
def certMatrix96 : S := ⟨!![1, 2, 0; 2, 0, 0; 1, 1, 2], by decide⟩
def certMatrix97 : S := ⟨!![1, 0, 0; 1, 1, 2; 0, 1, 0], by decide⟩
def certMatrix98 : S := ⟨!![2, 1, 1; 2, 0, 0; 0, 0, 1], by decide⟩
def certMatrix99 : S := ⟨!![2, 0, 2; 1, 1, 2; 0, 0, 2], by decide⟩
def certMatrix100 : S := ⟨!![2, 2, 1; 1, 2, 1; 0, 0, 2], by decide⟩
def certMatrix101 : S := ⟨!![0, 2, 0; 1, 0, 2; 0, 0, 1], by decide⟩
def certMatrix102 : S := ⟨!![0, 0, 2; 2, 0, 2; 0, 1, 2], by decide⟩
def certMatrix103 : S := ⟨!![0, 0, 1; 1, 1, 0; 1, 2, 2], by decide⟩
def certMatrix104 : S := ⟨!![0, 1, 0; 2, 0, 2; 2, 0, 0], by decide⟩
def certMatrix105 : S := ⟨!![0, 1, 1; 1, 0, 2; 1, 1, 2], by decide⟩
def certMatrix106 : S := ⟨!![1, 1, 1; 1, 2, 1; 2, 0, 0], by decide⟩
def certMatrix107 : S := ⟨!![2, 2, 1; 2, 2, 2; 1, 2, 2], by decide⟩
def certMatrix108 : S := ⟨!![0, 2, 0; 0, 2, 2; 1, 0, 1], by decide⟩
def certMatrix109 : S := ⟨!![2, 1, 2; 2, 1, 0; 2, 2, 0], by decide⟩
def certMatrix110 : S := ⟨!![1, 1, 1; 1, 2, 0; 1, 2, 1], by decide⟩
def certMatrix111 : S := ⟨!![2, 0, 1; 0, 1, 1; 0, 1, 0], by decide⟩
def certMatrix112 : S := ⟨!![1, 0, 2; 0, 1, 2; 0, 2, 2], by decide⟩
def certMatrix113 : S := ⟨!![1, 2, 1; 1, 1, 0; 2, 2, 2], by decide⟩
def certMatrix114 : S := ⟨!![0, 1, 0; 2, 0, 2; 1, 0, 2], by decide⟩
def certMatrix115 : S := ⟨!![0, 0, 1; 1, 1, 0; 2, 0, 2], by decide⟩
def certMatrix116 : S := ⟨!![0, 0, 2; 0, 1, 2; 1, 1, 0], by decide⟩
def certMatrix117 : S := ⟨!![0, 2, 1; 0, 2, 2; 2, 1, 2], by decide⟩
def certMatrix118 : S := ⟨!![0, 1, 1; 0, 2, 0; 1, 1, 1], by decide⟩
def certMatrix119 : S := ⟨!![1, 2, 0; 2, 1, 2; 0, 1, 1], by decide⟩
def certMatrix120 : S := ⟨!![2, 1, 0; 1, 1, 0; 0, 2, 1], by decide⟩
def certMatrix121 : S := ⟨!![1, 2, 0; 2, 0, 2; 0, 0, 2], by decide⟩
def certMatrix122 : S := ⟨!![1, 0, 0; 2, 2, 2; 0, 2, 1], by decide⟩
def certMatrix123 : S := ⟨!![2, 1, 1; 1, 1, 2; 0, 1, 1], by decide⟩
def certMatrix124 : S := ⟨!![2, 0, 2; 0, 1, 0; 1, 2, 0], by decide⟩
def certMatrix125 : S := ⟨!![1, 0, 2; 0, 1, 1; 2, 1, 0], by decide⟩
def certMatrix126 : S := ⟨!![2, 1, 1; 0, 2, 1; 1, 2, 0], by decide⟩
def certMatrix127 : S := ⟨!![2, 0, 2; 2, 1, 1; 1, 0, 0], by decide⟩
def certMatrix128 : S := ⟨!![1, 1, 0; 1, 0, 2; 2, 1, 1], by decide⟩
def certMatrix129 : S := ⟨!![2, 1, 2; 2, 0, 2; 1, 0, 2], by decide⟩
def certMatrix130 : S := ⟨!![0, 2, 0; 2, 1, 1; 1, 2, 1], by decide⟩
def certMatrix131 : S := ⟨!![2, 2, 1; 0, 2, 1; 0, 1, 0], by decide⟩
def certMatrix132 : S := ⟨!![2, 1, 0; 2, 0, 0; 0, 2, 1], by decide⟩
def certMatrix133 : S := ⟨!![0, 2, 2; 2, 1, 0; 2, 2, 0], by decide⟩
def certMatrix134 : S := ⟨!![2, 2, 2; 0, 2, 2; 1, 0, 1], by decide⟩
def certMatrix135 : S := ⟨!![1, 2, 1; 0, 1, 2; 2, 0, 1], by decide⟩
def certMatrix136 : S := ⟨!![2, 2, 0; 0, 0, 1; 1, 2, 2], by decide⟩
def certMatrix137 : S := ⟨!![0, 2, 1; 0, 0, 2; 1, 0, 1], by decide⟩
def certMatrix138 : S := ⟨!![2, 1, 1; 0, 0, 1; 2, 2, 0], by decide⟩
def certMatrix139 : S := ⟨!![0, 0, 2; 2, 0, 2; 2, 1, 1], by decide⟩
def certMatrix140 : S := ⟨!![0, 2, 0; 1, 0, 2; 1, 0, 0], by decide⟩
def certMatrix141 : S := ⟨!![2, 2, 1; 1, 2, 1; 1, 2, 0], by decide⟩
def certMatrix142 : S := ⟨!![1, 1, 1; 2, 2, 0; 0, 2, 0], by decide⟩
def certMatrix143 : S := ⟨!![2, 0, 1; 1, 0, 1; 2, 2, 1], by decide⟩
def certMatrix144 : S := ⟨!![1, 0, 1; 2, 2, 0; 1, 0, 0], by decide⟩
def certMatrix145 : S := ⟨!![2, 2, 0; 1, 2, 1; 2, 1, 1], by decide⟩
def certMatrix146 : S := ⟨!![1, 0, 1; 0, 1, 0; 0, 2, 1], by decide⟩
def certMatrix147 : S := ⟨!![1, 2, 2; 1, 1, 2; 2, 2, 0], by decide⟩
def certMatrix148 : S := ⟨!![0, 1, 2; 2, 0, 0; 1, 0, 1], by decide⟩
def certMatrix149 : S := ⟨!![0, 0, 1; 1, 1, 2; 2, 0, 1], by decide⟩
def certMatrix150 : S := ⟨!![0, 1, 0; 2, 2, 2; 1, 2, 2], by decide⟩
def certMatrix151 : S := ⟨!![1, 2, 1; 0, 2, 2; 1, 0, 1], by decide⟩
def certMatrix152 : S := ⟨!![2, 2, 0; 0, 1, 2; 2, 0, 1], by decide⟩
def certMatrix153 : S := ⟨!![1, 0, 1; 0, 0, 1; 1, 2, 2], by decide⟩
def certMatrix154 : S := ⟨!![1, 2, 2; 0, 0, 2; 0, 1, 2], by decide⟩
def certMatrix155 : S := ⟨!![1, 2, 0; 2, 2, 2; 0, 1, 0], by decide⟩
def certMatrix156 : S := ⟨!![2, 1, 0; 1, 1, 2; 0, 0, 1], by decide⟩
def certMatrix157 : S := ⟨!![2, 0, 1; 0, 1, 1; 0, 0, 2], by decide⟩
def certMatrix158 : S := ⟨!![1, 1, 1; 1, 2, 0; 0, 0, 1], by decide⟩
def certMatrix159 : S := ⟨!![0, 1, 1; 1, 0, 0; 0, 0, 2], by decide⟩
def certMatrix160 : S := ⟨!![1, 2, 0; 2, 2, 1; 0, 0, 1], by decide⟩
def certMatrix161 : S := ⟨!![2, 0, 2; 0, 2, 2; 0, 2, 0], by decide⟩
def certMatrix162 : S := ⟨!![1, 1, 0; 0, 2, 0; 0, 0, 2], by decide⟩
def certMatrix163 : S := ⟨!![2, 1, 2; 0, 0, 2; 0, 2, 1], by decide⟩
def certMatrix164 : S := ⟨!![1, 1, 1; 0, 2, 1; 0, 1, 1], by decide⟩

def a13 : S := certMatrix0

def b13 : S := certMatrix1

def s13 : S := certMatrix2

def t13 : S := certMatrix3

theorem tr13_01_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (0 : Fin 3) ≠ 1) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix4 ∈ H := by
    have he : (1 : S) * a13⁻¹ = certMatrix4 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem ha)

  have h2 : certMatrix5 ∈ H := by
    have he : certMatrix4 * b13 = certMatrix5 := by decide
    exact he ▸ H.mul_mem h1 hb

  have h3 : certMatrix6 ∈ H := by
    have he : certMatrix5 * a13⁻¹ = certMatrix6 := by decide
    exact he ▸ H.mul_mem h2 (H.inv_mem ha)

  have h4 : certMatrix7 ∈ H := by
    have he : certMatrix6 * a13⁻¹ = certMatrix7 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem ha)

  have h5 : certMatrix8 ∈ H := by
    have he : certMatrix7 * b13 = certMatrix8 := by decide
    exact he ▸ H.mul_mem h4 hb

  have h6 : certMatrix9 ∈ H := by
    have he : certMatrix8 * a13⁻¹ = certMatrix9 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have hf : transvection (by decide : (0 : Fin 3) ≠ 1) (1 : ZMod 3) = certMatrix9 := by decide
  exact hf.symm ▸ h6

theorem tr13_02_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (0 : Fin 3) ≠ 2) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix10 ∈ H := by
    have he : certMatrix0 * b13⁻¹ = certMatrix10 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix11 ∈ H := by
    have he : certMatrix10 * a13 = certMatrix11 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix12 ∈ H := by
    have he : certMatrix11 * b13⁻¹ = certMatrix12 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix13 ∈ H := by
    have he : certMatrix12 * b13⁻¹ = certMatrix13 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem hb)

  have h6 : certMatrix14 ∈ H := by
    have he : certMatrix13 * a13⁻¹ = certMatrix14 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix15 ∈ H := by
    have he : certMatrix14 * b13⁻¹ = certMatrix15 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have hf : transvection (by decide : (0 : Fin 3) ≠ 2) (1 : ZMod 3) = certMatrix15 := by decide
  exact hf.symm ▸ h7

theorem tr13_10_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (1 : Fin 3) ≠ 0) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix1 ∈ H := by
    have he : (1 : S) * b13 = certMatrix1 := by decide
    exact he ▸ H.mul_mem h0 hb

  have h2 : certMatrix16 ∈ H := by
    have he : certMatrix1 * a13 = certMatrix16 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix17 ∈ H := by
    have he : certMatrix16 * a13 = certMatrix17 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix18 ∈ H := by
    have he : certMatrix17 * b13⁻¹ = certMatrix18 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix19 ∈ H := by
    have he : certMatrix18 * a13 = certMatrix19 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix20 ∈ H := by
    have he : certMatrix19 * b13 = certMatrix20 := by decide
    exact he ▸ H.mul_mem h5 hb

  have hf : transvection (by decide : (1 : Fin 3) ≠ 0) (1 : ZMod 3) = certMatrix20 := by decide
  exact hf.symm ▸ h6

theorem tr13_12_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (1 : Fin 3) ≠ 2) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix10 ∈ H := by
    have he : certMatrix0 * b13⁻¹ = certMatrix10 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix11 ∈ H := by
    have he : certMatrix10 * a13 = certMatrix11 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix12 ∈ H := by
    have he : certMatrix11 * b13⁻¹ = certMatrix12 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix21 ∈ H := by
    have he : certMatrix12 * a13 = certMatrix21 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix22 ∈ H := by
    have he : certMatrix21 * a13 = certMatrix22 := by decide
    exact he ▸ H.mul_mem h5 ha

  have h7 : certMatrix23 ∈ H := by
    have he : certMatrix22 * b13 = certMatrix23 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix24 ∈ H := by
    have he : certMatrix23 * b13 = certMatrix24 := by decide
    exact he ▸ H.mul_mem h7 hb

  have h9 : certMatrix25 ∈ H := by
    have he : certMatrix24 * b13 = certMatrix25 := by decide
    exact he ▸ H.mul_mem h8 hb

  have h10 : certMatrix26 ∈ H := by
    have he : certMatrix25 * a13⁻¹ = certMatrix26 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem ha)

  have h11 : certMatrix27 ∈ H := by
    have he : certMatrix26 * b13 = certMatrix27 := by decide
    exact he ▸ H.mul_mem h10 hb

  have hf : transvection (by decide : (1 : Fin 3) ≠ 2) (1 : ZMod 3) = certMatrix27 := by decide
  exact hf.symm ▸ h11

theorem tr13_20_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (2 : Fin 3) ≠ 0) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix10 ∈ H := by
    have he : certMatrix0 * b13⁻¹ = certMatrix10 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix11 ∈ H := by
    have he : certMatrix10 * a13 = certMatrix11 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix12 ∈ H := by
    have he : certMatrix11 * b13⁻¹ = certMatrix12 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix13 ∈ H := by
    have he : certMatrix12 * b13⁻¹ = certMatrix13 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem hb)

  have h6 : certMatrix14 ∈ H := by
    have he : certMatrix13 * a13⁻¹ = certMatrix14 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix28 ∈ H := by
    have he : certMatrix14 * b13 = certMatrix28 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix29 ∈ H := by
    have he : certMatrix28 * a13⁻¹ = certMatrix29 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem ha)

  have h9 : certMatrix30 ∈ H := by
    have he : certMatrix29 * a13⁻¹ = certMatrix30 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem ha)

  have h10 : certMatrix31 ∈ H := by
    have he : certMatrix30 * b13⁻¹ = certMatrix31 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem hb)

  have hf : transvection (by decide : (2 : Fin 3) ≠ 0) (1 : ZMod 3) = certMatrix31 := by decide
  exact hf.symm ▸ h10

theorem tr13_21_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    transvection (by decide : (2 : Fin 3) ≠ 1) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix32 ∈ H := by
    have he : (1 : S) * b13⁻¹ = certMatrix32 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix33 ∈ H := by
    have he : certMatrix32 * b13⁻¹ = certMatrix33 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix34 ∈ H := by
    have he : certMatrix33 * b13⁻¹ = certMatrix34 := by decide
    exact he ▸ H.mul_mem h2 (H.inv_mem hb)

  have h4 : certMatrix35 ∈ H := by
    have he : certMatrix34 * a13 = certMatrix35 := by decide
    exact he ▸ H.mul_mem h3 ha

  have h5 : certMatrix36 ∈ H := by
    have he : certMatrix35 * b13 = certMatrix36 := by decide
    exact he ▸ H.mul_mem h4 hb

  have h6 : certMatrix37 ∈ H := by
    have he : certMatrix36 * a13⁻¹ = certMatrix37 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix38 ∈ H := by
    have he : certMatrix37 * b13 = certMatrix38 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix39 ∈ H := by
    have he : certMatrix38 * a13⁻¹ = certMatrix39 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem ha)

  have hf : transvection (by decide : (2 : Fin 3) ≠ 1) (1 : ZMod 3) = certMatrix39 := by decide
  exact hf.symm ▸ h8

theorem dg13_01_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    diag2n (by decide : (0 : Fin 3) ≠ 1) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix10 ∈ H := by
    have he : certMatrix0 * b13⁻¹ = certMatrix10 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix11 ∈ H := by
    have he : certMatrix10 * a13 = certMatrix11 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix12 ∈ H := by
    have he : certMatrix11 * b13⁻¹ = certMatrix12 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix40 ∈ H := by
    have he : certMatrix12 * a13⁻¹ = certMatrix40 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem ha)

  have h6 : certMatrix41 ∈ H := by
    have he : certMatrix40 * a13⁻¹ = certMatrix41 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix42 ∈ H := by
    have he : certMatrix41 * b13⁻¹ = certMatrix42 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix43 ∈ H := by
    have he : certMatrix42 * b13⁻¹ = certMatrix43 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem hb)

  have h9 : certMatrix44 ∈ H := by
    have he : certMatrix43 * a13 = certMatrix44 := by decide
    exact he ▸ H.mul_mem h8 ha

  have hf : diag2n (by decide : (0 : Fin 3) ≠ 1) (2 : ZMod 3) (by decide) = certMatrix44 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 0 then (2 : ZMod 3) else
      if k = 1 then (2 : ZMod 3)⁻¹ else 1) = !![2, 0, 0; 0, 2, 0; 0, 0, 1]
    rw [inv_two]
    decide
  exact hf.symm ▸ h9

theorem dg13_02_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    diag2n (by decide : (0 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix45 ∈ H := by
    have he : certMatrix0 * a13 = certMatrix45 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix46 ∈ H := by
    have he : certMatrix45 * b13⁻¹ = certMatrix46 := by decide
    exact he ▸ H.mul_mem h2 (H.inv_mem hb)

  have h4 : certMatrix47 ∈ H := by
    have he : certMatrix46 * b13⁻¹ = certMatrix47 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix48 ∈ H := by
    have he : certMatrix47 * a13 = certMatrix48 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix49 ∈ H := by
    have he : certMatrix48 * b13⁻¹ = certMatrix49 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem hb)

  have h7 : certMatrix50 ∈ H := by
    have he : certMatrix49 * b13⁻¹ = certMatrix50 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix51 ∈ H := by
    have he : certMatrix50 * a13 = certMatrix51 := by decide
    exact he ▸ H.mul_mem h7 ha

  have h9 : certMatrix52 ∈ H := by
    have he : certMatrix51 * b13⁻¹ = certMatrix52 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have h10 : certMatrix53 ∈ H := by
    have he : certMatrix52 * a13 = certMatrix53 := by decide
    exact he ▸ H.mul_mem h9 ha

  have h11 : certMatrix54 ∈ H := by
    have he : certMatrix53 * a13 = certMatrix54 := by decide
    exact he ▸ H.mul_mem h10 ha

  have h12 : certMatrix55 ∈ H := by
    have he : certMatrix54 * b13 = certMatrix55 := by decide
    exact he ▸ H.mul_mem h11 hb

  have h13 : certMatrix56 ∈ H := by
    have he : certMatrix55 * a13⁻¹ = certMatrix56 := by decide
    exact he ▸ H.mul_mem h12 (H.inv_mem ha)

  have h14 : certMatrix57 ∈ H := by
    have he : certMatrix56 * a13⁻¹ = certMatrix57 := by decide
    exact he ▸ H.mul_mem h13 (H.inv_mem ha)

  have h15 : certMatrix58 ∈ H := by
    have he : certMatrix57 * b13⁻¹ = certMatrix58 := by decide
    exact he ▸ H.mul_mem h14 (H.inv_mem hb)

  have h16 : certMatrix59 ∈ H := by
    have he : certMatrix58 * b13⁻¹ = certMatrix59 := by decide
    exact he ▸ H.mul_mem h15 (H.inv_mem hb)

  have hf : diag2n (by decide : (0 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) = certMatrix59 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 0 then (2 : ZMod 3) else
      if k = 2 then (2 : ZMod 3)⁻¹ else 1) = !![2, 0, 0; 0, 1, 0; 0, 0, 2]
    rw [inv_two]
    decide
  exact hf.symm ▸ h16

theorem dg13_12_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H) :
    diag2n (by decide : (1 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix0 ∈ H := by
    have he : (1 : S) * a13 = certMatrix0 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix45 ∈ H := by
    have he : certMatrix0 * a13 = certMatrix45 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix46 ∈ H := by
    have he : certMatrix45 * b13⁻¹ = certMatrix46 := by decide
    exact he ▸ H.mul_mem h2 (H.inv_mem hb)

  have h4 : certMatrix60 ∈ H := by
    have he : certMatrix46 * a13⁻¹ = certMatrix60 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem ha)

  have h5 : certMatrix61 ∈ H := by
    have he : certMatrix60 * b13⁻¹ = certMatrix61 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem hb)

  have h6 : certMatrix62 ∈ H := by
    have he : certMatrix61 * a13 = certMatrix62 := by decide
    exact he ▸ H.mul_mem h5 ha

  have h7 : certMatrix63 ∈ H := by
    have he : certMatrix62 * b13⁻¹ = certMatrix63 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix64 ∈ H := by
    have he : certMatrix63 * a13⁻¹ = certMatrix64 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem ha)

  have h9 : certMatrix65 ∈ H := by
    have he : certMatrix64 * b13⁻¹ = certMatrix65 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have h10 : certMatrix66 ∈ H := by
    have he : certMatrix65 * b13⁻¹ = certMatrix66 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem hb)

  have h11 : certMatrix67 ∈ H := by
    have he : certMatrix66 * a13 = certMatrix67 := by decide
    exact he ▸ H.mul_mem h10 ha

  have h12 : certMatrix68 ∈ H := by
    have he : certMatrix67 * b13 = certMatrix68 := by decide
    exact he ▸ H.mul_mem h11 hb

  have h13 : certMatrix69 ∈ H := by
    have he : certMatrix68 * a13⁻¹ = certMatrix69 := by decide
    exact he ▸ H.mul_mem h12 (H.inv_mem ha)

  have h14 : certMatrix70 ∈ H := by
    have he : certMatrix69 * a13⁻¹ = certMatrix70 := by decide
    exact he ▸ H.mul_mem h13 (H.inv_mem ha)

  have h15 : certMatrix71 ∈ H := by
    have he : certMatrix70 * b13⁻¹ = certMatrix71 := by decide
    exact he ▸ H.mul_mem h14 (H.inv_mem hb)

  have h16 : certMatrix72 ∈ H := by
    have he : certMatrix71 * b13⁻¹ = certMatrix72 := by decide
    exact he ▸ H.mul_mem h15 (H.inv_mem hb)

  have h17 : certMatrix73 ∈ H := by
    have he : certMatrix72 * a13⁻¹ = certMatrix73 := by decide
    exact he ▸ H.mul_mem h16 (H.inv_mem ha)

  have hf : diag2n (by decide : (1 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) = certMatrix73 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 1 then (2 : ZMod 3) else
      if k = 2 then (2 : ZMod 3)⁻¹ else 1) = !![1, 0, 0; 0, 2, 0; 0, 0, 2]
    rw [inv_two]
    decide
  exact hf.symm ▸ h17

theorem all_transvections13_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3) : transvection hij c ∈ H := by
  have h1 : transvection hij (1 : ZMod 3) ∈ H := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact tr13_01_mem H ha hb | exact tr13_02_mem H ha hb | exact tr13_10_mem H ha hb | exact tr13_12_mem H ha hb | exact tr13_20_mem H ha hb | exact tr13_21_mem H ha hb
  have hc_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases hc_cases c with rfl | rfl | rfl
  · simpa only [transvection_coeff_zero] using H.one_mem
  · exact h1
  · have he : transvection hij (2 : ZMod 3) = transvection hij 1 * transvection hij 1 := by
      rw [← transvection_add]
      congr 1
    rw [he]
    exact H.mul_mem h1 h1

theorem all_diagonals13_mem (H : Subgroup S) (ha : a13 ∈ H) (hb : b13 ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3) (hc : c ≠ 0) : diag2n hij c hc ∈ H := by
  have hc_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases hc_cases c with rfl | rfl | rfl
  · exact (hc rfl).elim
  · rw [diag_one]
    exact H.one_mem
  · fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact dg13_01_mem H ha hb | exact dg13_02_mem H ha hb | exact dg13_12_mem H ha hb | (rw [diag_two_swap]; first | exact dg13_01_mem H ha hb | exact dg13_02_mem H ha hb | exact dg13_12_mem H ha hb)

theorem generating13 : Subgroup.closure ({a13, b13} : Set S) = ⊤ := by
  apply top_le_iff.mp
  intro g _
  let H := Subgroup.closure ({a13, b13} : Set S)
  have ha : a13 ∈ H := Subgroup.subset_closure (by simp)
  have hb : b13 ∈ H := Subgroup.subset_closure (by simp)
  apply diagonal_transvection_induction' (fun g => g ∈ H) g
  · exact fun i j hij _ hc => all_diagonals13_mem H ha hb i j hij _ hc
  · exact all_transvections13_mem H ha hb
  · exact fun _ _ => H.mul_mem

theorem conjugate13 : s13⁻¹ * a13 * s13 = b13 := by decide
theorem commutator13 : paperCommutator a13 b13 = t13⁻¹ * a13 * t13 := by decide
theorem goodClass13 : IsGeneratingGoodSet (conjugatesOf a13) := by
  apply isGeneratingGoodSet_conjugatesOf_of_certificate a13 s13 t13
  · rw [conjugate13, commutator13]
  · rw [conjugate13, generating13]

theorem power13 : a13 ^ 13 = 1 := by
  have h1 : a13 ^ 1 = certMatrix0 := by simp only [pow_one]; rfl

  have h2 : a13 ^ 2 = certMatrix45 := by
    calc
      a13 ^ 2 = a13 ^ 1 * a13 := pow_succ _ _
      _ = certMatrix45 := by rw [h1]; decide

  have h3 : a13 ^ 3 = certMatrix74 := by
    calc
      a13 ^ 3 = a13 ^ 2 * a13 := pow_succ _ _
      _ = certMatrix74 := by rw [h2]; decide

  have h4 : a13 ^ 4 = certMatrix75 := by
    calc
      a13 ^ 4 = a13 ^ 3 * a13 := pow_succ _ _
      _ = certMatrix75 := by rw [h3]; decide

  have h5 : a13 ^ 5 = certMatrix76 := by
    calc
      a13 ^ 5 = a13 ^ 4 * a13 := pow_succ _ _
      _ = certMatrix76 := by rw [h4]; decide

  have h6 : a13 ^ 6 = certMatrix77 := by
    calc
      a13 ^ 6 = a13 ^ 5 * a13 := pow_succ _ _
      _ = certMatrix77 := by rw [h5]; decide

  have h7 : a13 ^ 7 = certMatrix78 := by
    calc
      a13 ^ 7 = a13 ^ 6 * a13 := pow_succ _ _
      _ = certMatrix78 := by rw [h6]; decide

  have h8 : a13 ^ 8 = certMatrix79 := by
    calc
      a13 ^ 8 = a13 ^ 7 * a13 := pow_succ _ _
      _ = certMatrix79 := by rw [h7]; decide

  have h9 : a13 ^ 9 = certMatrix80 := by
    calc
      a13 ^ 9 = a13 ^ 8 * a13 := pow_succ _ _
      _ = certMatrix80 := by rw [h8]; decide

  have h10 : a13 ^ 10 = certMatrix81 := by
    calc
      a13 ^ 10 = a13 ^ 9 * a13 := pow_succ _ _
      _ = certMatrix81 := by rw [h9]; decide

  have h11 : a13 ^ 11 = certMatrix82 := by
    calc
      a13 ^ 11 = a13 ^ 10 * a13 := pow_succ _ _
      _ = certMatrix82 := by rw [h10]; decide

  have h12 : a13 ^ 12 = certMatrix4 := by
    calc
      a13 ^ 12 = a13 ^ 11 * a13 := pow_succ _ _
      _ = certMatrix4 := by rw [h11]; decide

  have h13 : a13 ^ 13 = 1 := by
    calc
      a13 ^ 13 = a13 ^ 12 * a13 := pow_succ _ _
      _ = 1 := by rw [h12]; decide

  exact h13

theorem order13 : orderOf a13 = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  exact orderOf_eq_prime power13 (by decide : a13 ≠ 1)

def a8 : S := certMatrix83

def b8 : S := certMatrix84

def s8 : S := certMatrix85

def t8 : S := certMatrix86

theorem tr8_01_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (0 : Fin 3) ≠ 1) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix87 ∈ H := by
    have he : (1 : S) * a8⁻¹ = certMatrix87 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem ha)

  have h2 : certMatrix88 ∈ H := by
    have he : certMatrix87 * b8⁻¹ = certMatrix88 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix89 ∈ H := by
    have he : certMatrix88 * a8 = certMatrix89 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix90 ∈ H := by
    have he : certMatrix89 * a8 = certMatrix90 := by decide
    exact he ▸ H.mul_mem h3 ha

  have h5 : certMatrix91 ∈ H := by
    have he : certMatrix90 * b8 = certMatrix91 := by decide
    exact he ▸ H.mul_mem h4 hb

  have h6 : certMatrix92 ∈ H := by
    have he : certMatrix91 * a8⁻¹ = certMatrix92 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix93 ∈ H := by
    have he : certMatrix92 * b8 = certMatrix93 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix94 ∈ H := by
    have he : certMatrix93 * a8⁻¹ = certMatrix94 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem ha)

  have h9 : certMatrix95 ∈ H := by
    have he : certMatrix94 * b8 = certMatrix95 := by decide
    exact he ▸ H.mul_mem h8 hb

  have h10 : certMatrix96 ∈ H := by
    have he : certMatrix95 * a8⁻¹ = certMatrix96 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem ha)

  have h11 : certMatrix97 ∈ H := by
    have he : certMatrix96 * b8⁻¹ = certMatrix97 := by decide
    exact he ▸ H.mul_mem h10 (H.inv_mem hb)

  have h12 : certMatrix98 ∈ H := by
    have he : certMatrix97 * a8 = certMatrix98 := by decide
    exact he ▸ H.mul_mem h11 ha

  have h13 : certMatrix99 ∈ H := by
    have he : certMatrix98 * b8⁻¹ = certMatrix99 := by decide
    exact he ▸ H.mul_mem h12 (H.inv_mem hb)

  have h14 : certMatrix9 ∈ H := by
    have he : certMatrix99 * b8⁻¹ = certMatrix9 := by decide
    exact he ▸ H.mul_mem h13 (H.inv_mem hb)

  have hf : transvection (by decide : (0 : Fin 3) ≠ 1) (1 : ZMod 3) = certMatrix9 := by decide
  exact hf.symm ▸ h14

theorem tr8_02_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (0 : Fin 3) ≠ 2) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix100 ∈ H := by
    have he : (1 : S) * b8⁻¹ = certMatrix100 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix101 ∈ H := by
    have he : certMatrix100 * b8⁻¹ = certMatrix101 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix102 ∈ H := by
    have he : certMatrix101 * a8 = certMatrix102 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix103 ∈ H := by
    have he : certMatrix102 * b8⁻¹ = certMatrix103 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix104 ∈ H := by
    have he : certMatrix103 * a8⁻¹ = certMatrix104 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem ha)

  have h6 : certMatrix105 ∈ H := by
    have he : certMatrix104 * a8⁻¹ = certMatrix105 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix106 ∈ H := by
    have he : certMatrix105 * b8 = certMatrix106 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix107 ∈ H := by
    have he : certMatrix106 * a8 = certMatrix107 := by decide
    exact he ▸ H.mul_mem h7 ha

  have h9 : certMatrix108 ∈ H := by
    have he : certMatrix107 * b8⁻¹ = certMatrix108 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have h10 : certMatrix109 ∈ H := by
    have he : certMatrix108 * b8⁻¹ = certMatrix109 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem hb)

  have h11 : certMatrix110 ∈ H := by
    have he : certMatrix109 * a8 = certMatrix110 := by decide
    exact he ▸ H.mul_mem h10 ha

  have h12 : certMatrix111 ∈ H := by
    have he : certMatrix110 * b8 = certMatrix111 := by decide
    exact he ▸ H.mul_mem h11 hb

  have h13 : certMatrix15 ∈ H := by
    have he : certMatrix111 * a8 = certMatrix15 := by decide
    exact he ▸ H.mul_mem h12 ha

  have hf : transvection (by decide : (0 : Fin 3) ≠ 2) (1 : ZMod 3) = certMatrix15 := by decide
  exact hf.symm ▸ h13

theorem tr8_10_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (1 : Fin 3) ≠ 0) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix83 ∈ H := by
    have he : (1 : S) * a8 = certMatrix83 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix112 ∈ H := by
    have he : certMatrix83 * a8 = certMatrix112 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix113 ∈ H := by
    have he : certMatrix112 * b8 = certMatrix113 := by decide
    exact he ▸ H.mul_mem h2 hb

  have h4 : certMatrix114 ∈ H := by
    have he : certMatrix113 * b8 = certMatrix114 := by decide
    exact he ▸ H.mul_mem h3 hb

  have h5 : certMatrix115 ∈ H := by
    have he : certMatrix114 * a8 = certMatrix115 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix116 ∈ H := by
    have he : certMatrix115 * b8⁻¹ = certMatrix116 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem hb)

  have h7 : certMatrix117 ∈ H := by
    have he : certMatrix116 * a8 = certMatrix117 := by decide
    exact he ▸ H.mul_mem h6 ha

  have h8 : certMatrix118 ∈ H := by
    have he : certMatrix117 * a8 = certMatrix118 := by decide
    exact he ▸ H.mul_mem h7 ha

  have h9 : certMatrix119 ∈ H := by
    have he : certMatrix118 * b8⁻¹ = certMatrix119 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have h10 : certMatrix120 ∈ H := by
    have he : certMatrix119 * a8⁻¹ = certMatrix120 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem ha)

  have h11 : certMatrix121 ∈ H := by
    have he : certMatrix120 * a8⁻¹ = certMatrix121 := by decide
    exact he ▸ H.mul_mem h10 (H.inv_mem ha)

  have h12 : certMatrix20 ∈ H := by
    have he : certMatrix121 * b8⁻¹ = certMatrix20 := by decide
    exact he ▸ H.mul_mem h11 (H.inv_mem hb)

  have hf : transvection (by decide : (1 : Fin 3) ≠ 0) (1 : ZMod 3) = certMatrix20 := by decide
  exact hf.symm ▸ h12

theorem tr8_12_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (1 : Fin 3) ≠ 2) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix100 ∈ H := by
    have he : (1 : S) * b8⁻¹ = certMatrix100 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix122 ∈ H := by
    have he : certMatrix100 * a8 = certMatrix122 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix123 ∈ H := by
    have he : certMatrix122 * a8 = certMatrix123 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix124 ∈ H := by
    have he : certMatrix123 * b8⁻¹ = certMatrix124 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix125 ∈ H := by
    have he : certMatrix124 * a8⁻¹ = certMatrix125 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem ha)

  have h6 : certMatrix126 ∈ H := by
    have he : certMatrix125 * a8⁻¹ = certMatrix126 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix127 ∈ H := by
    have he : certMatrix126 * b8⁻¹ = certMatrix127 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix128 ∈ H := by
    have he : certMatrix127 * a8 = certMatrix128 := by decide
    exact he ▸ H.mul_mem h7 ha

  have h9 : certMatrix129 ∈ H := by
    have he : certMatrix128 * a8 = certMatrix129 := by decide
    exact he ▸ H.mul_mem h8 ha

  have h10 : certMatrix130 ∈ H := by
    have he : certMatrix129 * b8 = certMatrix130 := by decide
    exact he ▸ H.mul_mem h9 hb

  have h11 : certMatrix131 ∈ H := by
    have he : certMatrix130 * b8 = certMatrix131 := by decide
    exact he ▸ H.mul_mem h10 hb

  have h12 : certMatrix27 ∈ H := by
    have he : certMatrix131 * a8 = certMatrix27 := by decide
    exact he ▸ H.mul_mem h11 ha

  have hf : transvection (by decide : (1 : Fin 3) ≠ 2) (1 : ZMod 3) = certMatrix27 := by decide
  exact hf.symm ▸ h12

theorem tr8_20_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (2 : Fin 3) ≠ 0) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix84 ∈ H := by
    have he : (1 : S) * b8 = certMatrix84 := by decide
    exact he ▸ H.mul_mem h0 hb

  have h2 : certMatrix132 ∈ H := by
    have he : certMatrix84 * a8 = certMatrix132 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix133 ∈ H := by
    have he : certMatrix132 * b8 = certMatrix133 := by decide
    exact he ▸ H.mul_mem h2 hb

  have h4 : certMatrix134 ∈ H := by
    have he : certMatrix133 * b8 = certMatrix134 := by decide
    exact he ▸ H.mul_mem h3 hb

  have h5 : certMatrix135 ∈ H := by
    have he : certMatrix134 * a8⁻¹ = certMatrix135 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem ha)

  have h6 : certMatrix136 ∈ H := by
    have he : certMatrix135 * a8⁻¹ = certMatrix136 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix137 ∈ H := by
    have he : certMatrix136 * b8⁻¹ = certMatrix137 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix138 ∈ H := by
    have he : certMatrix137 * b8⁻¹ = certMatrix138 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem hb)

  have h9 : certMatrix31 ∈ H := by
    have he : certMatrix138 * a8⁻¹ = certMatrix31 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem ha)

  have hf : transvection (by decide : (2 : Fin 3) ≠ 0) (1 : ZMod 3) = certMatrix31 := by decide
  exact hf.symm ▸ h9

theorem tr8_21_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    transvection (by decide : (2 : Fin 3) ≠ 1) (1 : ZMod 3) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix83 ∈ H := by
    have he : (1 : S) * a8 = certMatrix83 := by decide
    exact he ▸ H.mul_mem h0 ha

  have h2 : certMatrix112 ∈ H := by
    have he : certMatrix83 * a8 = certMatrix112 := by decide
    exact he ▸ H.mul_mem h1 ha

  have h3 : certMatrix113 ∈ H := by
    have he : certMatrix112 * b8 = certMatrix113 := by decide
    exact he ▸ H.mul_mem h2 hb

  have h4 : certMatrix114 ∈ H := by
    have he : certMatrix113 * b8 = certMatrix114 := by decide
    exact he ▸ H.mul_mem h3 hb

  have h5 : certMatrix115 ∈ H := by
    have he : certMatrix114 * a8 = certMatrix115 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix139 ∈ H := by
    have he : certMatrix115 * b8 = certMatrix139 := by decide
    exact he ▸ H.mul_mem h5 hb

  have h7 : certMatrix140 ∈ H := by
    have he : certMatrix139 * a8⁻¹ = certMatrix140 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem ha)

  have h8 : certMatrix141 ∈ H := by
    have he : certMatrix140 * b8 = certMatrix141 := by decide
    exact he ▸ H.mul_mem h7 hb

  have h9 : certMatrix39 ∈ H := by
    have he : certMatrix141 * b8 = certMatrix39 := by decide
    exact he ▸ H.mul_mem h8 hb

  have hf : transvection (by decide : (2 : Fin 3) ≠ 1) (1 : ZMod 3) = certMatrix39 := by decide
  exact hf.symm ▸ h9

theorem dg8_01_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    diag2n (by decide : (0 : Fin 3) ≠ 1) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix100 ∈ H := by
    have he : (1 : S) * b8⁻¹ = certMatrix100 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix142 ∈ H := by
    have he : certMatrix100 * a8⁻¹ = certMatrix142 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem ha)

  have h3 : certMatrix143 ∈ H := by
    have he : certMatrix142 * b8 = certMatrix143 := by decide
    exact he ▸ H.mul_mem h2 hb

  have h4 : certMatrix144 ∈ H := by
    have he : certMatrix143 * a8 = certMatrix144 := by decide
    exact he ▸ H.mul_mem h3 ha

  have h5 : certMatrix145 ∈ H := by
    have he : certMatrix144 * a8 = certMatrix145 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix146 ∈ H := by
    have he : certMatrix145 * b8 = certMatrix146 := by decide
    exact he ▸ H.mul_mem h5 hb

  have h7 : certMatrix147 ∈ H := by
    have he : certMatrix146 * b8 = certMatrix147 := by decide
    exact he ▸ H.mul_mem h6 hb

  have h8 : certMatrix148 ∈ H := by
    have he : certMatrix147 * b8 = certMatrix148 := by decide
    exact he ▸ H.mul_mem h7 hb

  have h9 : certMatrix149 ∈ H := by
    have he : certMatrix148 * a8⁻¹ = certMatrix149 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem ha)

  have h10 : certMatrix150 ∈ H := by
    have he : certMatrix149 * a8⁻¹ = certMatrix150 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem ha)

  have h11 : certMatrix151 ∈ H := by
    have he : certMatrix150 * b8⁻¹ = certMatrix151 := by decide
    exact he ▸ H.mul_mem h10 (H.inv_mem hb)

  have h12 : certMatrix152 ∈ H := by
    have he : certMatrix151 * a8⁻¹ = certMatrix152 := by decide
    exact he ▸ H.mul_mem h11 (H.inv_mem ha)

  have h13 : certMatrix153 ∈ H := by
    have he : certMatrix152 * a8⁻¹ = certMatrix153 := by decide
    exact he ▸ H.mul_mem h12 (H.inv_mem ha)

  have h14 : certMatrix154 ∈ H := by
    have he : certMatrix153 * b8 = certMatrix154 := by decide
    exact he ▸ H.mul_mem h13 hb

  have h15 : certMatrix44 ∈ H := by
    have he : certMatrix154 * a8⁻¹ = certMatrix44 := by decide
    exact he ▸ H.mul_mem h14 (H.inv_mem ha)

  have hf : diag2n (by decide : (0 : Fin 3) ≠ 1) (2 : ZMod 3) (by decide) = certMatrix44 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 0 then (2 : ZMod 3) else
      if k = 1 then (2 : ZMod 3)⁻¹ else 1) = !![2, 0, 0; 0, 2, 0; 0, 0, 1]
    rw [inv_two]
    decide
  exact hf.symm ▸ h15

theorem dg8_02_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    diag2n (by decide : (0 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix100 ∈ H := by
    have he : (1 : S) * b8⁻¹ = certMatrix100 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix101 ∈ H := by
    have he : certMatrix100 * b8⁻¹ = certMatrix101 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem hb)

  have h3 : certMatrix102 ∈ H := by
    have he : certMatrix101 * a8 = certMatrix102 := by decide
    exact he ▸ H.mul_mem h2 ha

  have h4 : certMatrix103 ∈ H := by
    have he : certMatrix102 * b8⁻¹ = certMatrix103 := by decide
    exact he ▸ H.mul_mem h3 (H.inv_mem hb)

  have h5 : certMatrix104 ∈ H := by
    have he : certMatrix103 * a8⁻¹ = certMatrix104 := by decide
    exact he ▸ H.mul_mem h4 (H.inv_mem ha)

  have h6 : certMatrix105 ∈ H := by
    have he : certMatrix104 * a8⁻¹ = certMatrix105 := by decide
    exact he ▸ H.mul_mem h5 (H.inv_mem ha)

  have h7 : certMatrix155 ∈ H := by
    have he : certMatrix105 * b8⁻¹ = certMatrix155 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem hb)

  have h8 : certMatrix156 ∈ H := by
    have he : certMatrix155 * a8 = certMatrix156 := by decide
    exact he ▸ H.mul_mem h7 ha

  have h9 : certMatrix59 ∈ H := by
    have he : certMatrix156 * b8⁻¹ = certMatrix59 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have hf : diag2n (by decide : (0 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) = certMatrix59 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 0 then (2 : ZMod 3) else
      if k = 2 then (2 : ZMod 3)⁻¹ else 1) = !![2, 0, 0; 0, 1, 0; 0, 0, 2]
    rw [inv_two]
    decide
  exact hf.symm ▸ h9

theorem dg8_12_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H) :
    diag2n (by decide : (1 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) ∈ H := by
  have h0 : (1 : S) ∈ H := H.one_mem

  have h1 : certMatrix100 ∈ H := by
    have he : (1 : S) * b8⁻¹ = certMatrix100 := by decide
    exact he ▸ H.mul_mem h0 (H.inv_mem hb)

  have h2 : certMatrix142 ∈ H := by
    have he : certMatrix100 * a8⁻¹ = certMatrix142 := by decide
    exact he ▸ H.mul_mem h1 (H.inv_mem ha)

  have h3 : certMatrix143 ∈ H := by
    have he : certMatrix142 * b8 = certMatrix143 := by decide
    exact he ▸ H.mul_mem h2 hb

  have h4 : certMatrix144 ∈ H := by
    have he : certMatrix143 * a8 = certMatrix144 := by decide
    exact he ▸ H.mul_mem h3 ha

  have h5 : certMatrix145 ∈ H := by
    have he : certMatrix144 * a8 = certMatrix145 := by decide
    exact he ▸ H.mul_mem h4 ha

  have h6 : certMatrix146 ∈ H := by
    have he : certMatrix145 * b8 = certMatrix146 := by decide
    exact he ▸ H.mul_mem h5 hb

  have h7 : certMatrix157 ∈ H := by
    have he : certMatrix146 * a8⁻¹ = certMatrix157 := by decide
    exact he ▸ H.mul_mem h6 (H.inv_mem ha)

  have h8 : certMatrix158 ∈ H := by
    have he : certMatrix157 * b8⁻¹ = certMatrix158 := by decide
    exact he ▸ H.mul_mem h7 (H.inv_mem hb)

  have h9 : certMatrix159 ∈ H := by
    have he : certMatrix158 * b8⁻¹ = certMatrix159 := by decide
    exact he ▸ H.mul_mem h8 (H.inv_mem hb)

  have h10 : certMatrix160 ∈ H := by
    have he : certMatrix159 * b8⁻¹ = certMatrix160 := by decide
    exact he ▸ H.mul_mem h9 (H.inv_mem hb)

  have h11 : certMatrix73 ∈ H := by
    have he : certMatrix160 * b8⁻¹ = certMatrix73 := by decide
    exact he ▸ H.mul_mem h10 (H.inv_mem hb)

  have hf : diag2n (by decide : (1 : Fin 3) ≠ 2) (2 : ZMod 3) (by decide) = certMatrix73 := by
    apply Subtype.ext
    change diagonal (fun k : Fin 3 => if k = 1 then (2 : ZMod 3) else
      if k = 2 then (2 : ZMod 3)⁻¹ else 1) = !![1, 0, 0; 0, 2, 0; 0, 0, 2]
    rw [inv_two]
    decide
  exact hf.symm ▸ h11

theorem all_transvections8_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3) : transvection hij c ∈ H := by
  have h1 : transvection hij (1 : ZMod 3) ∈ H := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact tr8_01_mem H ha hb | exact tr8_02_mem H ha hb | exact tr8_10_mem H ha hb | exact tr8_12_mem H ha hb | exact tr8_20_mem H ha hb | exact tr8_21_mem H ha hb
  have hc_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases hc_cases c with rfl | rfl | rfl
  · simpa only [transvection_coeff_zero] using H.one_mem
  · exact h1
  · have he : transvection hij (2 : ZMod 3) = transvection hij 1 * transvection hij 1 := by
      rw [← transvection_add]
      congr 1
    rw [he]
    exact H.mul_mem h1 h1

theorem all_diagonals8_mem (H : Subgroup S) (ha : a8 ∈ H) (hb : b8 ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (c : ZMod 3) (hc : c ≠ 0) : diag2n hij c hc ∈ H := by
  have hc_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases hc_cases c with rfl | rfl | rfl
  · exact (hc rfl).elim
  · rw [diag_one]
    exact H.one_mem
  · fin_cases i <;> fin_cases j
    all_goals first | exact (hij rfl).elim | exact dg8_01_mem H ha hb | exact dg8_02_mem H ha hb | exact dg8_12_mem H ha hb | (rw [diag_two_swap]; first | exact dg8_01_mem H ha hb | exact dg8_02_mem H ha hb | exact dg8_12_mem H ha hb)

theorem generating8 : Subgroup.closure ({a8, b8} : Set S) = ⊤ := by
  apply top_le_iff.mp
  intro g _
  let H := Subgroup.closure ({a8, b8} : Set S)
  have ha : a8 ∈ H := Subgroup.subset_closure (by simp)
  have hb : b8 ∈ H := Subgroup.subset_closure (by simp)
  apply diagonal_transvection_induction' (fun g => g ∈ H) g
  · exact fun i j hij _ hc => all_diagonals8_mem H ha hb i j hij _ hc
  · exact all_transvections8_mem H ha hb
  · exact fun _ _ => H.mul_mem

theorem conjugate8 : s8⁻¹ * a8 * s8 = b8 := by decide
theorem commutator8 : paperCommutator a8 b8 = t8⁻¹ * a8 * t8 := by decide
theorem goodClass8 : IsGeneratingGoodSet (conjugatesOf a8) := by
  apply isGeneratingGoodSet_conjugatesOf_of_certificate a8 s8 t8
  · rw [conjugate8, commutator8]
  · rw [conjugate8, generating8]

theorem power8 : a8 ^ 8 = 1 := by
  have h1 : a8 ^ 1 = certMatrix83 := by simp only [pow_one]; rfl

  have h2 : a8 ^ 2 = certMatrix112 := by
    calc
      a8 ^ 2 = a8 ^ 1 * a8 := pow_succ _ _
      _ = certMatrix112 := by rw [h1]; decide

  have h3 : a8 ^ 3 = certMatrix161 := by
    calc
      a8 ^ 3 = a8 ^ 2 * a8 := pow_succ _ _
      _ = certMatrix161 := by rw [h2]; decide

  have h4 : a8 ^ 4 = certMatrix162 := by
    calc
      a8 ^ 4 = a8 ^ 3 * a8 := pow_succ _ _
      _ = certMatrix162 := by rw [h3]; decide

  have h5 : a8 ^ 5 = certMatrix163 := by
    calc
      a8 ^ 5 = a8 ^ 4 * a8 := pow_succ _ _
      _ = certMatrix163 := by rw [h4]; decide

  have h6 : a8 ^ 6 = certMatrix164 := by
    calc
      a8 ^ 6 = a8 ^ 5 * a8 := pow_succ _ _
      _ = certMatrix164 := by rw [h5]; decide

  have h7 : a8 ^ 7 = certMatrix87 := by
    calc
      a8 ^ 7 = a8 ^ 6 * a8 := pow_succ _ _
      _ = certMatrix87 := by rw [h6]; decide

  have h8 : a8 ^ 8 = 1 := by
    calc
      a8 ^ 8 = a8 ^ 7 * a8 := pow_succ _ _
      _ = 1 := by rw [h7]; decide

  exact h8

theorem order8 : orderOf a8 = 8 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    (by decide : a8 ^ 2 ^ 2 ≠ 1) power8

end Kourovka2135.SL33Witnesses

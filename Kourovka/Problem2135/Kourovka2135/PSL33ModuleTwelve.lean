import Kourovka2135.SL33ProjectiveData
import Kourovka2135.PermutationDeletedCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Equiv.Fin.Basic

/-! The actual twelve-dimensional binary PSL3(3) module. It is constructed
from the proved projective action, in coordinates modulo the constant line.
The two small certificates identify its genuine left-action operators with
the inverse transposes of the pinned ATLAS right-row matrices.
No irreducibility, character table, presentation or cohomology assertion is
assumed or proved merely by constructing this representation. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.PSL33ModuleTwelve
open SL33ProjectiveData
abbrev k := ZMod 2
abbrev V := Fin 12 → k

/-- The thirteenth point is the distinguished constant-line coordinate. -/
def chart : Fin 13 ≃ Option (Fin 12) := finSuccEquiv' (Fin.last 12)

def optionPermutation : Q →* Equiv.Perm (Option (Fin 12)) where
  toFun g := chart.permCongr (permutation g)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [Equiv.permCongr_apply]

/-- An actual representation of the actual projective group, defined on all elements. -/
def representation : Representation k Q V :=
  (PermutationDeletedCoordinates.representation k (Fin 12)).comp optionPermutation

theorem finrank_eq_twelve : Module.finrank k V = 12 := by simp [V]

def atlasA : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def atlasB : Matrix (Fin 12) (Fin 12) k :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def leftA : Matrix (Fin 12) (Fin 12) k :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

def leftB : Matrix (Fin 12) (Fin 12) k :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

theorem toMatrix_a :
    LinearMap.toMatrix' (representation (PSL33GoodSets.q a)) = leftA := by
  change LinearMap.toMatrix' (PermutationDeletedCoordinates.representation k (Fin 12)
    (chart.permCongr (permutation (PSL33GoodSets.q a)))) = _
  rw [permutation_a]
  ext i j
  change (((chart.permCongr permA).symm (some i)).elim 0 (Pi.single j 1) -
    ((chart.permCongr permA).symm none).elim 0 (Pi.single j 1) : ZMod 2) = leftA i j
  fin_cases i <;> fin_cases j <;> decide

/-- Both inverse equations pin the inverse-transpose convention without an inverse implementation. -/
theorem inverse_transpose_a :
    leftA * atlasA.transpose = 1 ∧ atlasA.transpose * leftA = 1 := by decide

theorem toMatrix_b :
    LinearMap.toMatrix' (representation (PSL33GoodSets.q b)) = leftB := by
  change LinearMap.toMatrix' (PermutationDeletedCoordinates.representation k (Fin 12)
    (chart.permCongr (permutation (PSL33GoodSets.q b)))) = _
  rw [permutation_b]
  ext i j
  change (((chart.permCongr permB).symm (some i)).elim 0 (Pi.single j 1) -
    ((chart.permCongr permB).symm none).elim 0 (Pi.single j 1) : ZMod 2) = leftB i j
  fin_cases i <;> fin_cases j <;> decide

/-- Both inverse equations pin the inverse-transpose convention without an inverse implementation. -/
theorem inverse_transpose_b :
    leftB * atlasB.transpose = 1 ∧ atlasB.transpose * leftB = 1 := by decide

end Kourovka2135.PSL33ModuleTwelve

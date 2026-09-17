import Kourovka.Problem2153.AmbientFacts.Frame.Steps

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.WilsonModel.Frame
open Field8 F8

theorem trace_starts : ∀ j : Fin 27, traces j 0 = basisZero := by decide +kernel

theorem trace_ends_entries : ∀ i j : Fin 26, traces i.castSucc 48 j = frameMatrix i j := by
  intro i
  fin_cases i <;> decide +kernel

theorem trace_ends (i : Fin 26) : traces i.castSucc 48 = frameMatrix i := funext (trace_ends_entries i)

theorem bridge_trace_end : traces 26 48 = bridgeVector := by decide +kernel

theorem frame_alignment : frameMatrix = Sparse.eval frameRows := by decide +kernel

theorem inverse_alignment : frameInverse = Sparse.eval inverseRows := by decide +kernel

theorem frame_mul_inverse : frameMatrix * frameInverse = 1 :=
  Sparse.mul_eq_of_check_alignment frameMatrix frameRows frameInverse 1 frame_alignment (by decide +kernel)

theorem inverse_mul_frame : frameInverse * frameMatrix = 1 :=
  Sparse.mul_eq_of_check_alignment frameInverse inverseRows frameMatrix 1 inverse_alignment (by decide +kernel)

theorem bridge_coordinates_check : Matrix.vecMul bridgeCoordinates frameMatrix = bridgeVector := by decide +kernel

theorem bridge_coordinates_nonzero : ∀ i, bridgeCoordinates i ≠ 0 := by decide +kernel

#print axioms trace_steps
#print axioms frame_mul_inverse
#print axioms inverse_mul_frame
#print axioms bridge_coordinates_check
end Kourovka.Problem2153.WilsonModel.Frame

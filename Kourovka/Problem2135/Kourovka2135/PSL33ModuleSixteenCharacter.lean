import Kourovka2135.PSL33ModuleSixteen
import Kourovka2135.BinaryFieldSixteenEmbedding

/-! An ordinary character value of the actual sixteen-dimensional quotient
representation, with its four distinct Frobenius conjugates. All field
constants below use polynomial-basis bits rather than natural-number casts. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section

namespace Kourovka2135.PSL33ModuleSixteenCharacter
open PSL33ModuleSixteen PSL33SingerSixteenData SL33ProjectiveData

def singer : Q := PSL33GoodSets.q a * PSL33GoodSets.q b

theorem singer_matrix : LinearMap.toMatrix' (representation singer) = leftA * leftB := by
  rw [singer, map_mul, LinearMap.toMatrix'_mul, toMatrix_a, toMatrix_b]

theorem matrix_trace : Matrix.trace (leftA * leftB) = BinaryFieldSixteen.ofBits 13 := by
  decide +kernel

theorem singer_character : representation.character singer = BinaryFieldSixteen.ofBits 13 := by
  change LinearMap.trace k V (representation singer) = _
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 16))]
  change Matrix.trace (LinearMap.toMatrix' (representation singer)) = _
  rw [singer_matrix, matrix_trace]

theorem trace_frobenius_injective :
    Function.Injective (fun i : Fin 4 => (representation.character singer) ^ (2 ^ i.val)) := by
  rw [singer_character]
  decide +kernel

/-- The four representations built from the actual quotient are pairwise
inequivalent over every algebraically closed field of characteristic two. -/
theorem models_pairwise_not_equiv (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] :
    Pairwise fun i j => ¬ Nonempty
      ((RepresentationEmbeddingModel.model (BinaryFieldSixteenEmbedding.embedding L i)
        representation).Equiv
       (RepresentationEmbeddingModel.model (BinaryFieldSixteenEmbedding.embedding L j)
        representation)) :=
  BinaryFieldSixteenEmbedding.models_pairwise_not_equiv L representation singer
    trace_frobenius_injective

end Kourovka2135.PSL33ModuleSixteenCharacter

import Kourovka.Problems.P21_29.Proof.FiniteModel

namespace Kourovka.P21_29

private theorem checked : ∀ k : Fin 64,
      groupElement ⟨128 + k.val, by omega⟩ • regularVector = regularVector →
        128 + k.val = 0 := by
    decide +kernel

theorem regularChunk002 (i : Fin 1152)
    (_hlo : 128 ≤ i.val) (hhi : i.val < 192) :
    groupElement i • regularVector = regularVector → groupElement i = 1 := by
  let k : Fin 64 := ⟨i.val - 128, by omega⟩
  have heq : (⟨128 + k.val, by omega⟩ : Fin 1152) = i := by
    apply Fin.ext
    dsimp [k]
    omega
  intro hg
  have hz := checked k (by simpa only [heq] using hg)
  have hi : i = 0 := by apply Fin.ext; dsimp [k] at hz; omega
  subst i
  apply SemidirectProduct.ext
  · apply Subtype.ext
    funext x
    revert x
    decide +kernel
  · rfl

end Kourovka.P21_29

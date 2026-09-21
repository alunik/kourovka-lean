import Kourovka2135.SuzukiEightPairedPcData
import Kourovka2135.FiniteEightPcMaps

/-! Identify each actual paired normal form with its abstract product inside
the generated cover. Subsequent subgroup-membership proofs use this equality
without recomputing products of pairs of matrices. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiEightPairedPcData
open SuzukiEightPairedGoodSet

theorem form_eq_word (i : Fin 256) :
    form i = FiniteEightPcWords.word (G := E) pc i := by
  apply Subtype.ext
  change formAmbient i = coverGroup.subtype (FiniteEightPcWords.word (G := E) pc i)
  rw [FiniteEightPcWords.word_map]
  exact (formAmbient_eq_word i).trans (congrArg
    (fun a : Fin 8 → Ambient => FiniteEightPcWords.word (G := Ambient) a i)
    (funext fun j => (pc_val j).symm))

end Kourovka2135.SuzukiEightPairedPcData

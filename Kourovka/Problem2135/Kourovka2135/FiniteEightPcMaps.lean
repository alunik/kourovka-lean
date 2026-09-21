import Kourovka2135.FiniteEightPcWords

/-! Homomorphism transport for abstract eight-generator words. Keeping this
calculation abstract avoids expanding concrete matrix group multiplication. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
namespace Kourovka2135.FiniteEightPcWords

theorem word_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (pc : Fin 8 → G) (i : Fin 256) :
    f (word pc i) = word (fun j => f (pc j)) i := by
  fin_cases i <;> simp [word, map_mul]

end Kourovka2135.FiniteEightPcWords

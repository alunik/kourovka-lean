import Kourovka.Problems.P21_03.Proof.GroupRankBound

/-!
# A crude cardinality bound for automorphism groups
-/

namespace Kourovka213

/-- An automorphism of a finite group is determined by its values on a minimum generating set. -/
theorem natCard_mulAut_le_pow_rank (G : Type*) [Group G] [Finite G] :
    Nat.card (MulAut G) ≤ Nat.card G ^ Group.rank G := by
  classical
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec G
  let evaluate : MulAut G → (S → G) := fun f x => f x
  have hevaluate : Function.Injective evaluate := by
    intro f g hfg
    apply MulEquiv.ext
    have hhom : f.toMonoidHom = g.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hSgen
      intro x hx
      exact congrFun hfg ⟨x, hx⟩
    intro x
    change f.toMonoidHom x = g.toMonoidHom x
    rw [hhom]
  calc
    Nat.card (MulAut G) ≤ Nat.card (S → G) := Nat.card_le_card_of_injective evaluate hevaluate
    _ = Nat.card G ^ Group.rank G := by
      rw [Nat.card_fun, ← hScard]
      congr 1
      simp

/-- The same bound with the exponent replaced by `log 2 |G|`. -/
theorem natCard_mulAut_le_pow_log_two (G : Type*) [Group G] [Finite G] :
    Nat.card (MulAut G) ≤ Nat.card G ^ Nat.log 2 (Nat.card G) := by
  refine (natCard_mulAut_le_pow_rank G).trans ?_
  exact Nat.pow_le_pow_right Nat.card_pos (group_rank_le_log_two_natCard G)

end Kourovka213

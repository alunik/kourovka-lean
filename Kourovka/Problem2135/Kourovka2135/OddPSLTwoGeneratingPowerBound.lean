import Kourovka2135.OddPSLTwoGeneratingClassBound
import Kourovka2135.RepresentationMovingPowerBound
import Kourovka2135.BinaryRepresentationCorrection

/-! Generating inputs may be conjugate to arbitrary powers of the output.
Taking a power cannot increase moving rank, so the closed-field bound and
its finite-field descent need no coprimality condition on those powers. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OddPSLTwoGeneratingPowerBound
open OddPSLTwoProjectiveChart RepresentationCohomologyAlternative
open IrreducibleEndCohomology

variable (F : Type) [Field F] [Fintype F] [Group.IsPerfect (Q F)]

theorem alternative (k : Type) [Field k] [CharP k 2] [IsAlgClosed k]
    {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k (Q F) V) [ρ.IsIrreducible]
    (hodd : Odd (Fintype.card F)) (hsize : 17 ≤ Fintype.card F) (a b c : Q F)
    (hgen : Subgroup.closure ({a, b} : Set (Q F)) = ⊤)
    (m n : ℕ) (ha : IsConj a (c ^ m)) (hb : IsConj b (c ^ n)) :
    Alternative ρ c := by
  by_cases hz : Module.finrank k (groupCohomology (Rep.of ρ) 1) = 0
  · exact Or.inl hz
  let : Nontrivial (groupCohomology (Rep.of ρ) 1) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hz)
  have hglobal := PerfectIrreducibleCohomology.invariants_eq_bot_of_nontrivial_H1 ρ
  have hdim := OddPSLTwoGeneratingClassBound.half_field_le_finrank_of_nontrivial_H1 F k ρ hodd
  have hrank := RepresentationMovingPowerBound.finrank_le_twice_moving
    ρ a b c hgen hglobal m n ha hb
  refine Or.inr ⟨OddPSLTwoFirstCohomology.finrank_H1_le_one F k hodd ρ hglobal, ?_⟩
  omega

theorem finite_bound {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) (Q F) V) [ρ.IsIrreducible]
    (hdual : Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ.dual) 1) =
      Module.finrank (ZMod 2) (groupCohomology (Rep.of ρ) 1))
    (hodd : Odd (Fintype.card F)) (hsize : 17 ≤ Fintype.card F) (a b c : Q F)
    (hgen : Subgroup.closure ({a, b} : Set (Q F)) = ⊤)
    (m n : ℕ) (ha : IsConj a (c ^ m)) (hb : IsConj b (c ^ n)) :
    BinaryRepresentationCorrection.Bound ρ c := by
  apply BinaryRepresentationCorrection.of_closed ρ c hdual
  exact alternative F (ClosedField ρ) (extended ρ) hodd hsize a b c hgen m n ha hb

end Kourovka2135.OddPSLTwoGeneratingPowerBound

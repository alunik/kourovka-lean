import Kourovka.Problems.P21_03.Proof.ForestContainer
import Kourovka.Problems.P21_03.Proof.PrimitiveSolvable
import Kourovka.Problems.P21_03.Proof.WreathSupport

/-!
# Degree controlled by moving top blocks in a natural wreath action

A nonidentity element of a primitive soluble top group moves at least half of
the top points.  Each moved top point contributes an entire fibre to the
support of the associated natural wreath permutation.
-/

namespace Kourovka213

universe u v

/-- If the top component of a natural wreath-product element is nontrivial,
then twice its support controls the degree of the imprimitive action. -/
theorem degree_mul_le_two_mul_wreathSupport_of_right_ne_one
    (T F : SolubleAction.{u, v})
    [MulAction.IsPreprimitive T.Actor T.Point]
    (g : PermWreath F.Actor T.Actor T.Point) (hg : g.right ≠ 1) :
    T.degree * F.degree ≤
      2 * (PermWreath.naturalToPerm F.Actor T.Actor T.Point F.Point g).support.card := by
  classical
  let qperm : Equiv.Perm T.Point := MulAction.toPermHom T.Actor T.Point g.right
  have hfixed :=
    primitive_solvable_two_mul_card_fixedBy_le T.Actor T.Point g.right hg
  have hfixedCard :
      Nat.card (MulAction.fixedBy T.Point g.right) = qperm.supportᶜ.card := by
    let e : MulAction.fixedBy T.Point g.right ≃
        {x // x ∈ qperm.supportᶜ} :=
      Equiv.subtypeEquivRight fun x => by
        simp only [MulAction.mem_fixedBy, Finset.mem_compl,
          Equiv.Perm.mem_support, not_not]
        rfl
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    exact Fintype.card_coe qperm.supportᶜ
  have htop : T.degree ≤ 2 * qperm.support.card := by
    rw [hfixedCard, Finset.card_compl] at hfixed
    have hs : qperm.support.card ≤ T.degree := qperm.support.card_le_univ
    simpa [SolubleAction.degree] using (show
      Fintype.card T.Point ≤ 2 * qperm.support.card by omega)
  have hsum :
      qperm.support.card * F.degree ≤
        (PermWreath.naturalToPerm F.Actor T.Actor T.Point F.Point g).support.card := by
    rw [PermWreath.card_support_naturalToPerm_eq_sum]
    calc
      qperm.support.card * F.degree =
          ∑ i : T.Point, if i ∈ qperm.support then F.degree else 0 := by
        rw [← Finset.sum_filter]
        have hfilter :
            Finset.univ.filter (fun i : T.Point ↦ i ∈ qperm.support) =
              qperm.support := by
          ext i
          simp
        rw [hfilter]
        simp
      _ = ∑ i : T.Point, if g.right • i ≠ i then F.degree else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [qperm, Equiv.Perm.mem_support]
        rfl
      _ ≤ ∑ i : T.Point, if g.right • i ≠ i then Fintype.card F.Point
          else (MulAction.toPermHom F.Actor F.Point (g.left i)).support.card := by
        apply Finset.sum_le_sum
        intro i _hi
        by_cases hmove : g.right • i ≠ i
        · simp [hmove, SolubleAction.degree]
        · simp [hmove]
  calc
    T.degree * F.degree ≤ (2 * qperm.support.card) * F.degree :=
      Nat.mul_le_mul_right F.degree htop
    _ = 2 * (qperm.support.card * F.degree) := by ac_rfl
    _ ≤ 2 *
        (PermWreath.naturalToPerm F.Actor T.Actor T.Point F.Point g).support.card :=
      Nat.mul_le_mul_left 2 hsum

end Kourovka213

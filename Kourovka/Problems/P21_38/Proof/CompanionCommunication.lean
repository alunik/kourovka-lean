import Kourovka.Problems.P21_38.Proof.CompanionTrees
import Kourovka.Problems.P21_38.Proof.LeafCommunication

/-!
# Branch communication for the prescribed companion

This is the positive-exponent case of Golan-Polak's finite leaf-chain
argument. Every relation is witnessed in the ordinary generated subgroup.
-/

namespace Kourovka.P21_38

private theorem split_forall₂_append {α β : Type*} {r : α → β → Prop}
    {a b : List α} {c d : List β} (hlen : a.length = c.length)
    (h : List.Forall₂ r (a ++ b) (c ++ d)) :
    List.Forall₂ r a c ∧ List.Forall₂ r b d := by
  have htake := List.forall₂_take a.length h
  have hdrop := List.forall₂_drop a.length h
  rw [List.take_left, hlen, List.take_left] at htake
  rw [List.drop_left, hlen, List.drop_left] at hdrop
  exact ⟨htake, hdrop⟩

/-- The companion branches connect the finite interior leaves and both endpoint rays. -/
theorem companion_leaf_communication
    {H : Subgroup (Equiv.Perm ℚ)} {g : F} {a u v w z : List Bool}
    {L R : List (List Bool)} (hg : g.1 ∈ H)
    (hcomp : List.Forall₂ (HasBranch g.1)
      (CompanionTrees.sourceWords a w z L R) (CompanionTrees.targetWords a w z L R))
    (hu : u ∈ L) (hv0 : v ++ [false] ∈ L) (hv1 : v ++ [true] ∈ L)
    (huv : BranchRelated H u v) (hvw : BranchRelated H v w) :
    BranchRelated H w (w ++ [false]) ∧ BranchRelated H w (w ++ [true]) ∧
    (∀ x ∈ CompanionTrees.baseWords a w z L R, x ≠ a → x ≠ z → BranchRelated H x w) ∧
    (∀ j, BranchRelated H (endpointExit a false j) w) ∧
    (∀ j, BranchRelated H (endpointExit z true j) w) := by
  have hrel := hcomp.imp (fun x y hb => (show BranchRelated H x y from ⟨g.1, hg, hb⟩))
  have hshape : List.Forall₂ (BranchRelated H)
      ((a ++ [false, false]) :: (a ++ [false, true]) ::
        ((a ++ [true]) :: L) ++
          [w ++ [false], w ++ [true, false, false], w ++ [true, false, true, false, false],
            w ++ [true, false, true, false, true], w ++ [true, false, true, true],
            w ++ [true, true]] ++
          (R ++ [z ++ [false]]) ++ [z ++ [true, false], z ++ [true, true]])
      ((a ++ [false]) :: (a ++ [true]) ::
        (L ++ [w ++ [false, false]]) ++
          [w ++ [false, true], w ++ [true, false, false], w ++ [true, false, true, false],
            w ++ [true, false, true, true, false], w ++ [true, false, true, true, true],
            w ++ [true, true, false]] ++
          ((w ++ [true, true, true]) :: R) ++ [z ++ [false], z ++ [true]]) := by
    simpa only [CompanionTrees.sourceWords, CompanionTrees.targetWords,
      List.append_assoc, List.cons_append, List.nil_append] using hrel
  obtain ⟨ha00, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨ha01, hshape⟩ := List.forall₂_cons.mp hshape
  have hleftlen : ((a ++ [true]) :: L).length = (L ++ [w ++ [false, false]]).length := by simp
  simp only [List.append_eq, List.append_assoc] at hshape
  rw [← List.append_assoc L [w ++ [false, false]]] at hshape
  obtain ⟨hL, hshape⟩ := split_forall₂_append hleftlen hshape
  obtain ⟨hw01, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hw100, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hwshift, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hw10101, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hw1011, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hw11, hshape⟩ := List.forall₂_cons.mp hshape
  have hrightlen : (R ++ [z ++ [false]]).length = ((w ++ [true, true, true]) :: R).length := by simp
  simp only [List.append_eq] at hshape
  rw [← List.append_assoc R [z ++ [false]]] at hshape
  obtain ⟨hR, hshape⟩ := split_forall₂_append hrightlen hshape
  obtain ⟨hz10, hshape⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hz11, _⟩ := List.forall₂_cons.mp hshape
  obtain ⟨hvc0, hvc1⟩ := BranchRelated.children_of_shifted_chain hL hu hv0 hv1 huv
  have hwc (b : Bool) : BranchRelated H w (w ++ [b]) :=
    ((hvw.symm.descendant_to_related hvc0 hvc1 [b]).trans hvw).symm
  have hLchain := BranchRelated.of_shifted_chain hL
  have ha1 : BranchRelated H (a ++ [true]) w :=
    ((hLchain u (List.mem_cons_of_mem _ (List.mem_append_left _ hu))).trans huv).trans hvw
  have hLall (x : List Bool) (hx : x ∈ L) : BranchRelated H x w :=
    (hLchain x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))).symm.trans ha1
  have hwdesc (s : List Bool) : BranchRelated H (w ++ s) w :=
    BranchRelated.descendant_to_self (hwc false) (hwc true) s
  have hRflip : List.Forall₂ (BranchRelated H)
      ((w ++ [true, true, true]) :: R) (R ++ [z ++ [false]]) :=
    List.Forall₂.flip (hR.imp (fun _ _ h => h.symm))
  have hRchain := BranchRelated.of_shifted_chain hRflip
  have hRall (x : List Bool) (hx : x ∈ R) : BranchRelated H x w :=
    (hRchain x (List.mem_cons_of_mem _ (List.mem_append_left _ hx))).symm.trans (hwdesc _)
  have hz0 : BranchRelated H (z ++ [false]) w :=
    (hRchain _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))).symm.trans
      (hwdesc _)
  refine ⟨hwc false, hwc true, ?_, ?_, ?_⟩
  · intro x hx hxa hxz
    have hw0 := hwdesc [false]
    have hw10 := hwdesc [true, false]
    have hw11' := hwdesc [true, true]
    simp only [CompanionTrees.baseWords, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    aesop
  · exact endpointExit_related ha1 ha01 ha00
  · exact endpointExit_related hz0 hz10 hz11

end Kourovka.P21_38

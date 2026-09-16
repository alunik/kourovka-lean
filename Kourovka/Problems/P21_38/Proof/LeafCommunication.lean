import Kourovka.Problems.P21_38.Proof.BranchCommunication
import Mathlib.Data.List.Forall2
import Kourovka.Problems.P21_38.Proof.BinaryIntervalOrder

/-!
# Communication along leaf chains

The arguments here take place in the ordinary subgroup. Each equivalence
is witnessed by a finite product of its elements.
-/

namespace Kourovka.P21_38

namespace BranchRelated

variable {H : Subgroup (Equiv.Perm ℚ)}

/-- A finite shifted list of branches connects every vertex in the chain. -/
theorem of_shifted_chain {a b : List Bool} {ws : List (List Bool)}
    (h : List.Forall₂ (BranchRelated H) (a :: ws) (ws ++ [b])) :
    ∀ x ∈ a :: ws ++ [b], BranchRelated H a x := by
  induction ws generalizing a with
  | nil =>
    obtain ⟨hab, _⟩ := List.forall₂_cons.mp h
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact refl H a
    · have hx' := List.mem_singleton.mp hx
      subst x
      exact hab
  | cons w ws ih =>
    obtain ⟨haw, htail⟩ := List.forall₂_cons.mp h
    intro x hx
    rcases List.mem_cons.mp hx with hx | hx
    · subst x
      exact refl H a
    · exact haw.trans (ih htail x hx)

/-- A leaf chain containing `u,v0,v1`, together with `u~v`, collapses both children of `v`. -/
theorem children_of_shifted_chain {a b u v : List Bool} {ws : List (List Bool)}
    (h : List.Forall₂ (BranchRelated H) (a :: ws) (ws ++ [b]))
    (hu : u ∈ ws) (hv0 : v ++ [false] ∈ ws) (hv1 : v ++ [true] ∈ ws)
    (huv : BranchRelated H u v) :
    BranchRelated H v (v ++ [false]) ∧ BranchRelated H v (v ++ [true]) := by
  have hchain := of_shifted_chain h
  have hau := hchain u (List.mem_cons_of_mem _ (List.mem_append_left _ hu))
  have hva := (hau.trans huv).symm
  exact ⟨hva.trans (hchain _ (List.mem_cons_of_mem _ (List.mem_append_left _ hv0))),
    hva.trans (hchain _ (List.mem_cons_of_mem _ (List.mem_append_left _ hv1)))⟩

end BranchRelated

/-- Leave the constant endpoint ray after exactly `n` further equal bits. -/
def endpointExit (a : List Bool) (b : Bool) (n : ℕ) : List Bool :=
  a ++ List.replicate n b ++ [!b]

/-- Two endpoint branches propagate communication along the entire endpoint ray. -/
theorem endpointExit_related {H : Subgroup (Equiv.Perm ℚ)} {a w : List Bool} {b : Bool}
    (hbase : BranchRelated H (a ++ [!b]) w)
    (hstep : BranchRelated H (a ++ [b, !b]) (a ++ [!b]))
    (hdouble : BranchRelated H (a ++ [b, b]) (a ++ [b])) :
    ∀ n, BranchRelated H (endpointExit a b n) w := by
  intro n
  induction n with
  | zero => simpa [endpointExit] using hbase
  | succ n ih =>
    cases n with
    | zero => simpa [endpointExit] using hstep.trans hbase
    | succ n =>
      have h := hdouble.append (List.replicate n b ++ [!b])
      have h' : BranchRelated H (endpointExit a b (n + 2)) (endpointExit a b (n + 1)) := by
        simpa [endpointExit, List.replicate_succ, List.append_assoc] using h
      exact h'.trans ih

theorem exists_first_opposite {b : Bool} {r : List Bool} (h : (!b) ∈ r) :
    ∃ n s, r = List.replicate n b ++ ((!b) :: s) := by
  induction r with
  | nil => simp at h
  | cons c r ih =>
    by_cases hcb : c = b
    · subst c
      have hr : (!b) ∈ r := by simpa using h
      obtain ⟨n, s, rfl⟩ := ih hr
      exact ⟨n + 1, s, by simp [List.replicate_succ]⟩
    · have hc : c = !b := by cases b <;> cases c <;> simp_all
      exact ⟨0, r, by simp [hc]⟩

/-- A mixed word below an endpoint leaf eventually leaves its constant ray. -/
theorem exists_endpointExit_prefix {n : ℕ} {b : Bool} {r : List Bool}
    (hp : List.replicate n b <+: r) (hm : (!b) ∈ r) :
    ∃ j, endpointExit (List.replicate n b) b j <+: r := by
  obtain ⟨s, rfl⟩ := hp
  have hs : (!b) ∈ s := by simpa using hm
  obtain ⟨j, t, rfl⟩ := exists_first_opposite hs
  exact ⟨j, t, by simp only [endpointExit, List.append_assoc, List.singleton_append]⟩

/-- The maximum leaf length is finite; a sum gives a convenient sufficient bound. -/
theorem exists_leaf_length_bound (ws : List (List Bool)) :
    ∃ K : ℕ, ∀ w ∈ ws, w.length ≤ K := by
  induction ws with
  | nil => exact ⟨0, by simp⟩
  | cons w ws ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨max w.length K, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with rfl | hv
    · exact le_max_left _ _
    · exact (hK v hv).trans (le_max_right _ _)

/-- Interior leaves and the two endpoint rays imply uniform communication of deep words. -/
theorem deep_related_of_leaf_communication
    {H : Subgroup (Equiv.Perm ℚ)} {ws : List (List Bool)} {w : List Bool} {n m : ℕ}
    (hpart : WordPartition 0 1 ws)
    (hchildren0 : BranchRelated H w (w ++ [false]))
    (hchildren1 : BranchRelated H w (w ++ [true]))
    (hinterior : ∀ u ∈ ws, u ≠ List.replicate n false → u ≠ List.replicate m true →
      BranchRelated H u w)
    (hleft : ∀ j, BranchRelated H (endpointExit (List.replicate n false) false j) w)
    (hright : ∀ j, BranchRelated H (endpointExit (List.replicate m true) true j) w) :
    ∃ K : ℕ, ∀ p s : List Bool, false ∈ p → true ∈ p → K ≤ s.length →
      BranchRelated H (p ++ s) w := by
  obtain ⟨K, hK⟩ := exists_leaf_length_bound ws
  refine ⟨K, fun p s hp0 hp1 hs => ?_⟩
  have hlen : ∀ u ∈ ws, u.length ≤ (p ++ s).length := by
    intro u hu
    exact (hK u hu).trans (hs.trans (by simp))
  obtain ⟨u, hu, hup⟩ := hpart.exists_prefix_of_length_le (p ++ s) hlen
  by_cases hu0 : u = List.replicate n false
  · subst u
    obtain ⟨j, t, ht⟩ := exists_endpointExit_prefix hup
      (show (!false) ∈ p ++ s from List.mem_append_left _ hp1)
    rw [← ht]
    exact (hleft j).descendant_to_related hchildren0 hchildren1 t
  · by_cases hu1 : u = List.replicate m true
    · subst u
      obtain ⟨j, t, ht⟩ := exists_endpointExit_prefix hup
        (show (!true) ∈ p ++ s from List.mem_append_left _ hp0)
      rw [← ht]
      exact (hright j).descendant_to_related hchildren0 hchildren1 t
    · obtain ⟨t, ht⟩ := hup
      rw [← ht]
      exact (hinterior u hu hu0 hu1).descendant_to_related hchildren0 hchildren1 t

end Kourovka.P21_38

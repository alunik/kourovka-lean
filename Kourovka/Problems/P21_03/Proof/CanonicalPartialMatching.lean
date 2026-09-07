import Kourovka.Problems.P21_03.Proof.FiniteAsymmetricLopsidedLLL
import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.PartialBijectionCount
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Canonical partial-matching events in a random permutation

A canonical event prescribes the images of an injective list of source
points.  The broad conflict relation records a shared source or a shared
target.  The main result is the canonical-event lopsided counting inequality:
conditioning on avoidance of pairwise nonconflicting canonical events cannot
increase the density of a fixed event.
-/

namespace Kourovka213

open scoped BigOperators

/-- An injective partial matching in one finite ambient type. -/
structure CanonicalPartialMatching (alpha : Type*) where
  size : Nat
  source : Fin size ↪ alpha
  target : Fin size ↪ alpha

namespace CanonicalPartialMatching

variable {alpha I : Type*} [Fintype alpha] [DecidableEq alpha]

/-- The permutation realizes every prescribed edge of the partial matching. -/
def Holds (c : CanonicalPartialMatching alpha) (sigma : Equiv.Perm alpha) : Prop :=
  forall k, sigma (c.source k) = c.target k

/-- The finite canonical event associated with a partial matching. -/
noncomputable def event (c : CanonicalPartialMatching alpha) :
    Finset (Equiv.Perm alpha) := by
  classical
  exact Finset.univ.filter c.Holds

@[simp]
theorem mem_event {c : CanonicalPartialMatching alpha} {sigma : Equiv.Perm alpha} :
    sigma ∈ c.event ↔ c.Holds sigma := by
  classical
  simp [event]

/-- Exact size of a canonical event. -/
theorem card_event (c : CanonicalPartialMatching alpha) :
    c.event.card = (Fintype.card alpha - c.size).factorial := by
  classical
  rw [event]
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  unfold Holds
  rw [card_perm_extending_injective_pair c.source c.target
      c.source.injective c.target.injective]
  simp only [Fintype.card_fin]

/-- Two partial matchings broadly conflict if they share a source endpoint or
a target endpoint. -/
def Conflicts (c d : CanonicalPartialMatching alpha) : Prop :=
  (exists k l, c.source k = d.source l) ∨
    (exists k l, c.target k = d.target l)

theorem conflicts_symm {c d : CanonicalPartialMatching alpha} :
    c.Conflicts d -> d.Conflicts c := by
  rintro (⟨k, l, h⟩ | ⟨k, l, h⟩)
  · exact Or.inl ⟨l, k, h.symm⟩
  · exact Or.inr ⟨l, k, h.symm⟩

/-- The reflexive broad-conflict neighborhood in a finite indexed family. -/
noncomputable def neighborhood [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) : Finset I := by
  classical
  exact Finset.univ.filter fun j => i = j ∨ (C i).Conflicts (C j)

@[simp]
theorem mem_neighborhood [Fintype I] [DecidableEq I]
    {C : I -> CanonicalPartialMatching alpha} {i j : I} :
    j ∈ neighborhood C i ↔ i = j ∨ (C i).Conflicts (C j) := by
  classical
  simp [neighborhood]

/-- The target points used by the conditioning family which lie outside the
range of a proposed new target embedding.  These are the points fixed by the
transport permutation in the negative-dependency injection. -/
private def ProtectedTarget (C : I -> CanonicalPartialMatching alpha)
    (S : Finset I) {s : Nat} (f : Fin s ↪ alpha) :=
  {a : alpha //
    (exists j, j ∈ S ∧ exists k, (C j).target k = a) ∧
      a ∉ Set.range f}

private noncomputable instance protectedTargetFintype
    (C : I -> CanonicalPartialMatching alpha) (S : Finset I)
    {s : Nat} (f : Fin s ↪ alpha) : Fintype (ProtectedTarget C S f) :=
  letI : Finite (ProtectedTarget C S f) := by
    unfold ProtectedTarget
    infer_instance
  Fintype.ofFinite _

private def transportSource (C : I -> CanonicalPartialMatching alpha)
    (i : I) (S : Finset I) (f : Fin (C i).size ↪ alpha) :
    Fin (C i).size ⊕ ProtectedTarget C S f -> alpha :=
  Sum.elim (C i).target (fun a => a.1)

private def transportTarget (C : I -> CanonicalPartialMatching alpha)
    (i : I) (S : Finset I) (f : Fin (C i).size ↪ alpha) :
    Fin (C i).size ⊕ ProtectedTarget C S f -> alpha :=
  Sum.elim f (fun a => a.1)

private theorem transportSource_injective
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha) :
    Function.Injective (transportSource C i S f) := by
  unfold transportSource
  apply Function.Injective.sumElim (C i).target.injective Subtype.val_injective
  intro k a hka
  rcases a.2.1 with ⟨j, hjS, l, hl⟩
  apply hOutside j hjS
  rw [mem_neighborhood]
  apply Or.inr
  apply Or.inr
  exact ⟨k, l, hka.trans hl.symm⟩

private theorem transportTarget_injective
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (f : Fin (C i).size ↪ alpha) :
    Function.Injective (transportTarget C i S f) := by
  unfold transportTarget
  apply Function.Injective.sumElim f.injective Subtype.val_injective
  intro k a hka
  exact a.2.2 ⟨k, hka⟩

/-- A permutation carrying the original target list to `f`, while fixing all
conditioning targets which do not lie in the range of `f`. -/
private noncomputable def transportPermutation
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha) : Equiv.Perm alpha :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (transportSource C i S f) (transportTarget C i S f)
    (transportSource_injective C i S hOutside f)
    (transportTarget_injective C i S f)

private theorem transportPermutation_spec
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha)
    (z : Fin (C i).size ⊕ ProtectedTarget C S f) :
    transportPermutation C i S hOutside f (transportSource C i S f z) =
      transportTarget C i S f z :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (transportSource C i S f) (transportTarget C i S f)
    (transportSource_injective C i S hOutside f)
    (transportTarget_injective C i S f)) z

private theorem transportPermutation_target
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha) (k : Fin (C i).size) :
    transportPermutation C i S hOutside f ((C i).target k) = f k := by
  have h := transportPermutation_spec C i S hOutside f (Sum.inl k)
  change transportPermutation C i S hOutside f ((C i).target k) = f k at h
  exact h

private theorem transportPermutation_protected
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha) (a : ProtectedTarget C S f) :
    transportPermutation C i S hOutside f a.1 = a.1 := by
  have h := transportPermutation_spec C i S hOutside f (Sum.inr a)
  change transportPermutation C i S hOutside f a.1 = a.1 at h
  exact h

private theorem transported_mem_avoidEvents
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (f : Fin (C i).size ↪ alpha) (sigma : Equiv.Perm alpha)
    (hsigma_i : sigma ∈ (C i).event)
    (hsigma_S : sigma ∈ avoidEvents (fun j => (C j).event) S) :
    sigma.trans (transportPermutation C i S hOutside f) ∈
      avoidEvents (fun j => (C j).event) S := by
  rw [mem_avoidEvents]
  intro j hjS
  intro htau_j
  have hnotConflict : ¬((C i).Conflicts (C j)) := by
    intro hconflict
    exact hOutside j hjS (mem_neighborhood.mpr (Or.inr hconflict))
  have hi := mem_event.mp hsigma_i
  have hj := mem_event.mp htau_j
  have hsigma_not_j := (mem_avoidEvents.mp hsigma_S) j hjS
  by_cases hmeet : exists k, (C j).target k ∈ Set.range f
  · obtain ⟨k, l, hl⟩ := hmeet
    have hrho :
        transportPermutation C i S hOutside f
              (sigma ((C j).source k)) =
            transportPermutation C i S hOutside f ((C i).target l) := by
      calc
        transportPermutation C i S hOutside f
              (sigma ((C j).source k)) = (C j).target k := by
          simpa [Holds] using hj k
        _ = f l := hl.symm
        _ = transportPermutation C i S hOutside f ((C i).target l) :=
          (transportPermutation_target C i S hOutside f l).symm
    have hsigmaeq : sigma ((C j).source k) = (C i).target l :=
      (transportPermutation C i S hOutside f).injective hrho
    have hsource : (C j).source k = (C i).source l :=
      sigma.injective (hsigmaeq.trans (hi l).symm)
    exact hnotConflict (Or.inl ⟨l, k, hsource.symm⟩)
  · apply hsigma_not_j
    rw [mem_event]
    intro k
    let a : ProtectedTarget C S f :=
      ⟨(C j).target k,
        ⟨⟨j, hjS, k, rfl⟩, fun hk => hmeet ⟨k, hk⟩⟩⟩
    apply (transportPermutation C i S hOutside f).injective
    calc
      transportPermutation C i S hOutside f (sigma ((C j).source k)) =
          (C j).target k := by
        simpa [Holds] using hj k
      _ = transportPermutation C i S hOutside f ((C j).target k) := by
        simpa [a] using (transportPermutation_protected C i S hOutside f a).symm

private noncomputable def transportAvoider
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i) :
    (Fin (C i).size ↪ alpha) ×
        {sigma : Equiv.Perm alpha //
          sigma ∈ (C i).event ∩ avoidEvents (fun j => (C j).event) S} ->
      {tau : Equiv.Perm alpha // tau ∈ avoidEvents (fun j => (C j).event) S} :=
  fun z =>
    ⟨z.2.1.trans (transportPermutation C i S hOutside z.1),
      transported_mem_avoidEvents C i S hOutside z.1 z.2.1
        (Finset.mem_inter.mp z.2.2).1 (Finset.mem_inter.mp z.2.2).2⟩

private theorem transportAvoider_on_source
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i)
    (z : (Fin (C i).size ↪ alpha) ×
      {sigma : Equiv.Perm alpha //
        sigma ∈ (C i).event ∩ avoidEvents (fun j => (C j).event) S})
    (k : Fin (C i).size) :
    (transportAvoider C i S hOutside z).1 ((C i).source k) = z.1 k := by
  change transportPermutation C i S hOutside z.1
      (z.2.1 ((C i).source k)) = z.1 k
  rw [(mem_event.mp (Finset.mem_inter.mp z.2.2).1) k]
  exact transportPermutation_target C i S hOutside z.1 k

private theorem transportAvoider_injective
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i) :
    Function.Injective (transportAvoider C i S hOutside) := by
  intro z w hzw
  have hfirst : z.1 = w.1 := by
    apply DFunLike.ext _ _
    intro k
    calc
      z.1 k = (transportAvoider C i S hOutside z).1 ((C i).source k) :=
        (transportAvoider_on_source C i S hOutside z k).symm
      _ = (transportAvoider C i S hOutside w).1 ((C i).source k) := by
        exact congrArg (fun tau => tau.1 ((C i).source k)) hzw
      _ = w.1 k := transportAvoider_on_source C i S hOutside w k
  rcases z with ⟨f, sigma⟩
  rcases w with ⟨g, tau⟩
  dsimp at hfirst
  subst g
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Equiv.ext
    intro a
    apply (transportPermutation C i S hOutside f).injective
    have happ := congrArg (fun u => u.1 a) hzw
    simpa [transportAvoider] using happ

/-- Canonical-permutation negative dependency in division-free cardinal form.
There are `(n)_s` choices for a replacement target embedding, and the
transport construction injects all of them into the conditioned avoiders. -/
theorem descFactorial_mul_card_event_inter_avoidEvents_le
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) (i : I) (S : Finset I)
    (hOutside : ∀ j ∈ S, j ∉ neighborhood C i) :
    (Fintype.card alpha).descFactorial (C i).size *
        ((C i).event ∩ avoidEvents (fun j => (C j).event) S).card <=
      (avoidEvents (fun j => (C j).event) S).card := by
  classical
  have hcard := Fintype.card_le_of_injective
    (transportAvoider C i S hOutside)
    (transportAvoider_injective C i S hOutside)
  simpa only [Fintype.card_prod, Fintype.card_embedding_eq,
    Fintype.card_coe, Fintype.card_fin] using hcard

/-- The canonical negative-dependency estimate with the distinguished event
allowed to lie outside the indexed conditioning family.  This is the form
needed when a non-core transporter prescription is conditioned on avoidance
of all core collision events. -/
theorem descFactorial_mul_card_external_event_inter_avoidEvents_le
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (c : CanonicalPartialMatching alpha) (S : Finset I)
    (hOutside : ∀ j ∈ S, ¬ c.Conflicts (C j)) :
    (Fintype.card alpha).descFactorial c.size *
        (c.event ∩ avoidEvents (fun j => (C j).event) S).card <=
      (avoidEvents (fun j => (C j).event) S).card := by
  classical
  let D : Option I -> CanonicalPartialMatching alpha
    | none => c
    | some j => C j
  let S' : Finset (Option I) := S.image some
  have hOutside' : ∀ j ∈ S', j ∉ neighborhood D none := by
    intro j hj
    obtain ⟨k, hkS, rfl⟩ := Finset.mem_image.mp hj
    rw [mem_neighborhood]
    change ¬ (none = some k ∨ c.Conflicts (C k))
    intro h
    rcases h with h | h
    · exact Option.some_ne_none k h.symm
    · exact hOutside k hkS h
  have hAvoid :
      avoidEvents (fun j => (D j).event) S' =
        avoidEvents (fun j => (C j).event) S := by
    ext sigma
    simp only [mem_avoidEvents]
    constructor
    · intro hsigma j hjS
      have hjS' : some j ∈ S' := Finset.mem_image.mpr ⟨j, hjS, rfl⟩
      simpa [D] using hsigma (some j) hjS'
    · intro hsigma j hjS'
      obtain ⟨k, hkS, rfl⟩ := Finset.mem_image.mp hjS'
      simpa [D] using hsigma k hkS
  have hcount :=
    descFactorial_mul_card_event_inter_avoidEvents_le D none S' hOutside'
  simpa [D, hAvoid] using hcount

/-- Core events which broadly conflict with a distinguished external
canonical event. -/
noncomputable def conflictSet [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (c : CanonicalPartialMatching alpha) : Finset I := by
  classical
  exact Finset.univ.filter fun j => c.Conflicts (C j)

@[simp]
theorem mem_conflictSet [Fintype I] [DecidableEq I]
    {C : I -> CanonicalPartialMatching alpha}
    {c : CanonicalPartialMatching alpha} {j : I} :
    j ∈ conflictSet C c ↔ c.Conflicts (C j) := by
  classical
  simp [conflictSet]

/-- Real-density form of canonical negative dependency for an event outside
the conditioning family. -/
theorem external_event_density_le
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha)
    (c : CanonicalPartialMatching alpha) (S : Finset I)
    (hOutside : ∀ j ∈ S, ¬ c.Conflicts (C j)) :
    ((c.event ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
      (1 / ((Fintype.card alpha).descFactorial c.size : Real)) *
        ((avoidEvents (fun j => (C j).event) S).card : Real) := by
  have hcount :=
    descFactorial_mul_card_external_event_inter_avoidEvents_le C c S hOutside
  have hsize : c.size <= Fintype.card alpha := by
    simpa using Fintype.card_le_of_injective c.source c.source.injective
  have hdposNat : 0 < (Fintype.card alpha).descFactorial c.size :=
    Nat.descFactorial_pos.mpr hsize
  have hdpos :
      (0 : Real) < ((Fintype.card alpha).descFactorial c.size : Real) := by
    exact_mod_cast hdposNat
  have hcountReal :
      ((Fintype.card alpha).descFactorial c.size : Real) *
          ((c.event ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
        ((avoidEvents (fun j => (C j).event) S).card : Real) := by
    exact_mod_cast hcount
  calc
    ((c.event ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
        ((avoidEvents (fun j => (C j).event) S).card : Real) /
          ((Fintype.card alpha).descFactorial c.size : Real) := by
      apply (le_div_iff₀ hdpos).mpr
      simpa [mul_comm] using hcountReal
    _ = (1 / ((Fintype.card alpha).descFactorial c.size : Real)) *
          ((avoidEvents (fun j => (C j).event) S).card : Real) := by
      ring

/-- The broad conflict neighborhoods form a lopsided dependency system with
the exact canonical-event density `1 / (n)_s`. -/
theorem finiteLopsidedBound_event
    [Fintype I] [DecidableEq I]
    (C : I -> CanonicalPartialMatching alpha) :
    FiniteLopsidedBound (fun i => (C i).event) (neighborhood C)
      (fun i => 1 / ((Fintype.card alpha).descFactorial (C i).size : Real)) := by
  intro i S _hiS hOutside
  have hcount := descFactorial_mul_card_event_inter_avoidEvents_le C i S hOutside
  have hsize : (C i).size <= Fintype.card alpha := by
    simpa using Fintype.card_le_of_injective (C i).source (C i).source.injective
  have hdposNat : 0 < (Fintype.card alpha).descFactorial (C i).size :=
    Nat.descFactorial_pos.mpr hsize
  have hdpos :
      (0 : Real) < ((Fintype.card alpha).descFactorial (C i).size : Real) := by
    exact_mod_cast hdposNat
  have hcountReal :
      ((Fintype.card alpha).descFactorial (C i).size : Real) *
          (((C i).event ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
        ((avoidEvents (fun j => (C j).event) S).card : Real) := by
    exact_mod_cast hcount
  calc
    (((C i).event ∩ avoidEvents (fun j => (C j).event) S).card : Real) <=
        ((avoidEvents (fun j => (C j).event) S).card : Real) /
          ((Fintype.card alpha).descFactorial (C i).size : Real) := by
      apply (le_div_iff₀ hdpos).mpr
      simpa [mul_comm] using hcountReal
    _ = (1 / ((Fintype.card alpha).descFactorial (C i).size : Real)) *
          ((avoidEvents (fun j => (C j).event) S).card : Real) := by
      ring

end CanonicalPartialMatching

end Kourovka213

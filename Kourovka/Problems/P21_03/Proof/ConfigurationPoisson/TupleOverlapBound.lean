import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.EndpointDegree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Finset

/-!
# A finite union bound for endpoint-overlapping tuples

This is the quantitative combinatorial core of the bounded-degree Brun sieve.
For an endpoint map with fibres of size at most `d`, the number of `I`-tuples
whose two-oriented endpoint map is not injective is at most
`(2|I|)^2 d |W|^(|I|-1)`.
-/

namespace Kourovka213

open scoped BigOperators

section BinaryConstraint

variable {I W X : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W] [DecidableEq X]

private def binaryConstraintEmbedding (i j : I) (hij : i ≠ j)
    (a b : W → X) :
    {F : I → W // a (F i) = b (F j)} ↪
      Σ rest : ({t : I // t ≠ j} → W),
        {w : W // b w = a (rest ⟨i, hij⟩)} where
  toFun F :=
    ⟨fun t => F.1 t.1, ⟨F.1 j, F.2.symm⟩⟩
  inj' := by
    intro F G h
    apply Subtype.ext
    funext t
    by_cases ht : t = j
    · subst t
      exact congrArg (fun z => z.2.1) h
    · exact congrArg (fun z => z.1 ⟨t, ht⟩) h

/-- One equality between two distinct coordinates costs one free choice, up to
the maximum fibre size of the second endpoint map. -/
theorem card_binaryConstraint_le (i j : I) (hij : i ≠ j)
    (a b : W → X) (d : ℕ)
    (hfiber : ∀ x : X, Fintype.card {w : W // b w = x} ≤ d) :
    Fintype.card {F : I → W // a (F i) = b (F j)} ≤
      Fintype.card W ^ (Fintype.card I - 1) * d := by
  have hinj := Fintype.card_le_of_injective
    (binaryConstraintEmbedding i j hij a b)
    (binaryConstraintEmbedding i j hij a b).injective
  have hsub : Fintype.card {t : I // t ≠ j} = Fintype.card I - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hcod :
      Fintype.card (Σ rest : ({t : I // t ≠ j} → W),
        {w : W // b w = a (rest ⟨i, hij⟩)}) ≤
        Fintype.card W ^ (Fintype.card I - 1) * d := by
    rw [Fintype.card_sigma]
    calc
      (∑ rest : ({t : I // t ≠ j} → W),
          Fintype.card {w : W // b w = a (rest ⟨i, hij⟩)}) ≤
          ∑ _rest : ({t : I // t ≠ j} → W), d := by
        apply Finset.sum_le_sum
        intro rest _hrest
        exact hfiber _
      _ = Fintype.card ({t : I // t ≠ j} → W) * d := by simp
      _ = Fintype.card W ^ (Fintype.card I - 1) * d := by
        rw [Fintype.card_fun, hsub]
  exact hinj.trans hcod

end BinaryConstraint

section EndpointTuples

variable {I W X : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W] [DecidableEq X]

/-- Tuples for which a specified pair of oriented coordinates has equal
endpoints. -/
noncomputable def endpointCollisionTuples
    (endpoint : W → Bool → X) (a b : I × Bool) : Finset (I → W) := by
  classical
  exact Finset.univ.filter fun F =>
    endpoint (F a.1) a.2 = endpoint (F b.1) b.2

/-- Union of all pair-collision events for distinct oriented coordinates. -/
noncomputable def endpointCollisionCover
    (endpoint : W → Bool → X) : Finset (I → W) := by
  classical
  exact Finset.univ.biUnion fun a : I × Bool =>
    (Finset.univ.erase a).biUnion fun b => endpointCollisionTuples endpoint a b

/-- Tuples whose induced map from oriented coordinates to endpoints is not
injective. -/
noncomputable def endpointOverlappingTuples
    (endpoint : W → Bool → X) : Finset (I → W) := by
  classical
  exact Finset.univ.filter fun F =>
    ¬Function.Injective fun a : I × Bool => endpoint (F a.1) a.2

theorem endpointOverlappingTuples_subset_cover
    (endpoint : W → Bool → X) :
    endpointOverlappingTuples (I := I) endpoint ⊆
      endpointCollisionCover (I := I) endpoint := by
  classical
  intro F hF
  rw [endpointOverlappingTuples, Finset.mem_filter] at hF
  obtain ⟨a, b, habEq, habNe⟩ := Function.not_injective_iff.mp hF.2
  simp only [endpointCollisionCover, Finset.mem_biUnion, Finset.mem_univ,
    endpointCollisionTuples, Finset.mem_erase, Finset.mem_filter, true_and]
  exact ⟨a, ⟨b, ⟨⟨habNe.symm, trivial⟩, habEq⟩⟩⟩

private theorem endpointCollisionTuples_eq_empty_of_same_index
    (endpoint : W → Bool → X)
    (hwithin : ∀ w : W, endpoint w false ≠ endpoint w true)
    (a b : I × Bool) (hab : a ≠ b) (hindex : a.1 = b.1) :
    endpointCollisionTuples endpoint a b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro F hF
  rw [endpointCollisionTuples, Finset.mem_filter] at hF
  have horient : a.2 ≠ b.2 := by
    intro h
    exact hab (Prod.ext hindex h)
  cases ha : a.2 <;> cases hb : b.2 <;> simp_all [hwithin]
  exact hwithin _ hF.symm

private theorem card_endpointCollisionTuples_le
    (endpoint : W → Bool → X)
    (hwithin : ∀ w : W, endpoint w false ≠ endpoint w true)
    (d : ℕ)
    (hfiber : ∀ (b : Bool) (x : X),
      Fintype.card {w : W // endpoint w b = x} ≤ d)
    (a b : I × Bool) (hab : a ≠ b) :
    (endpointCollisionTuples endpoint a b).card ≤
      Fintype.card W ^ (Fintype.card I - 1) * d := by
  classical
  by_cases hindex : a.1 = b.1
  · rw [endpointCollisionTuples_eq_empty_of_same_index endpoint hwithin a b hab hindex]
    simp
  · rw [endpointCollisionTuples, ← Fintype.card_subtype]
    exact card_binaryConstraint_le a.1 b.1 hindex
      (fun w => endpoint w a.2) (fun w => endpoint w b.2) d (hfiber b.2)

/-- Quantitative union bound for endpoint-overlapping tuples. -/
theorem card_endpointOverlappingTuples_le
    (endpoint : W → Bool → X)
    (hwithin : ∀ w : W, endpoint w false ≠ endpoint w true)
    (d : ℕ)
    (hfiber : ∀ (b : Bool) (x : X),
      Fintype.card {w : W // endpoint w b = x} ≤ d) :
    (endpointOverlappingTuples (I := I) endpoint).card ≤
      (2 * Fintype.card I) ^ 2 *
        (Fintype.card W ^ (Fintype.card I - 1) * d) := by
  classical
  let R := Fintype.card W ^ (Fintype.card I - 1) * d
  have hcover :
      (endpointCollisionCover (I := I) endpoint).card ≤
        Fintype.card (I × Bool) * (Fintype.card (I × Bool) * R) := by
    unfold endpointCollisionCover
    apply (Finset.card_biUnion_le_card_mul _ _ _)
    intro a _ha
    calc
      ((Finset.univ.erase a).biUnion fun b => endpointCollisionTuples endpoint a b).card ≤
          (Finset.univ.erase a).card * R := by
        apply (Finset.card_biUnion_le_card_mul _ _ _)
        intro b hb
        exact card_endpointCollisionTuples_le endpoint hwithin d hfiber a b
          (Finset.ne_of_mem_erase hb).symm
      _ ≤ Fintype.card (I × Bool) * R := by
        apply Nat.mul_le_mul_right
        simpa using Finset.card_le_card (Finset.erase_subset a Finset.univ)
  calc
    (endpointOverlappingTuples (I := I) endpoint).card ≤
        (endpointCollisionCover (I := I) endpoint).card :=
      Finset.card_le_card
        (endpointOverlappingTuples_subset_cover (I := I) endpoint)
    _ ≤ Fintype.card (I × Bool) * (Fintype.card (I × Bool) * R) := hcover
    _ = (2 * Fintype.card I) ^ 2 *
        (Fintype.card W ^ (Fintype.card I - 1) * d) := by
      simp [R]
      ring

end EndpointTuples

end Kourovka213

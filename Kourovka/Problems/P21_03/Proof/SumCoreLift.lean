import Kourovka.Problems.P21_03.Proof.ForestContainer
import Kourovka.Problems.P21_03.Proof.TranspositionCore

/-!
# Lifting transposition cores through direct sums

Extending a permutation by the identity along an embedding preserves the
property of being a transposition.  Consequently it transports a
transposition core whenever it transports the ambient subgroup.
-/

namespace Kourovka213

universe u v

private theorem viaEmbedding_isSwap
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) {g : Equiv.Perm X} (hg : g.IsSwap) :
    (Equiv.Perm.viaEmbeddingHom e g).IsSwap := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hg
  refine ⟨e a, e b, e.injective.ne hab, ?_⟩
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply]
    simp [Equiv.swap_apply_def, e.injective.eq_iff]
    split_ifs <;> rfl
  · rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem]
    · symm
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        exact hy ⟨a, h.symm⟩
      · intro h
        exact hy ⟨b, h.symm⟩
    · exact hy

/-- Extending permutations by the identity maps one transposition core into
another, provided it maps the corresponding ambient subgroup into the other. -/
theorem viaEmbedding_mem_transpositionCore_of_mem
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) (H : Subgroup (Equiv.Perm X))
    (K : Subgroup (Equiv.Perm Y))
    (hHK : ∀ g ∈ H, Equiv.Perm.viaEmbeddingHom e g ∈ K)
    {g : Equiv.Perm X} (hg : g ∈ transpositionCore H) :
    Equiv.Perm.viaEmbeddingHom e g ∈ transpositionCore K := by
  change g ∈ Subgroup.closure (transpositionsIn H) at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      rw [transpositionCore]
      apply Subgroup.subset_closure
      exact ⟨viaEmbedding_isSwap e hg.1, hHK g hg.2⟩
  | one => simpa only [map_one] using
      (Subgroup.one_mem (transpositionCore K))
  | mul a b _ _ ha hb =>
      rw [map_mul]
      exact Subgroup.mul_mem (transpositionCore K) ha hb
  | inv a _ ha =>
      rw [map_inv]
      exact Subgroup.inv_mem (transpositionCore K) ha

namespace SolubleAction

private def sumLeftEmbedding (A B : SolubleAction) :
    A.Point ↪ A.Point ⊕ B.Point where
  toFun := Sum.inl
  inj' _ _ h := Sum.inl.inj h

private def sumRightEmbedding (A B : SolubleAction) :
    B.Point ↪ A.Point ⊕ B.Point where
  toFun := Sum.inr
  inj' _ _ h := Sum.inr.inj h

private theorem viaEmbedding_left_toPerm (A B : SolubleAction)
    (a : A.Actor) :
    Equiv.Perm.viaEmbeddingHom (sumLeftEmbedding A B) (A.toPermHom a) =
      (SolubleAction.sum A B).toPermHom (a, 1) := by
  classical
  apply Equiv.ext
  intro p
  cases p with
  | inl x =>
      change
        ((A.toPermHom a).viaEmbedding (sumLeftEmbedding A B))
            ((sumLeftEmbedding A B) x) = _
      rw [Equiv.Perm.viaEmbedding_apply]
      rfl
  | inr y =>
      rw [Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem]
      · change Sum.inr y = Sum.inr ((1 : B.Actor) • y)
        simp
      · rintro ⟨x, h⟩
        change Sum.inl x = Sum.inr y at h
        cases h

private theorem viaEmbedding_right_toPerm (A B : SolubleAction)
    (b : B.Actor) :
    Equiv.Perm.viaEmbeddingHom (sumRightEmbedding A B) (B.toPermHom b) =
      (SolubleAction.sum A B).toPermHom (1, b) := by
  classical
  apply Equiv.ext
  intro p
  cases p with
  | inl x =>
      rw [Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem]
      · change Sum.inl x = Sum.inl ((1 : A.Actor) • x)
        simp
      · rintro ⟨y, h⟩
        change Sum.inr y = Sum.inl x at h
        cases h
  | inr y =>
      change
        ((B.toPermHom b).viaEmbedding (sumRightEmbedding A B))
            ((sumRightEmbedding A B) y) = _
      rw [Equiv.Perm.viaEmbedding_apply]
      rfl

/-- Componentwise transposition-core membership implies transposition-core
membership in the direct-sum action. -/
theorem sum_toPerm_mem_transpositionCore_of_components
    (A B : SolubleAction)
    (g : (SolubleAction.sum A B).Actor)
    (hA : A.toPermHom g.1 ∈ transpositionCore A.toPermHom.range)
    (hB : B.toPermHom g.2 ∈ transpositionCore B.toPermHom.range) :
    (SolubleAction.sum A B).toPermHom g ∈
      transpositionCore (SolubleAction.sum A B).toPermHom.range := by
  let S := SolubleAction.sum A B
  have hleft : S.toPermHom (g.1, 1) ∈ transpositionCore S.toPermHom.range := by
    rw [← viaEmbedding_left_toPerm A B]
    apply viaEmbedding_mem_transpositionCore_of_mem
      (sumLeftEmbedding A B) A.toPermHom.range S.toPermHom.range
    · intro σ hσ
      obtain ⟨a, rfl⟩ := hσ
      rw [viaEmbedding_left_toPerm]
      exact ⟨(a, 1), rfl⟩
    · exact hA
  have hright : S.toPermHom (1, g.2) ∈ transpositionCore S.toPermHom.range := by
    rw [← viaEmbedding_right_toPerm A B]
    apply viaEmbedding_mem_transpositionCore_of_mem
      (sumRightEmbedding A B) B.toPermHom.range S.toPermHom.range
    · intro σ hσ
      obtain ⟨b, rfl⟩ := hσ
      rw [viaEmbedding_right_toPerm]
      exact ⟨(1, b), rfl⟩
    · exact hB
  have hgprod : g = (g.1, 1) * (1, g.2) := by
    ext <;> simp
  rw [hgprod, map_mul]
  exact Subgroup.mul_mem (transpositionCore S.toPermHom.range) hleft hright

end SolubleAction

end Kourovka213

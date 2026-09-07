import Kourovka.Problems.P21_03.Proof.ConfigurationPoisson.EndpointDegree

/-!
# Counting maps with few occupied bounded fibres

If every fibre of `block : X → L` has size at most `d`, the number of maps
`I → X` occupying exactly `b` block labels is at most
`|L|^b (bd)^|I|`.
-/

namespace Kourovka213

section BlockMaps

variable {I X L : Type*}
variable [Fintype I] [DecidableEq I]
variable [Fintype X] [DecidableEq X]
variable [Fintype L] [DecidableEq L]

/-- Block labels used by a finite map. -/
def usedBlockLabels (block : X → L) (f : I → X) : Finset L :=
  Finset.univ.image (block ∘ f)

/-- Points lying over one of a finite collection of labels. -/
def pointsOverLabels (block : X → L) (B : Finset L) :=
  {x : X // block x ∈ B}

noncomputable instance (block : X → L) (B : Finset L) :
    Fintype (pointsOverLabels block B) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

private def pointOverLabelsEmbedding (block : X → L) (B : Finset L) :
    pointsOverLabels block B ↪
      Σ a : B, {x : X // block x = a.1} where
  toFun x := ⟨⟨block x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) h

/-- A union of `b` fibres of size at most `d` has at most `bd` points. -/
theorem card_pointsOverLabels_le (block : X → L) (B : Finset L) (d : ℕ)
    (hfiber : ∀ a : L, Fintype.card {x : X // block x = a} ≤ d) :
    Fintype.card (pointsOverLabels block B) ≤ B.card * d := by
  calc
    Fintype.card (pointsOverLabels block B) ≤
        Fintype.card (Σ a : B, {x : X // block x = a.1}) :=
      Fintype.card_le_of_injective (pointOverLabelsEmbedding block B)
        (pointOverLabelsEmbedding block B).injective
    _ = Finset.univ.sum
        (fun a : B => Fintype.card {x : X // block x = a.1}) := by
      rw [Fintype.card_sigma]
    _ ≤ Finset.univ.sum (fun _a : B => d) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact hfiber a.1
    _ = B.card * d := by simp

private def mapsByUsedLabelsEmbedding (block : X → L) (b : ℕ) :
    {f : I → X // (usedBlockLabels block f).card = b} ↪
      Σ B : {B : Finset L // B.card = b},
        I → pointsOverLabels block B.1 where
  toFun f :=
    ⟨⟨usedBlockLabels block f.1, f.2⟩,
      fun i => ⟨f.1 i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩
  inj' := by
    intro f g h
    apply Subtype.ext
    funext i
    exact congrArg (fun z => ((z.2 i).1 : X)) h

/-- Number of finite maps using exactly `b` labels of a bounded-fibre map. -/
theorem card_maps_usedBlockLabels_eq_le (block : X → L) (b d : ℕ)
    (hfiber : ∀ a : L, Fintype.card {x : X // block x = a} ≤ d) :
    Fintype.card {f : I → X // (usedBlockLabels block f).card = b} ≤
      Fintype.card L ^ b * (b * d) ^ Fintype.card I := by
  have hpoint : ∀ B : {B : Finset L // B.card = b},
      Fintype.card (pointsOverLabels block B.1) ≤ b * d := by
    intro B
    simpa [B.2] using card_pointsOverLabels_le block B.1 d hfiber
  calc
    Fintype.card {f : I → X // (usedBlockLabels block f).card = b} ≤
        Fintype.card (Σ B : {B : Finset L // B.card = b},
          I → pointsOverLabels block B.1) :=
      Fintype.card_le_of_injective (mapsByUsedLabelsEmbedding block b)
        (mapsByUsedLabelsEmbedding block b).injective
    _ = Finset.univ.sum (fun B : {B : Finset L // B.card = b} =>
        Fintype.card (pointsOverLabels block B.1) ^ Fintype.card I) := by
      simp [Fintype.card_sigma, Fintype.card_fun]
    _ ≤ Finset.univ.sum (fun _B : {B : Finset L // B.card = b} =>
        (b * d) ^ Fintype.card I) := by
      apply Finset.sum_le_sum
      intro B _hB
      exact Nat.pow_le_pow_left (hpoint B) _
    _ = (Fintype.card L).choose b * (b * d) ^ Fintype.card I := by
      simp [Fintype.card_finset_len]
    _ ≤ Fintype.card L ^ b * (b * d) ^ Fintype.card I :=
      Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

end BlockMaps

end Kourovka213

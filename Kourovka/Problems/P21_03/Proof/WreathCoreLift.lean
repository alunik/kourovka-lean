import Kourovka.Problems.P21_03.Proof.NaturalWreath
import Kourovka.Problems.P21_03.Proof.TranspositionCore
import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Lifting transposition cores through a wreath-product base

A pure base element acts independently on the fibres.  This file proves that if
every fibre section belongs to the transposition core of the fibre action, then
the resulting natural wreath permutation belongs to the transposition core of
the full wreath action.
-/

namespace Kourovka213

universe u v

namespace PermWreath

private def fibreEmbedding (i : ι) : Δ ↪ ι × Δ where
  toFun d := (i, d)
  inj' _ _ h := congrArg Prod.snd h

/-- Extend a fibre permutation by the identity outside one wreath block. -/
private noncomputable def fibrePermHom (i : ι) :
    Equiv.Perm Δ →* Equiv.Perm (ι × Δ) :=
  Equiv.Perm.viaEmbeddingHom (fibreEmbedding i)

private theorem fibrePermHom_toPerm
    (X Q ι Δ : Type*) [Group X] [Group Q]
    [MulAction Q ι] [MulAction X Δ]
    [DecidableEq ι] [DecidableEq Δ] (i : ι) (x : X) :
    fibrePermHom i (MulAction.toPermHom X Δ x) =
      naturalToPerm X Q ι Δ (coordinate X Q ι i x) := by
  classical
  apply Equiv.ext
  intro p
  rcases p with ⟨j, d⟩
  by_cases hji : j = i
  · subst j
    change
      ((MulAction.toPermHom X Δ x).viaEmbedding (fibreEmbedding i))
          ((fibreEmbedding i) d) = _
    rw [Equiv.Perm.viaEmbedding_apply]
    rw [naturalToPerm_apply, coordinate_right, one_smul,
      coordinate_left_apply, if_pos rfl]
    dsimp only [fibreEmbedding]
    rfl
  · rw [fibrePermHom, Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem]
    · simp [hji]
    · rintro ⟨d', hd'⟩
      exact hji (congrArg Prod.fst hd').symm

private theorem fibrePermHom_isSwap [DecidableEq ι] [DecidableEq Δ]
    {i : ι} {g : Equiv.Perm Δ}
    (hg : g.IsSwap) : (fibrePermHom i g).IsSwap := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := hg
  refine ⟨(i, a), (i, b), ?_, ?_⟩
  · exact fun h ↦ hab (congrArg Prod.snd h)
  · apply Equiv.ext
    intro p
    rcases p with ⟨j, d⟩
    by_cases hji : j = i
    · subst j
      change
        ((Equiv.swap a b).viaEmbedding (fibreEmbedding i))
            ((fibreEmbedding i) d) = _
      rw [Equiv.Perm.viaEmbedding_apply]
      dsimp only [fibreEmbedding]
      simp only [Equiv.swap_apply_def, Prod.mk.injEq, true_and]
      split_ifs <;> rfl
    · rw [fibrePermHom, Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem]
      · symm
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          exact hji (congrArg Prod.fst h)
        · intro h
          exact hji (congrArg Prod.fst h)
      · rintro ⟨d', hd'⟩
        exact hji (congrArg Prod.fst hd').symm

/-- A transposition-core element in one fibre lifts to the transposition core
of the full natural wreath action at any chosen coordinate. -/
theorem naturalToPerm_coordinate_mem_transpositionCore
    (X Q ι Δ : Type*) [Group X] [Group Q]
    [MulAction Q ι] [MulAction X Δ]
    [DecidableEq ι] [DecidableEq Δ] (i : ι) (x : X)
    (hx : MulAction.toPermHom X Δ x ∈
      transpositionCore (MulAction.toPermHom X Δ).range) :
    naturalToPerm X Q ι Δ (coordinate X Q ι i x) ∈
      transpositionCore (naturalToPerm X Q ι Δ).range := by
  let φ := MulAction.toPermHom X Δ
  let ψ := naturalToPerm X Q ι Δ
  let F : Equiv.Perm Δ →* Equiv.Perm (ι × Δ) :=
    fibrePermHom (i := i)
  have hmap : ∀ (g : Equiv.Perm Δ),
      g ∈ transpositionCore φ.range →
        F g ∈ transpositionCore ψ.range := by
    intro g hg
    change g ∈ Subgroup.closure (transpositionsIn φ.range) at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
        rw [transpositionCore]
        apply Subgroup.subset_closure
        refine ⟨fibrePermHom_isSwap hg.1, ?_⟩
        obtain ⟨y, rfl⟩ := hg.2
        refine ⟨coordinate X Q ι i y, ?_⟩
        exact (fibrePermHom_toPerm X Q ι Δ i y).symm
    | one => simpa only [map_one] using
        (Subgroup.one_mem (transpositionCore ψ.range))
    | mul a b _ _ ha hb =>
        rw [map_mul]
        exact Subgroup.mul_mem (transpositionCore ψ.range) ha hb
    | inv a _ ha =>
        rw [map_inv]
        exact Subgroup.inv_mem (transpositionCore ψ.range) ha
  rw [← fibrePermHom_toPerm X Q ι Δ i x]
  exact hmap _ hx

/-- If every section of a pure base element lies in the transposition core of
the fibre action, then the whole base permutation lies in the transposition
core of the natural wreath action. -/
theorem naturalToPerm_base_mem_transpositionCore_of_forall
    (X Q ι Δ : Type*) [Group X] [Group Q]
    [MulAction Q ι] [MulAction X Δ]
    [Fintype ι] [DecidableEq ι] [DecidableEq Δ]
    (f : ι → X)
    (hf : ∀ i, MulAction.toPermHom X Δ (f i) ∈
      transpositionCore (MulAction.toPermHom X Δ).range) :
    naturalToPerm X Q ι Δ (base X Q ι f) ∈
      transpositionCore (naturalToPerm X Q ι Δ).range := by
  classical
  let ψ := naturalToPerm X Q ι Δ
  let B : (ι → X) →* Equiv.Perm (ι × Δ) :=
    ψ.comp (base X Q ι)
  let E := MonoidHom.noncommPiCoprodEquiv
    (M := Equiv.Perm (ι × Δ)) (N := fun _ : ι ↦ X)
  let Φ := E.symm B
  have hB : MonoidHom.noncommPiCoprod Φ.1 Φ.2 = B :=
    E.apply_symm_apply B
  change B f ∈ transpositionCore ψ.range
  rw [← hB]
  rw [MonoidHom.noncommPiCoprod_apply]
  apply Subgroup.noncommProd_mem (transpositionCore ψ.range) _
  intro i _hi
  change B (Pi.mulSingle i (f i)) ∈ transpositionCore ψ.range
  have hcoord : B (Pi.mulSingle i (f i)) =
      ψ (coordinate X Q ι i (f i)) := by
    apply congrArg ψ
    apply PermWreath.ext
    · funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    · simp [B]
  rw [hcoord]
  exact naturalToPerm_coordinate_mem_transpositionCore
    X Q ι Δ i (f i) (hf i)

end PermWreath

end Kourovka213

import Kourovka2135.WeightedCharacterProjector
import Kourovka2135.FinitePermutationMovingRank

/-! Distinct coprime character weights supply actual independent vectors and
moving-rank lower bounds. Orthogonality is proved for the actual averaging
operators; no classification or chosen Fourier basis is assumed. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.CharacterWeightIndependence
open WeightedCharacterProjector

variable {k U V : Type u} [Field k] [Group U] [IsMulCommutative U] [Fintype U]
variable [AddCommGroup V] [Module k V]
variable (ρ : Representation k U V)

theorem projector_action (χ : U →* kˣ) (g : U) (v : V) :
    projector ρ χ (ρ g v) = ρ g (projector ρ χ v) := by
  simp only [projector_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  change (ρ t * ρ g) v = (ρ g * ρ t) v
  rw [← map_mul, ← map_mul, mul_comm' t g]

/-- The projector of one character kills a vector of a different character. -/
theorem projector_eq_zero_of_ne (χ ψ : U →* kˣ) (hχψ : χ ≠ ψ)
    (v : V) (hv : ∀ g, ρ g v = (ψ g : k) • v) : projector ρ χ v = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : U, χ g ≠ ψ g := by
    by_contra he
    push Not at he
    exact hχψ (MonoidHom.ext he)
  have hs : (χ g : k) ≠ (ψ g : k) := fun he => hg (Units.ext he)
  have ha := action_projector ρ χ g v
  have hb : ρ g (projector ρ χ v) = (ψ g : k) • projector ρ χ v := by
    rw [← projector_action, hv g, map_smul]
  have hz : ((χ g : k) - (ψ g : k)) • projector ρ χ v = 0 := by
    rw [sub_smul, ← ha, ← hb, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs)

/-- Finite families of distinct nonzero character vectors are independent. -/
theorem linearIndependent_of_characters {ι : Type*} [Fintype ι]
    (hcard : (Fintype.card U : k) ≠ 0)
    (χ : ι → U →* kˣ) (hχ : Function.Injective χ)
    (v : ι → V) (hv : ∀ i, v i ≠ 0)
    (heigen : ∀ i g, ρ g (v i) = (χ i g : k) • v i) :
    LinearIndependent k v := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hp := congrArg (projector ρ (χ i)) ha
  simp only [map_sum, map_smul, map_zero] at hp
  have hs : (∑ j, a j • projector ρ (χ i) (v j)) = a i • v i := by
    rw [Finset.sum_eq_single i]
    · rw [projector_eq_self ρ (χ i) hcard (v i) (heigen i)]
    · intro j _ hji
      rw [projector_eq_zero_of_ne ρ (χ i) (χ j)
        (fun h => hji (hχ h).symm) (v j) (heigen j), smul_zero]
    · simp
  rw [hs] at hp
  exact (smul_eq_zero.mp hp).resolve_right (hv i)

/-- Every distinct occurring weight nontrivial at g contributes a moving
dimension for that actual group element. -/
theorem card_le_finrank_moving [FiniteDimensional k V]
    {ι : Type*} [Fintype ι] (hcard : (Fintype.card U : k) ≠ 0)
    (χ : ι → U →* kˣ) (hχ : Function.Injective χ)
    (v : ι → V) (hv : ∀ i, v i ≠ 0)
    (heigen : ∀ i g, ρ g (v i) = (χ i g : k) • v i)
    (g : U) (hg : ∀ i, χ i g ≠ 1) :
    Fintype.card ι ≤ Module.finrank k (LinearMap.range (ρ g - LinearMap.id)) := by
  apply FinitePermutationMovingRank.card_le_finrank_of_eigenvectors
    (ρ g) v (linearIndependent_of_characters ρ hcard χ hχ v hv heigen)
    (fun i => (χ i g : k))
  · intro i h
    apply hg i
    exact Units.ext h
  · intro i
    exact heigen i g

end Kourovka2135.CharacterWeightIndependence

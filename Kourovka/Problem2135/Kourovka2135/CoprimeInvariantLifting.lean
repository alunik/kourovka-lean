import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Intertwining

/-! Lifting invariant vectors through an actual surjective intertwining map.

An explicit average supplies an invariant preimage when the finite group order
is nonzero in the coefficient field. There are no finite-dimensionality or
irreducibility assumptions on either representation.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.CoprimeInvariantLifting

variable {k G V W : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (τ : Representation k G W)

/-- The actual linear map on invariant vectors induced by an intertwiner. -/
def invariantMap (f : ρ.IntertwiningMap τ) : ρ.invariants →ₗ[k] τ.invariants where
  toFun v := ⟨f v.val, by
    intro g
    have h := LinearMap.congr_fun (f.isIntertwining' g) v.val
    change f (ρ g v.val) = τ g (f v.val) at h
    rw [v.property g] at h
    exact h.symm⟩
  map_add' v w := Subtype.ext (map_add f v.val w.val)
  map_smul' c v := Subtype.ext (map_smul f c v.val)

@[simp] theorem invariantMap_apply (f : ρ.IntertwiningMap τ) (v : ρ.invariants) :
    (invariantMap ρ τ f v).val = f v.val := rfl

variable [Fintype G]

/-- The explicit Reynolds average, with scalar inverse in the coefficient field. -/
def average : V →ₗ[k] V := (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g

@[simp] theorem average_apply (v : V) :
    average ρ v = (Fintype.card G : k)⁻¹ • ∑ g : G, ρ g v := by
  simp [average]

/-- Left multiplication permutes the terms of the average. -/
theorem average_mem_invariants (v : V) : average ρ v ∈ ρ.invariants := by
  classical
  intro g
  calc
    ρ g (average ρ v) = (Fintype.card G : k)⁻¹ • ∑ h : G, ρ (g * h) v := by
      rw [average_apply, map_smul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro h _
      rw [map_mul]
      rfl
    _ = average ρ v := by
      rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => ρ h v)]
      exact (average_apply ρ v).symm

/-- If the group order is invertible, averaging fixes every invariant vector. -/
theorem average_eq_self (hcard : (Fintype.card G : k) ≠ 0)
    (v : V) (hv : v ∈ ρ.invariants) : average ρ v = v := by
  rw [Representation.mem_invariants] at hv
  rw [average_apply]
  simp only [hv, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul k _ v, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Averaging commutes with any actual intertwining map. -/
theorem intertwining_average (f : ρ.IntertwiningMap τ) (v : V) :
    f (average ρ v) = average τ (f v) := by
  rw [average_apply, map_smul, map_sum, average_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact LinearMap.congr_fun (f.isIntertwining' g) v

/-- Surjectivity survives passage to fixed vectors for a coprime-order group. -/
theorem invariantMap_surjective (hcard : (Fintype.card G : k) ≠ 0)
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Surjective (invariantMap ρ τ f) := by
  intro w
  obtain ⟨v, hv⟩ := hf w.val
  refine ⟨⟨average ρ v, average_mem_invariants ρ v⟩, ?_⟩
  apply Subtype.ext
  change f (average ρ v) = w.val
  rw [intertwining_average, hv, average_eq_self τ hcard w.val w.property]

/-- An invariant target vector has an actual invariant preimage. -/
theorem exists_invariant_preimage (hcard : (Fintype.card G : k) ≠ 0)
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f)
    (w : W) (hw : w ∈ τ.invariants) :
    ∃ v : V, v ∈ ρ.invariants ∧ f v = w := by
  obtain ⟨v, hv⟩ := invariantMap_surjective ρ τ hcard f hf ⟨w, hw⟩
  exact ⟨v.val, v.property, congrArg Subtype.val hv⟩

/-- If the quotient kills every invariant vector of the source, it has no
invariant vectors of its own. -/
theorem invariants_eq_bot_of_le_ker (hcard : (Fintype.card G : k) ≠ 0)
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f)
    (hker : ρ.invariants ≤ LinearMap.ker f.toLinearMap) : τ.invariants = ⊥ := by
  apply bot_unique
  intro w hw
  change w = 0
  obtain ⟨v, hv, hfv⟩ := exists_invariant_preimage ρ τ hcard f hf w hw
  exact hfv.symm.trans (hker hv)

/-- A quotient of a representation with no invariants also has no invariants. -/
theorem invariants_eq_bot_of_surjective (hcard : (Fintype.card G : k) ≠ 0)
    (f : ρ.IntertwiningMap τ) (hf : Function.Surjective f)
    (hinv : ρ.invariants = ⊥) : τ.invariants = ⊥ := by
  apply bot_unique
  intro w hw
  change w = 0
  obtain ⟨v, hv, hfv⟩ := exists_invariant_preimage ρ τ hcard f hf w hw
  have hvzero : v = 0 := by
    rw [hinv] at hv
    exact hv
  rw [hvzero, map_zero] at hfv
  exact hfv.symm

end Kourovka2135.CoprimeInvariantLifting

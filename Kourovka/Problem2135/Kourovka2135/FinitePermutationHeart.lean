import Kourovka2135.FinitePermutationAugmentation
import Kourovka2135.CoprimeInvariantLifting
import Mathlib.LinearAlgebra.Quotient.Basic

/-! The actual permutation heart in the case where the coefficient
characteristic divides the number of points. A subgroup transitive away from
one point fixes exactly the constant line in the augmentation module. If its
order is invertible, the actual quotient heart has no fixed vector. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.FinitePermutationHeart
open FinitePermutationAugmentation

variable (k G X : Type u) [Field k] [Group G] [Fintype X] [MulAction G X]
variable (hcard : (Fintype.card X : k) = 0)

def constants : k →ₗ[k] Space k X where
  toFun c := ⟨fun _ => c, by
    change (∑ _ : X, c) = 0
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, hcard, zero_smul]⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem constants_apply (c : k) (x : X) :
    (constants k X hcard c : X → k) x = c := rfl

abbrev constantLine : Submodule k (Space k X) := LinearMap.range (constants k X hcard)

theorem action_constants (g : G) (c : k) :
    action k G X g (constants k X hcard c) = constants k X hcard c := Subtype.ext rfl

theorem constantLine_stable (g : G) :
    constantLine k X hcard ≤ (constantLine k X hcard).comap (action k G X g) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨c, (action_constants k G X hcard g c).symm⟩

abbrev Heart := Space k X ⧸ constantLine k X hcard

def representation : Representation k G (Heart k X hcard) :=
  Representation.quotient (action k G X) (constantLine k X hcard)
    (constantLine_stable k G X hcard)

def quotientHom : Representation.IntertwiningMap (action k G X)
    (representation k G X hcard) where
  toLinearMap := (constantLine k X hcard).mkQ
  isIntertwining' _ := LinearMap.ext (fun _ => rfl)

theorem quotientHom_surjective : Function.Surjective (quotientHom k G X hcard) :=
  (constantLine k X hcard).mkQ_surjective

variable (U : Subgroup G) (x₀ : X)

/-- Two orbits suffice; the second orbit is the complement of the base point. -/
theorem invariants_le_constantLine [Nontrivial X]
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Representation.invariants ((action k G X).comp U.subtype) ≤ constantLine k X hcard := by
  classical
  intro f hf
  obtain ⟨x₁, hx₁⟩ := exists_ne x₀
  let c : k := (f : X → k) x₁
  have hother : ∀ x : X, x ≠ x₀ → (f : X → k) x = c := by
    intro x hx
    obtain ⟨g, hg⟩ := htrans x₁ x hx₁ hx
    have he := congrArg (fun a : Space k X => (a : X → k) x₁) (hf g⁻¹)
    change (f : X → k) (((g⁻¹ : U) : G)⁻¹ • x₁) = c at he
    simpa only [InvMemClass.coe_inv, inv_inv, hg] using he
  have hdecomp : (f : X → k) = (constants k X hcard c : X → k) +
      ((f : X → k) x₀ - c) • delta k X x₀ := by
    funext x
    by_cases hx : x = x₀
    · subst x
      simp [delta, constants]
    · simp [delta, constants, hx, hother x hx]
  have hbase : (f : X → k) x₀ = c := by
    have he := congrArg (augmentation k X) hdecomp
    rw [map_add, map_smul, augmentation_delta,
      show augmentation k X (f : X → k) = 0 from f.property,
      show augmentation k X (constants k X hcard c : X → k) = 0 from
        (constants k X hcard c).property,
      zero_add, smul_eq_mul, mul_one] at he
    exact sub_eq_zero.mp he.symm
  refine ⟨c, ?_⟩
  apply Subtype.ext
  funext x
  change c = (f : X → k) x
  by_cases hx : x = x₀
  · simpa only [hx] using hbase.symm
  · exact (hother x hx).symm

/-- Averaging lifts fixed vectors through the actual heart quotient. -/
theorem heart_invariants_eq_bot [Nontrivial X] [Fintype U]
    (horder : (Fintype.card U : k) ≠ 0)
    (htrans : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃ g : U, (g : G) • x = y) :
    Representation.invariants ((representation k G X hcard).comp U.subtype) = ⊥ := by
  let f : Representation.IntertwiningMap ((action k G X).comp U.subtype)
      ((representation k G X hcard).comp U.subtype) :=
    ⟨(constantLine k X hcard).mkQ, fun _ => LinearMap.ext (fun _ => rfl)⟩
  apply CoprimeInvariantLifting.invariants_eq_bot_of_le_ker
    ((action k G X).comp U.subtype)
    ((representation k G X hcard).comp U.subtype) horder f
    ((constantLine k X hcard).mkQ_surjective)
  change Representation.invariants ((action k G X).comp U.subtype) ≤
    LinearMap.ker (constantLine k X hcard).mkQ
  rw [Submodule.ker_mkQ]
  exact invariants_le_constantLine k G X hcard U x₀ htrans

end Kourovka2135.FinitePermutationHeart

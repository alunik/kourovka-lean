import Kourovka2135.AbelianCommutatorFiber
import Kourovka2135.MinimalCharacterEquivalence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Nontrivial linear characters have zero average on the actual commutator
corrections. The normal kernel may be nonabelian: only the character values
commute. No character orthogonality, correction surjectivity, or invariant
character premise is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.LinearCharacterCorrectionAverage

open scoped BigOperators commutatorElement
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {G B : Type*} [Group G] [CommGroup B]
variable (N : Subgroup G) [N.Normal] (χ : N →* B)

/-- The actual ambient stabilizer of a unit-valued linear character. -/
def conjugationStabilizer : Subgroup G where
  carrier := {g | ∀ n : N, χ (MulAut.conjNormal g n) = χ n}
  one_mem' := by intro n; simp
  mul_mem' := by
    intro g h hg hh n
    rw [map_mul, MulAut.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg n
    have h := hg (MulAut.conjNormal g⁻¹ n)
    have hc : MulAut.conjNormal g (MulAut.conjNormal g⁻¹ n) = n := by
      rw [map_inv]
      exact (MulAut.conjNormal g).apply_symm_apply n
    rw [hc] at h
    exact h.symm

@[simp] theorem mem_conjugationStabilizer (g : G) :
    g ∈ conjugationStabilizer N χ ↔
      ∀ n : N, χ (MulAut.conjNormal g n) = χ n := Iff.rfl

/-- The first actual character factor in the commutator correction. -/
def firstDifference (a b : G) : N →* B where
  toFun u := (χ (MulAut.conjNormal (paperCommutator a b)⁻¹ u))⁻¹ *
    χ (MulAut.conjNormal b⁻¹ u)
  map_one' := by simp
  map_mul' u v := by simp [mul_assoc, mul_left_comm, mul_comm]

/-- The second actual character factor in the commutator correction. -/
def secondDifference (a b : G) : N →* B where
  toFun v := (χ (MulAut.conjNormal (a * paperCommutator a b)⁻¹ v))⁻¹ * χ v
  map_one' := by simp
  map_mul' u v := by simp [mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem firstDifference_apply (a b : G) (u : N) :
    firstDifference N χ a b u =
      (χ (MulAut.conjNormal (paperCommutator a b)⁻¹ u))⁻¹ *
        χ (MulAut.conjNormal b⁻¹ u) := rfl

@[simp] theorem secondDifference_apply (a b : G) (v : N) :
    secondDifference N χ a b v =
      (χ (MulAut.conjNormal (a * paperCommutator a b)⁻¹ v))⁻¹ * χ v := rfl

/-- The factorization is valid for nonabelian N because the target is commutative. -/
theorem correction_factor (a b : G) (u v : N) :
    χ (abelianCorrection N a b u v) =
      firstDifference N χ a b u * secondDifference N χ a b v := by
  simp only [abelianCorrection, map_mul, map_inv, firstDifference_apply,
    secondDifference_apply]
  ac_rfl

/-- Triviality of the first factor forces invariance under the first corrected generator. -/
theorem first_corrected_mem_stabilizer (a b : G)
    (hfirst : firstDifference N χ a b = 1) :
    ((paperCommutator a b)⁻¹ * b)⁻¹ ∈ conjugationStabilizer N χ := by
  intro n
  let c := paperCommutator a b
  have h := congrArg (fun ψ : N →* B => ψ (MulAut.conjNormal c n)) hfirst
  change (χ (MulAut.conjNormal c⁻¹ (MulAut.conjNormal c n)))⁻¹ *
    χ (MulAut.conjNormal b⁻¹ (MulAut.conjNormal c n)) = 1 at h
  have hc : MulAut.conjNormal c⁻¹ (MulAut.conjNormal c n) = n := by
    rw [map_inv]
    exact (MulAut.conjNormal c).symm_apply_apply n
  have hb : MulAut.conjNormal b⁻¹ (MulAut.conjNormal c n) =
      MulAut.conjNormal (c⁻¹ * b)⁻¹ n := by
    rw [← MulAut.mul_apply, ← map_mul]
    simp only [mul_inv_rev, inv_inv]
  rw [hc, hb] at h
  exact (eq_of_inv_mul_eq_one h).symm

/-- Triviality of the second factor forces invariance under the second corrected generator. -/
theorem second_corrected_mem_stabilizer (a b : G)
    (hsecond : secondDifference N χ a b = 1) :
    (a * paperCommutator a b)⁻¹ ∈ conjugationStabilizer N χ := by
  intro n
  have h := congrArg (fun ψ : N →* B => ψ n) hsecond
  change (χ (MulAut.conjNormal (a * paperCommutator a b)⁻¹ n))⁻¹ * χ n = 1 at h
  exact eq_of_inv_mul_eq_one h

/-- At least one actual factor is nontrivial when [N,G]=N and a,b generate G. -/
theorem difference_ne_one_or (hχ : χ ≠ 1)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    firstDifference N χ a b ≠ 1 ∨ secondDifference N χ a b ≠ 1 := by
  by_cases hfirst : firstDifference N χ a b = 1
  · right
    intro hsecond
    have hpair : Subgroup.closure
        ({((paperCommutator a b)⁻¹ * b)⁻¹,
          (a * paperCommutator a b)⁻¹} : Set G) = ⊤ := by
      rw [closure_inverse_pair, closure_commutator_correction_pair, hgen]
    have hle : Subgroup.closure
        ({((paperCommutator a b)⁻¹ * b)⁻¹,
          (a * paperCommutator a b)⁻¹} : Set G) ≤ conjugationStabilizer N χ := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact first_corrected_mem_stabilizer N χ a b hfirst
      · have heq := Set.mem_singleton_iff.mp hx
        subst x
        exact second_corrected_mem_stabilizer N χ a b hsecond
    rw [hpair] at hle
    exact hχ (MinimalCharacterEquivalence.conjugationInvariantHom_eq_one_of_moving
      N hmove χ (fun g => hle (Subgroup.mem_top g)))
  · exact Or.inl hfirst

/-- Translation by an element with nontrivial character value kills the finite sum. -/
theorem sum_unitHom_eq_zero {A k : Type*} [Group A] [Finite A] [Field k]
    (ψ : A →* kˣ) (hψ : ψ ≠ 1) : ∑ x : A, (ψ x : k) = 0 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hψ
  have hx' : (ψ x : k) ≠ 1 := by
    intro h
    apply hx
    exact Units.ext h
  have hsum : ∑ y : A, (ψ (x * y) : k) = ∑ y : A, (ψ y : k) :=
    Fintype.sum_bijective _ (Equiv.mulLeft x).bijective _ _ (fun _ => rfl)
  simp only [map_mul, Units.val_mul] at hsum
  rw [← Finset.mul_sum] at hsum
  exact eq_zero_of_mul_eq_self_left hx' hsum

/-- The raw double sum factors into the two actual finite character sums. -/
theorem correction_sum_factor {k : Type*} [Field k] [Finite N]
    (χ : N →* kˣ) (a b : G) :
    (∑ u : N, ∑ v : N, (χ (abelianCorrection N a b u v) : k)) =
      (∑ u : N, (firstDifference N χ a b u : k)) *
        (∑ v : N, (secondDifference N χ a b v : k)) := by
  rw [Fintype.sum_mul_sum]
  simp only [correction_factor, Units.val_mul]

/-- Every nontrivial linear character has zero average over the actual
commutator corrections for a generating pair and a moving normal subgroup. -/
theorem correction_sum_eq_zero {k : Type*} [Field k] [Finite N]
    (χ : N →* kˣ) (hχ : χ ≠ 1)
    (hmove : ⁅N, (⊤ : Subgroup G)⁆ = N)
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    ∑ u : N, ∑ v : N, (χ (abelianCorrection N a b u v) : k) = 0 := by
  rw [correction_sum_factor]
  rcases difference_ne_one_or N χ hχ hmove a b hgen with hfirst | hsecond
  · rw [sum_unitHom_eq_zero (firstDifference N χ a b) hfirst, zero_mul]
  · rw [sum_unitHom_eq_zero (secondDifference N χ a b) hsecond, mul_zero]

end Kourovka2135.LinearCharacterCorrectionAverage

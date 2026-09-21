import Kourovka2135.SLTwoUnipotent
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Ring.Commute

/-! Nonzero unipotent fixed vectors without finite-dimensionality.

A finite commuting family of square-zero operators has a nonzero common
kernel. Applied to the differences from identity of binary additive-group
actions, this gives fixed vectors in any nonzero representation or stable
subspace, and invariant functionals in the algebraic dual.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SLTwoUnipotentInvariants

section CommonKernel

variable {R : Type u} [Semiring R] {V : Type v} [AddCommMonoid V] [Module R V]
variable [Nontrivial V] {ι : Type w}

/-- Finite commuting square-zero operators have a nonzero simultaneous kernel. -/
theorem exists_nonzero_common_kernel (S : Finset ι) (D : ι → Module.End R V)
    (hsq : ∀ i ∈ S, D i * D i = 0)
    (hcomm : ∀ i ∈ S, ∀ j ∈ S, Commute (D i) (D j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i ∈ S, D i v = 0 := by
  classical
  revert hsq hcomm
  induction S using Finset.induction_on with
  | empty =>
      intro _ _
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, by simp⟩
  | @insert i S hi ih =>
      intro hsq hcomm
      obtain ⟨v, hv, hker⟩ := ih
        (fun j hj => hsq j (Finset.mem_insert_of_mem hj))
        (fun j hj l hl => hcomm j (Finset.mem_insert_of_mem hj)
          l (Finset.mem_insert_of_mem hl))
      by_cases hvi : D i v = 0
      · refine ⟨v, hv, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hvi
        · exact hker j hj
      · refine ⟨D i v, hvi, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact LinearMap.congr_fun (hsq j (Finset.mem_insert_self j S)) v
        · calc
            D j (D i v) = D i (D j v) :=
              LinearMap.congr_fun
                (hcomm j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i S)).eq v
            _ = 0 := by rw [hker j hj, map_zero]

end CommonKernel

section Additive

variable {k : Type u} [Field k] {F : Type v} [Field F]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The nilpotent difference associated to an additive parameter. -/
def additiveDifference (ρ : Representation k (Multiplicative F) V) (t : F) :
    Module.End k V := ρ (Multiplicative.ofAdd t) - 1

/-- Differences commute because the additive parameter group is abelian. -/
theorem additiveDifference_commute (ρ : Representation k (Multiplicative F) V) (s t : F) :
    Commute (additiveDifference ρ s) (additiveDifference ρ t) := by
  have h : Commute (ρ (Multiplicative.ofAdd s)) (ρ (Multiplicative.ofAdd t)) :=
    (Commute.all (Multiplicative.ofAdd s) (Multiplicative.ofAdd t)).map ρ
  exact (h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)

variable [CharP k 2] [CharP F 2] [Nontrivial V]

/-- In characteristic two each difference from an involution is square-zero. -/
theorem additiveDifference_mul_self (ρ : Representation k (Multiplicative F) V) (t : F) :
    additiveDifference ρ t * additiveDifference ρ t = 0 := by
  let : CharP (Module.End k V) 2 :=
    charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective 2
  have ht : Multiplicative.ofAdd t * Multiplicative.ofAdd t = (1 : Multiplicative F) := by
    change Multiplicative.ofAdd (t + t) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero]
  have hs : ρ (Multiplicative.ofAdd t) * ρ (Multiplicative.ofAdd t) = 1 := by
    rw [← map_mul, ht, map_one]
  change (ρ (Multiplicative.ofAdd t) - 1) * (ρ (Multiplicative.ofAdd t) - 1) = 0
  rw [← pow_two, sub_pow_char_of_commute (p := 2) (Commute.one_right _)]
  simp only [pow_two, one_mul, hs, sub_self]

/-- Every nonzero binary additive-group representation has a nonzero fixed vector. -/
theorem exists_nonzero_additive_fixed [Finite F]
    (ρ : Representation k (Multiplicative F) V) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : F, ρ (Multiplicative.ofAdd t) v = v := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨v, hv, hker⟩ := exists_nonzero_common_kernel Finset.univ (additiveDifference ρ)
    (fun t _ => additiveDifference_mul_self ρ t)
    (fun s _ t _ => additiveDifference_commute ρ s t)
  refine ⟨v, hv, ?_⟩
  intro t
  have h := hker t (Finset.mem_univ t)
  change ρ (Multiplicative.ofAdd t) v - v = 0 at h
  exact sub_eq_zero.mp h

end Additive

section SLTwo

variable {k : Type u} [Field k] [CharP k 2]
variable {F : Type v} [Field F] [CharP F 2] [Finite F]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- The upper-unipotent subgroup fixes a nonzero vector in every nonzero SL2 module. -/
theorem exists_nonzero_unipotent_fixed [Nontrivial V]
    (ρ : Representation k (SLTwo.SL2 F) V) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : F, ρ (SLTwo.uni t) v = v := by
  exact exists_nonzero_additive_fixed (ρ.comp (SLTwo.uniHom F))

/-- Only upper-unipotent stability of the chosen nonzero subspace is required. -/
theorem exists_nonzero_unipotent_fixed_mem
    (ρ : Representation k (SLTwo.SL2 F) V) (W : Submodule k V) (hW : W ≠ ⊥)
    (hstable : ∀ (t : F) (v : V), v ∈ W → ρ (SLTwo.uni t) v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∀ t : F, ρ (SLTwo.uni t) v = v := by
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let τ : Representation k (Multiplicative F) W :=
    Representation.subrepresentation (ρ.comp (SLTwo.uniHom F)) W
      (fun g v hv => hstable g.toAdd v hv)
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_additive_fixed τ
  refine ⟨v.val, v.property, ?_, ?_⟩
  · intro h
    exact hv (Subtype.ext h)
  · intro t
    exact congrArg Subtype.val (hfix t)

/-- The algebraic dual supplies a nonzero U-invariant linear functional. -/
theorem exists_nonzero_unipotent_invariant_functional [Nontrivial V]
    (ρ : Representation k (SLTwo.SL2 F) V) :
    ∃ ell : Module.Dual k V, ell ≠ 0 ∧
      ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v := by
  let : Nontrivial (Module.Dual k V) := (Module.nontrivial_dual_iff k).mpr inferInstance
  obtain ⟨ell, hell, hfix⟩ := exists_nonzero_unipotent_fixed ρ.dual
  refine ⟨ell, hell, ?_⟩
  intro t v
  have h := congrArg (fun l : Module.Dual k V => l (ρ (SLTwo.uni t) v)) (hfix t)
  change ell ((ρ ((SLTwo.uni t)⁻¹) * ρ (SLTwo.uni t)) v) = ell (ρ (SLTwo.uni t) v) at h
  rw [← map_mul, inv_mul_cancel, map_one] at h
  exact h.symm

end SLTwo

end Kourovka2135.SLTwoUnipotentInvariants

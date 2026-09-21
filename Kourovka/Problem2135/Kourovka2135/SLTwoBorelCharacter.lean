import Kourovka2135.SLTwoUnipotentInvariants
import Kourovka2135.EmbeddedFieldEigenvector
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Actual Borel-character functionals over an embedded finite binary field.

The torus acts by precomposition on the native space of upper-unipotent
invariant algebraic-dual functionals. A split-annihilator eigenvector and a
cyclic generator yield a character with the negative exponent convention
needed for the homogeneous-function embedding. No finite-dimensionality,
algebraic closure, irreducibility, or classification premise is used.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.SLTwoBorelCharacter

section Operators
variable {k : Type u} [Field k] {F : Type v} [Field F]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (SLTwo.SL2 F) V)

/-- The native subspace of upper-unipotent invariant linear functionals. -/
def invariantDual : Submodule k (Module.Dual k V) where
  carrier := {ell | ∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v}
  zero_mem' := by intro t v; rfl
  add_mem' := by
    intro ell ell' hell hell' t v
    change ell (ρ (SLTwo.uni t) v) + ell' (ρ (SLTwo.uni t) v) = ell v + ell' v
    rw [hell, hell']
  smul_mem' := by
    intro c ell hell t v
    change c * ell (ρ (SLTwo.uni t) v) = c * ell v
    rw [hell]

/-- The exact conjugation identity in the form used by precomposition. -/
theorem tor_uni_mul (a : Fˣ) (t : F) :
    SLTwo.tor a * SLTwo.uni t = SLTwo.uni ((a : F) ^ 2 * t) * SLTwo.tor a := by
  have h := congrArg (fun g : SLTwo.SL2 F => g * SLTwo.tor a) (SLTwo.tor_conj_uni a t)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- Forward torus precomposition preserves the actual invariant-dual subspace. -/
def torusOperator (a : Fˣ) : Module.End k (invariantDual ρ) where
  toFun ell :=
    ⟨ell.val.comp (ρ (SLTwo.tor a)), by
      intro t v
      change ell.val (ρ (SLTwo.tor a) (ρ (SLTwo.uni t) v)) = ell.val (ρ (SLTwo.tor a) v)
      calc
        _ = ell.val (ρ (SLTwo.tor a * SLTwo.uni t) v) :=
          congrArg (fun T : Module.End k V => ell.val (T v)) (ρ.map_mul _ _).symm
        _ = ell.val (ρ (SLTwo.uni ((a : F) ^ 2 * t) * SLTwo.tor a) v) :=
          congrArg (fun g : SLTwo.SL2 F => ell.val (ρ g v)) (tor_uni_mul a t)
        _ = ell.val (ρ (SLTwo.uni ((a : F) ^ 2 * t)) (ρ (SLTwo.tor a) v)) :=
          congrArg (fun T : Module.End k V => ell.val (T v)) (ρ.map_mul _ _)
        _ = ell.val (ρ (SLTwo.tor a) v) := ell.property _ _⟩
  map_add' ell ell' := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl
  map_smul' c ell := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    rfl

@[simp] theorem torusOperator_apply (a : Fˣ) (ell : invariantDual ρ) (v : V) :
    (torusOperator ρ a ell).val v = ell.val (ρ (SLTwo.tor a) v) := rfl

@[simp] theorem torusOperator_one : torusOperator ρ (1 : Fˣ) = 1 := by
  apply LinearMap.ext
  intro ell
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ell.val (ρ (SLTwo.tor 1) v) = ell.val v
  have ht : SLTwo.tor (1 : Fˣ) = 1 := (SLTwo.torHom F).map_one
  rw [ht, map_one]
  rfl

/-- Precomposition reverses composition, and the torus is commutative. -/
theorem torusOperator_mul (a b : Fˣ) :
    torusOperator ρ (a * b) = torusOperator ρ a * torusOperator ρ b := by
  apply LinearMap.ext
  intro ell
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ell.val (ρ (SLTwo.tor (a * b)) v) =
    ell.val (ρ (SLTwo.tor b) (ρ (SLTwo.tor a) v))
  have hab : SLTwo.tor (a * b) = SLTwo.tor b * SLTwo.tor a := by
    rw [mul_comm a b]
    exact (SLTwo.torHom F).map_mul b a
  rw [hab, map_mul]
  rfl

/-- The genuine torus representation on invariant algebraic-dual functionals. -/
def torusAction : Representation k Fˣ (invariantDual ρ) where
  toFun := torusOperator ρ
  map_one' := torusOperator_one ρ
  map_mul' := torusOperator_mul ρ

@[simp] theorem torusAction_apply (a : Fˣ) (ell : invariantDual ρ) (v : V) :
    (torusAction ρ a ell).val v = ell.val (ρ (SLTwo.tor a) v) := rfl

/-- The actual finite torus action satisfies the split finite-field annihilator. -/
theorem torusAction_pow_card_sub_one [Fintype F] (a : Fˣ) :
    torusAction ρ a ^ (Fintype.card F - 1) = 1 := by
  classical
  have ha : a ^ (Fintype.card F - 1) = 1 := by
    rw [← Fintype.card_units]
    exact pow_card_eq_one
  rw [← map_pow, ha, map_one]

end Operators

section Nonzero
variable {k : Type u} [Field k] [CharP k 2]
variable {F : Type v} [Field F] [CharP F 2] [Finite F]
variable {V : Type w} [AddCommGroup V] [Module k V] [Nontrivial V]
variable (ρ : Representation k (SLTwo.SL2 F) V)

/-- The invariant-dual space is nonzero for every nonzero binary SL2 module. -/
theorem invariantDual_ne_bot : invariantDual ρ ≠ ⊥ := by
  obtain ⟨ell, hell, hfix⟩ :=
    SLTwoUnipotentInvariants.exists_nonzero_unipotent_invariant_functional ρ
  intro h
  have hm : ell ∈ invariantDual ρ := hfix
  rw [h, Submodule.mem_bot] at hm
  exact hell hm

/-- Nontriviality needed for the split-annihilator eigenvector theorem. -/
theorem nontrivial_invariantDual : Nontrivial (invariantDual ρ) :=
  Submodule.nontrivial_iff_ne_bot.mpr (invariantDual_ne_bot ρ)

end Nonzero

section Character
variable {k : Type u} [Field k] [CharP k 2]
variable {F : Type v} [Field F] [CharP F 2] [Fintype F]
variable {V : Type w} [AddCommGroup V] [Module k V] [Nontrivial V]
variable (σ : F →+* k) (ρ : Representation k (SLTwo.SL2 F) V)

/-- Every nonzero representation has an actual nonzero Borel-character
functional, with the negative exponent required by homogeneous functions. -/
theorem exists_borel_character :
    ∃ n : ℕ, n < Fintype.card F - 1 ∧
      ∃ ell : Module.Dual k V, ell ≠ 0 ∧
        (∀ (t : F) (v : V), ell (ρ (SLTwo.uni t) v) = ell v) ∧
        (∀ (a : Fˣ) (v : V),
          ell (ρ (SLTwo.tor a) v) = σ ((a⁻¹ : Fˣ) : F) ^ n * ell v) := by
  classical
  have : Nontrivial (invariantDual ρ) := nontrivial_invariantDual ρ
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf r = Fintype.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hr, Nat.card_eq_fintype_card, Fintype.card_units]
  obtain ⟨b, ell, hell, he⟩ :=
    EmbeddedFieldEigenvector.exists_unit_eigenvector_of_pow_card_sub_one
      (V := ↥(invariantDual ρ)) σ (torusAction ρ r) (torusAction_pow_card_sub_one ρ r)
  obtain ⟨n, hn, hnb⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp (hr b⁻¹))
  have hn' : n < Fintype.card F - 1 := by
    simpa only [hord] using Finset.mem_range.mp hn
  have hb : b = (r⁻¹) ^ n := by
    rw [inv_pow, hnb, inv_inv]
  have hve : Module.End.HasEigenvector (torusAction ρ r) (σ (b : F)) ell :=
    ⟨Module.End.mem_eigenspace_iff.mpr he, hell⟩
  refine ⟨n, hn', ell.val, ?_, ell.property, ?_⟩
  · intro h
    exact hell (Subtype.ext h)
  · intro a v
    obtain ⟨m, _, hma⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp (hr a))
    have hbm : b ^ m = (a⁻¹) ^ n := by
      calc
        b ^ m = ((r⁻¹) ^ n) ^ m := by rw [hb]
        _ = ((r⁻¹) ^ m) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n m]
        _ = (a⁻¹) ^ n := by rw [inv_pow, hma]
    have hs : σ (b : F) ^ m = σ ((a⁻¹ : Fˣ) : F) ^ n := by
      calc
        σ (b : F) ^ m = σ ((b ^ m : Fˣ) : F) := by simp
        _ = σ (((a⁻¹) ^ n : Fˣ) : F) := congrArg (fun x : Fˣ => σ (x : F)) hbm
        _ = _ := by simp
    have hp := hve.pow_apply m
    rw [← map_pow, hma, hs] at hp
    have hv := congrArg (fun l : invariantDual ρ => l.val v) hp
    change ell.val (ρ (SLTwo.tor a) v) = σ ((a⁻¹ : Fˣ) : F) ^ n * ell.val v at hv
    exact hv

end Character
end Kourovka2135.SLTwoBorelCharacter

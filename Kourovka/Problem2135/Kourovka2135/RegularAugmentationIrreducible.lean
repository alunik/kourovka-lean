import Kourovka2135.PermutationAugmentationCocycles
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Sum

/-! A regular root orbit gives an irreducible binary augmentation module.

Everything is the actual permutation action on the kernel of coordinate sum.
The subgroup norm is computed explicitly; no representation classification,
semisimplicity, projectivity, or irreducibility premise is used.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.RegularAugmentationIrreducible

open FinitePermutationAugmentation
attribute [local instance] Classical.propDecidable

section Orbit
variable {G X : Type u} [Group G] [MulAction G X]
variable (U : Subgroup G) (x₀ : X)
variable (hfix : ∀ u : U, (u : G) • x₀ = x₀)
variable (hregular : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃! u : U, (u : G) • x = y)

include hfix in
theorem orbit_ne_base (y : X) (hy : y ≠ x₀) (a : U) : (a : G) • y ≠ x₀ := by
  intro h
  apply hy
  calc
    y = (a : G)⁻¹ • ((a : G) • y) := (inv_smul_smul (a : G) y).symm
    _ = x₀ := by rw [h]; exact hfix a⁻¹

include hfix hregular in
theorem orbit_injective (y : X) (hy : y ≠ x₀) :
    Function.Injective (fun a : U => (a : G) • y) := by
  intro a b hab
  exact (hregular y ((a : G) • y) hy (orbit_ne_base U x₀ hfix y hy a)).unique
    rfl hab.symm

/-- A genuine parametrization of all points by the root orbit and the fixed point. -/
def orbitSumEquiv (y : X) (hy : y ≠ x₀) : U ⊕ PUnit.{u + 1} ≃ X :=
  Equiv.ofBijective (Sum.elim (fun a : U => (a : G) • y) (fun _ => x₀)) (by
    constructor
    · intro a b hab
      cases a with
      | inl a =>
          cases b with
          | inl b => exact congrArg Sum.inl (orbit_injective U x₀ hfix hregular y hy hab)
          | inr b => exact (orbit_ne_base U x₀ hfix y hy a hab).elim
      | inr a =>
          cases b with
          | inl b => exact (orbit_ne_base U x₀ hfix y hy b hab.symm).elim
          | inr b => exact congrArg Sum.inr (Subsingleton.elim a b)
    · intro x
      by_cases hx : x = x₀
      · exact ⟨Sum.inr PUnit.unit, hx.symm⟩
      · obtain ⟨a, ha, _⟩ := hregular y x hy hx
        exact ⟨Sum.inl a, ha⟩)

/-- The orbit equivalence without the distinguished fixed point. -/
def orbitEquiv (y : X) (hy : y ≠ x₀) : U ≃ {x : X // x ≠ x₀} :=
  Equiv.ofBijective (fun a => ⟨(a : G) • y, orbit_ne_base U x₀ hfix y hy a⟩) (by
    constructor
    · intro a b hab
      exact orbit_injective U x₀ hfix hregular y hy (congrArg Subtype.val hab)
    · intro x
      obtain ⟨a, ha, _⟩ := hregular y x.val hy x.property
      exact ⟨a, Subtype.ext ha⟩)

variable [Fintype X] [Fintype U]
variable {k : Type u} [Field k]

include hfix hregular in
theorem sum_orbit_add (y : X) (hy : y ≠ x₀) (f : X → k) :
    (∑ a : U, f ((a : G) • y)) + f x₀ = ∑ x : X, f x := by
  have h := (orbitSumEquiv U x₀ hfix hregular y hy).sum_comp f
  change (∑ a : U ⊕ PUnit.{u + 1}, f (Sum.elim (fun a : U => (a : G) • y)
    (fun _ => x₀) a)) = ∑ x : X, f x at h
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique, Sum.elim_inl, Sum.elim_inr] using h

include hfix hregular in
theorem card_subgroup_cast_zero (y : X) (hy : y ≠ x₀)
    (hcard : (Fintype.card X : k) = 1) : (Fintype.card U : k) = 0 := by
  have hn : Fintype.card U + 1 = Fintype.card X := by
    simpa using Fintype.card_congr (orbitSumEquiv U x₀ hfix hregular y hy)
  have hk : (Fintype.card U : k) + 1 = (Fintype.card X : k) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : k)) hn
  rw [hcard] at hk
  exact add_right_cancel (show (Fintype.card U : k) + 1 = 0 + 1 by simpa using hk)

end Orbit

section Augmentation
variable (k G X : Type u) [Field k] [CharP k 2] [Group G] [Fintype X] [MulAction G X]
variable (hcard : (Fintype.card X : k) = 1)

/-- The indicator of the complement of a point, as an actual augmentation vector. -/
def complementVector (x : X) : Space k X :=
  ⟨(fun _ => 1) - delta k X x, by
    change augmentation k X ((fun _ => 1) - delta k X x) = 0
    rw [map_sub, augmentation_delta]
    simp [augmentation, hcard]⟩

omit [CharP k 2] in
@[simp] theorem complementVector_apply (x y : X) :
    (complementVector k X hcard x : X → k) y = if y = x then 0 else 1 := by
  classical
  by_cases h : y = x <;> simp [complementVector, delta, h]

omit [CharP k 2] in
theorem action_complementVector (g : G) (x : X) :
    action k G X g (complementVector k X hcard x) =
      complementVector k X hcard (g • x) := by
  apply Subtype.ext
  change representation k G X g ((fun _ => 1) - delta k X x) = _
  rw [map_sub, delta_action]
  rfl

omit [CharP k 2] in
theorem difference_eq_complement_sub (x₀ x : X) :
    difference k X x₀ x =
      complementVector k X hcard x₀ - complementVector k X hcard x := by
  apply Subtype.ext
  change delta k X x - delta k X x₀ =
    ((fun _ => 1) - delta k X x₀) - ((fun _ => 1) - delta k X x)
  abel

variable (U : Subgroup G) [Fintype U] (x₀ : X)
variable (hfix : ∀ u : U, (u : G) • x₀ = x₀)
variable (hregular : ∀ x y : X, x ≠ x₀ → y ≠ x₀ → ∃! u : U, (u : G) • x = y)
variable (x₁ : X) (hx₁ : x₁ ≠ x₀)

include hfix hregular hx₁ in
/-- The actual root-group norm is a rank-one map on augmentation. -/
theorem norm_eq (f : Space k X) :
    (∑ a : U, action k G X (a : G) f) =
      (f : X → k) x₀ • complementVector k X hcard x₀ := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ a : U, (f : X → k) ((a : G)⁻¹ • x)) =
    (f : X → k) x₀ * (complementVector k X hcard x₀ : X → k) x
  by_cases hx : x = x₀
  · subst x
    have hc := card_subgroup_cast_zero U x₀ hfix hregular x₁ hx₁ hcard
    have hfi (a : U) : (a : G)⁻¹ • x₀ = x₀ := hfix a⁻¹
    simp only [hfi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc,
      zero_mul, complementVector_apply, ite_true, mul_zero]
  · rw [complementVector_apply, ite_eq_right hx, mul_one]
    have hi : (∑ a : U, (f : X → k) ((a : G)⁻¹ • x)) =
        ∑ a : U, (f : X → k) ((a : G) • x) := by
      simpa using Equiv.sum_comp (Equiv.inv U) (fun a : U => (f : X → k) ((a : G) • x))
    rw [hi]
    have hs := sum_orbit_add U x₀ hfix hregular x hx (f : X → k)
    have hz : (∑ y : X, (f : X → k) y) = 0 := f.property
    rw [hz] at hs
    exact (eq_neg_of_add_eq_zero_left hs).trans (CharTwo.neg_eq _)

variable (htrans : ∀ x : X, ∃ g : G, g • x₀ = x)

include hcard hfix hregular hx₁ htrans in
/-- The norm vector and its genuine G-translates span every nonzero stable subspace. -/
theorem eq_top_of_stable (W : Submodule k (Space k X))
    (hW : ∃ f ∈ W, f ≠ 0)
    (hstable : ∀ (g : G) (f : Space k X), f ∈ W → action k G X g f ∈ W) : W = ⊤ := by
  classical
  obtain ⟨f, hfW, hf⟩ := hW
  obtain ⟨x, hx⟩ : ∃ x : X, (f : X → k) x ≠ 0 := by
    by_contra hn
    apply hf
    apply Subtype.ext
    funext x
    exact not_ne_iff.mp (not_exists.mp hn x)
  obtain ⟨g, hg⟩ := htrans x
  let v := action k G X g⁻¹ f
  have hvW : v ∈ W := hstable g⁻¹ f hfW
  have hv : (v : X → k) x₀ ≠ 0 := by
    simpa [v, action_val, hg] using hx
  have hnorm : (v : X → k) x₀ • complementVector k X hcard x₀ ∈ W := by
    rw [← norm_eq k G X hcard U x₀ hfix hregular x₁ hx₁ v]
    exact W.sum_mem (fun a _ => hstable a v hvW)
  have hbase : complementVector k X hcard x₀ ∈ W := by
    have h := W.smul_mem ((v : X → k) x₀)⁻¹ hnorm
    simpa [smul_smul, hv] using h
  have hall (y : X) : complementVector k X hcard y ∈ W := by
    obtain ⟨a, ha⟩ := htrans y
    have h := hstable a _ hbase
    rwa [action_complementVector, ha] at h
  apply top_unique
  intro v _
  rw [← PermutationAugmentationCocycles.sum_smul_difference x₀ v]
  apply W.sum_mem
  intro y _
  apply W.smul_mem
  rw [difference_eq_complement_sub k X hcard]
  exact W.sub_mem hbase (hall y)

include hcard hfix hregular hx₁ htrans in
/-- Generic absolute irreducibility: the coefficient field is arbitrary of characteristic two. -/
theorem isIrreducible : (action k G X).IsIrreducible := by
  let ρ := action k G X
  have hbase : complementVector k X hcard x₀ ≠ 0 := by
    intro h
    have he := congrArg (fun v : Space k X => (v : X → k) x₁) h
    simp [hx₁] at he
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    apply hbase
    have hv : complementVector k X hcard x₀ ∈ (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [h]; trivial
    exact hv
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hex : ∃ v ∈ W.toSubmodule, v ≠ 0 := by
    by_contra h
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    by_contra hne
    exact h ⟨v, hv, hne⟩
  apply Subrepresentation.toSubmodule_injective
  exact eq_top_of_stable k G X hcard U x₀ hfix hregular x₁ hx₁ htrans
    W.toSubmodule hex (fun g _ hv => W.apply_mem_toSubmodule g hv)

end Augmentation
end Kourovka2135.RegularAugmentationIrreducible

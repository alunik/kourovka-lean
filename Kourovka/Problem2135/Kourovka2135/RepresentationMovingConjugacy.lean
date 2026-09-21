import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.OrderOfElement

/-! Moving ranks of actual representations are invariant under equivalence,
conjugacy, and powers coprime to the order of the group element. The power
argument identifies the actual fixed kernels; no semisimplicity or assumption
on the characteristic is used. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.RepresentationMovingConjugacy

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

theorem mem_ker_sub_id_iff (f : V →ₗ[k] V) (v : V) :
    v ∈ LinearMap.ker (f - LinearMap.id) ↔ f v = v := by
  change f v - v = 0 ↔ f v = v
  exact sub_eq_zero

/-- An actual intertwining linear equivalence maps one fixed kernel onto the other. -/
theorem ker_map_of_intertwining (e : V ≃ₗ[k] W)
    (f : V →ₗ[k] V) (h : W →ₗ[k] W)
    (he : ∀ v : V, e (f v) = h (e v)) :
    (LinearMap.ker (f - LinearMap.id)).map e.toLinearMap =
      LinearMap.ker (h - LinearMap.id) := by
  ext w
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    apply (mem_ker_sub_id_iff h (e v)).mpr
    rw [← he v, (mem_ker_sub_id_iff f v).mp hv]
  · intro hw
    refine Submodule.mem_map.mpr ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    apply (mem_ker_sub_id_iff f (e.symm w)).mpr
    apply e.injective
    rw [he, e.apply_symm_apply]
    exact (mem_ker_sub_id_iff h w).mp hw

/-- Equal fixed kernels up to an actual intertwiner give equal moving ranks. -/
theorem finrank_moving_eq_of_intertwining [FiniteDimensional k V]
    [FiniteDimensional k W] (e : V ≃ₗ[k] W)
    (f : V →ₗ[k] V) (h : W →ₗ[k] W)
    (he : ∀ v : V, e (f v) = h (e v)) :
    Module.finrank k (f - LinearMap.id).range =
      Module.finrank k (h - LinearMap.id).range := by
  have hk := e.finrank_map_eq (LinearMap.ker (f - LinearMap.id))
  rw [ker_map_of_intertwining e f h he] at hk
  have hf := (f - LinearMap.id).finrank_range_add_finrank_ker
  have hh := (h - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk, ← e.finrank_eq] at hh
  exact Nat.add_right_cancel (hf.trans hh.symm)

section Monoid
variable {G : Type*} [Monoid G]
variable (ρ : Representation k G V)

theorem apply_pow_eq_self (g : G) (n : ℕ) (v : V) (hv : ρ g v = v) :
    ρ (g ^ n) v = v := by
  rw [map_pow, Module.End.pow_apply]
  exact Function.iterate_fixed hv n

/-- Coprime powers have exactly the same fixed vectors. -/
theorem ker_moving_pow_eq (g : G) (n : ℕ) (hn : n.Coprime (orderOf g)) :
    LinearMap.ker (ρ (g ^ n) - LinearMap.id) =
      LinearMap.ker (ρ g - LinearMap.id) := by
  ext v
  rw [mem_ker_sub_id_iff, mem_ker_sub_id_iff]
  constructor
  · intro hv
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hn
    rw [← hm]
    exact apply_pow_eq_self ρ (g ^ n) m v hv
  · intro hv
    exact apply_pow_eq_self ρ g n v hv

theorem finrank_moving_pow_eq [FiniteDimensional k V]
    (g : G) (n : ℕ) (hn : n.Coprime (orderOf g)) :
    Module.finrank k (ρ (g ^ n) - LinearMap.id).range =
      Module.finrank k (ρ g - LinearMap.id).range := by
  have hp := (ρ (g ^ n) - LinearMap.id).finrank_range_add_finrank_ker
  have hg := (ρ g - LinearMap.id).finrank_range_add_finrank_ker
  rw [ker_moving_pow_eq ρ g n hn] at hp
  exact Nat.add_right_cancel (hp.trans hg.symm)

/-- Representation equivalence preserves the moving rank at each actual element. -/
theorem finrank_moving_eq_of_equiv [FiniteDimensional k V] [FiniteDimensional k W]
    (τ : Representation k G W) (e : Representation.Equiv ρ τ) (g : G) :
    Module.finrank k (ρ g - LinearMap.id).range =
      Module.finrank k (τ g - LinearMap.id).range :=
  finrank_moving_eq_of_intertwining e.toLinearEquiv (ρ g) (τ g)
    (fun v => LinearMap.congr_fun (e.isIntertwining' g) v)

end Monoid

section Group
variable {G : Type*} [Group G]
variable (ρ : Representation k G V)

def actionEquiv (g : G) : V ≃ₗ[k] V :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)

@[simp] theorem actionEquiv_toLinearMap (g : G) :
    (actionEquiv ρ g).toLinearMap = ρ g := by
  change (↑(ρ.asGroupHom g) : V →ₗ[k] V) = ρ g
  exact Representation.asGroupHom_apply ρ g

@[simp] theorem actionEquiv_apply (g : G) (v : V) :
    actionEquiv ρ g v = ρ g v := by
  change (actionEquiv ρ g).toLinearMap v = ρ g v
  rw [actionEquiv_toLinearMap]

/-- A conjugating group element supplies the actual coefficient intertwiner. -/
theorem actionEquiv_intertwines (c a b : G) (hc : c * a = b * c) (v : V) :
    actionEquiv ρ c (ρ a v) = ρ b (actionEquiv ρ c v) := by
  rw [actionEquiv_apply, actionEquiv_apply]
  change (ρ c * ρ a) v = (ρ b * ρ c) v
  rw [← map_mul, ← map_mul, hc]

theorem ker_map_of_semiconj (c a b : G) (hc : c * a = b * c) :
    (LinearMap.ker (ρ a - LinearMap.id)).map (actionEquiv ρ c).toLinearMap =
      LinearMap.ker (ρ b - LinearMap.id) :=
  ker_map_of_intertwining (actionEquiv ρ c) (ρ a) (ρ b)
    (actionEquiv_intertwines ρ c a b hc)

theorem finrank_moving_eq_of_isConj [FiniteDimensional k V]
    {a b : G} (h : IsConj a b) :
    Module.finrank k (ρ a - LinearMap.id).range =
      Module.finrank k (ρ b - LinearMap.id).range := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  exact finrank_moving_eq_of_intertwining (actionEquiv ρ c) (ρ a) (ρ b)
    (actionEquiv_intertwines ρ c a b (mul_inv_eq_iff_eq_mul.mp hc))

end Group

end Kourovka2135.RepresentationMovingConjugacy

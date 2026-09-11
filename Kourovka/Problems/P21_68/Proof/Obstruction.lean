import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Module.Torsion.Free

/-!
# The subgroup-index obstruction to monomiality

These elementary lemmas isolate the group-theoretic part of the counterexample.
In particular, a normal subgroup whose order is coprime to an inducing index
lies in the inducing subgroup.  The normal subgroup need not be a Sylow subgroup.
-/

namespace Kourovka.P21_68

variable {G H : Type*} [Group G] [Group H]

/-- The relative index of `L` in a normal subgroup `N`, multiplied by the index
of their join, is the index of `L`. -/
theorem relIndex_mul_sup_index_of_normal_right [Finite G]
    (N L : Subgroup G) [N.Normal] :
    L.relIndex N * (L ⊔ N).index = L.index := by
  have h₁ := Subgroup.relIndex_mul_index (H := N) (K := L ⊔ N) le_sup_right
  rw [Subgroup.relIndex_sup_right] at h₁
  have h₂ := Subgroup.relIndex_inf_mul_relIndex L N (⊤ : Subgroup G)
  have h₃ := Subgroup.relIndex_inf_mul_relIndex N L (⊤ : Subgroup G)
  simp only [inf_top_eq, Subgroup.relIndex_top_right] at h₂ h₃
  have heq : L.relIndex N * N.index = N.relIndex L * L.index := by
    rw [h₂, h₃, inf_comm]
  rw [← h₁] at heq
  have hn : N.relIndex L ≠ 0 := Subgroup.index_ne_zero_of_finite
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn)
  calc
    N.relIndex L * (L.relIndex N * (L ⊔ N).index) =
        L.relIndex N * (N.relIndex L * (L ⊔ N).index) := by ac_rfl
    _ = N.relIndex L * L.index := heq

/-- A normal subgroup of order coprime to the index of `L` lies in `L`. -/
theorem le_of_coprime_card_index [Finite G] (N L : Subgroup G) [N.Normal]
    (hcop : (Nat.card N).Coprime L.index) : N ≤ L := by
  apply Subgroup.relIndex_eq_one.mp
  apply Nat.eq_one_of_dvd_coprimes hcop (L.relIndex_dvd_card N)
  exact ⟨(L ⊔ N).index, (relIndex_mul_sup_index_of_normal_right N L).symm⟩

/-- A subgroup of index `2*m` contained in a subgroup of index `m` has relative
index two. -/
theorem relIndex_eq_two_of_index_eq_twice {I L : Subgroup G} {m : ℕ}
    (hLI : L ≤ I) (hm : m ≠ 0) (hI : I.index = m) (hL : L.index = 2 * m) :
    L.relIndex I = 2 := by
  have h := Subgroup.relIndex_mul_index hLI
  rw [hI, hL] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hm) h

/-- The index-two obstruction after projecting the inertia subgroup.  In the
application, `q` is the projection `A ⋊ H → H`. -/
theorem false_of_index_eq_twice {I L : Subgroup G} {m : ℕ}
    (q : I →* H) (hq : Function.Surjective q)
    (hker : q.ker ≤ L.subgroupOf I) (hLI : L ≤ I)
    (hm : m ≠ 0) (hI : I.index = m) (hL : L.index = 2 * m)
    (hH : ∀ K : Subgroup H, K.index ≠ 2) : False := by
  apply hH ((L.subgroupOf I).map q)
  rw [Subgroup.index_map_eq _ hq hker]
  exact relIndex_eq_two_of_index_eq_twice hLI hm hI hL

section Weights

variable {k V U X : Type*} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]

/-- The inertia subgroup of a linear character of a normal subgroup, with the
conjugation convention `n ↦ g*n*g⁻¹`. -/
def linearCharacterInertia (N : Subgroup G) [N.Normal] (weight : N →* kˣ) : Subgroup G where
  carrier := {g | ∀ n, weight (MulAut.conjNormal g n) = weight n}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh n
    rw [map_mul, MulAut.mul_apply, hg, hh]
  inv_mem' := by
    intro g hg n
    have h := hg (MulAut.conjNormal g⁻¹ n)
    simpa only [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply] using h.symm

/-- A linear character extending `weight` forces its subgroup to preserve `weight`. -/
theorem le_linearCharacterInertia (N L : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (θ : L →* kˣ) (weight : N →* kˣ)
    (hweight : θ.comp (Subgroup.inclusion hNL) = weight) :
    L ≤ linearCharacterInertia N weight := by
  intro g hg n
  rw [← hweight]
  change θ ((Subgroup.inclusion hNL) (MulAut.conjNormal g n)) =
    θ ((Subgroup.inclusion hNL) n)
  have heq : (Subgroup.inclusion hNL) (MulAut.conjNormal g n) =
      (⟨g, hg⟩ : L) * (Subgroup.inclusion hNL) n * (⟨g, hg⟩ : L)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [heq]
  simp

/-- Jointly faithful coordinate maps identify the character of a nonzero
eigenvector when the normal subgroup acts by scalars in each coordinate.
Neither a basis nor distinctness of the displayed characters is needed. -/
theorem exists_weight_eq_of_eigenvector (N L : Subgroup G)
    (hNL : N ≤ L) (ρ : Representation k G V)
    (coordinate : X → V →ₗ[k] U)
    (hcoordinate : ∀ v, (∀ x, coordinate x v = 0) → v = 0)
    (weight : X → N →* kˣ)
    (hscalar : ∀ (n : N) x v, coordinate x (ρ n v) = (weight x n : k) • coordinate x v)
    (θ : L →* kˣ) (v : V) (hv : v ≠ 0)
    (heigen : ∀ l : L, ρ l v = (θ l : k) • v) :
    ∃ x, θ.comp (Subgroup.inclusion hNL) = weight x := by
  classical
  have hex : ∃ x, coordinate x v ≠ 0 := by
    by_contra! h
    exact hv (hcoordinate v h)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, MonoidHom.ext fun n => Units.ext ?_⟩
  apply smul_left_injective k hx
  have h := congrArg (coordinate x) (heigen ((Subgroup.inclusion hNL) n))
  simpa only [Subgroup.coe_inclusion, hscalar, map_smul, MonoidHom.comp_apply] using h.symm

/-- The subgroup supporting a linear-character eigenvector lies in one of the
weight inertia subgroups. -/
theorem exists_le_weightInertia_of_eigenvector (N L : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (ρ : Representation k G V)
    (coordinate : X → V →ₗ[k] U)
    (hcoordinate : ∀ v, (∀ x, coordinate x v = 0) → v = 0)
    (weight : X → N →* kˣ)
    (hscalar : ∀ (n : N) x v, coordinate x (ρ n v) = (weight x n : k) • coordinate x v)
    (θ : L →* kˣ) (v : V) (hv : v ≠ 0)
    (heigen : ∀ l : L, ρ l v = (θ l : k) • v) :
    ∃ x, L ≤ linearCharacterInertia N (weight x) := by
  obtain ⟨x, hx⟩ := exists_weight_eq_of_eigenvector N L hNL ρ coordinate
    hcoordinate weight hscalar θ v hv heigen
  exact ⟨x, le_linearCharacterInertia N L hNL θ (weight x) hx⟩

end Weights

end Kourovka.P21_68

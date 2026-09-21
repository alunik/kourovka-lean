import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Perm.Basic

/-! An injectively indexed subset of an actual group action inherits an
actual action when permutations of its indices certify invariance at a
generating set. There is no presentation or finite-action recognition premise. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SubactionCertificate

variable {G X I : Type*} [Group G]
variable (ρ : G →* Equiv.Perm X) (index : I → X)

/-- Actual elements whose ambient action permutes the indexed subset. -/
def compatibleSubgroup : Subgroup G where
  carrier := {g | ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i)}
  one_mem' := by refine ⟨1, ?_⟩; intro i; simp
  mul_mem' := by
    rintro g h ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p * q, ?_⟩
    intro i
    rw [map_mul, Equiv.Perm.mul_apply, hq, hp]
    rfl
  inv_mem' := by
    rintro g ⟨p, hp⟩
    refine ⟨p.symm, ?_⟩
    intro i
    apply (ρ g).injective
    rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    simpa using (hp (p.symm i)).symm

/-- Generator certificates propagate to every actual group element. -/
theorem exists_permutation (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i))
    (g : G) : ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i) := by
  have h : Subgroup.closure s ≤ compatibleSubgroup ρ index := (Subgroup.closure_le _).mpr hedge
  rw [hs] at h
  exact h (Subgroup.mem_top g)

/-- The inherited action is constructed from the ambient action. -/
def permutation (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i))
    (g : G) : Equiv.Perm I :=
  Classical.choose (exists_permutation ρ index s hs hedge g)

theorem permutation_spec (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i))
    (g : G) (i : I) :
    ρ g (index i) = index (permutation ρ index s hs hedge g i) :=
  Classical.choose_spec (exists_permutation ρ index s hs hedge g) i

/-- Injectivity of the indexing map certifies the group law. -/
def hom (hi : Function.Injective index) (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i)) :
    G →* Equiv.Perm I where
  toFun := permutation ρ index s hs hedge
  map_one' := by
    ext i
    apply hi
    exact (permutation_spec ρ index s hs hedge 1 i).symm.trans (by simp)
  map_mul' g h := by
    ext i
    apply hi
    change index (permutation ρ index s hs hedge (g * h) i) =
      index (permutation ρ index s hs hedge g (permutation ρ index s hs hedge h i))
    calc
      _ = ρ (g * h) (index i) := (permutation_spec ρ index s hs hedge (g * h) i).symm
      _ = ρ g (ρ h (index i)) := by rw [map_mul]; rfl
      _ = ρ g (index (permutation ρ index s hs hedge h i)) := by
        rw [permutation_spec ρ index s hs hedge h i]
      _ = _ := permutation_spec ρ index s hs hedge g _

/-- Finite generator formulas are retained exactly. -/
theorem hom_eq_of_spec (hi : Function.Injective index)
    (s : Set G) (hs : Subgroup.closure s = ⊤)
    (hedge : ∀ g ∈ s, ∃ p : Equiv.Perm I, ∀ i, ρ g (index i) = index (p i))
    (g : G) (p : Equiv.Perm I) (hp : ∀ i, ρ g (index i) = index (p i)) :
    hom ρ index hi s hs hedge g = p := by
  ext i
  apply hi
  exact (permutation_spec ρ index s hs hedge g i).symm.trans (hp i)

end Kourovka2135.SubactionCertificate

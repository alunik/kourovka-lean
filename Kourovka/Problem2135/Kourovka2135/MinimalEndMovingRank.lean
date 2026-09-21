import Kourovka2135.OddOrderMovingRank
import Kourovka2135.MinimalEndomorphismField
import Kourovka2135.MinimalFaithful
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.CharP.Algebra

/-! The actual commuting endomorphism field acts on an irreducible finite
representation. Its group action lifts to that field without changing any
underlying map. Restriction of scalars then multiplies the moving rank by the
endomorphism-field degree. No family classification hypothesis is used.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.MinimalEndMovingRank

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]

/-- The actual intertwining endomorphisms, with their existing ring operations. -/
abbrev EndField (ρ : Representation K G V) := ρ.IntertwiningMap ρ

/-- The existing semiring and additive-group operations combine into a ring. -/
instance endRing (ρ : Representation K G V) : Ring (EndField ρ) :=
  { (inferInstance : Semiring (EndField ρ)),
    (inferInstance : AddCommGroup (EndField ρ)) with }

/-- Intertwining endomorphisms act on the original module by evaluation. -/
instance endModule (ρ : Representation K G V) : Module (EndField ρ) V where
  smul a v := a v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero a := a.map_zero
  smul_add a := a.map_add
  zero_smul _ := rfl
  add_smul _ _ _ := rfl

@[simp] theorem end_smul_apply (ρ : Representation K G V) (a : EndField ρ) (v : V) :
    a • v = a v := rfl

instance endScalarTower (ρ : Representation K G V) : IsScalarTower K (EndField ρ) V where
  smul_assoc _ _ _ := rfl

/-- The original representation, now linear over all of its commuting
endomorphisms. The underlying pointwise action is unchanged. -/
def overEnd (ρ : Representation K G V) : Representation (EndField ρ) G V where
  toFun g :=
    { toFun := ρ g
      map_add' := (ρ g).map_add
      map_smul' := fun a v => (Representation.IntertwiningMap.isIntertwining ρ ρ a g v).symm }
  map_one' := by ext v; exact congrArg (fun T : V →ₗ[K] V => T v) ρ.map_one
  map_mul' g h := by ext v; exact congrArg (fun T : V →ₗ[K] V => T v) (ρ.map_mul g h)

@[simp] theorem overEnd_apply (ρ : Representation K G V) (g : G) (v : V) :
    overEnd ρ g v = ρ g v := rfl

@[simp] theorem overEnd_restrictScalars (ρ : Representation K G V) (g : G) :
    (overEnd ρ g).restrictScalars K = ρ g := by ext v; rfl

@[simp] theorem overEnd_eq_one_iff (ρ : Representation K G V) (g : G) :
    overEnd ρ g = 1 ↔ ρ g = 1 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : V →ₗ[EndField ρ] V => T v) h
  · intro h
    apply LinearMap.ext
    intro v
    exact congrArg (fun T : V →ₗ[K] V => T v) h

section Irreducible
variable [Finite V] (ρ : Representation K G V) [ρ.IsIrreducible]

/-- Schur's lemma and little Wedderburn supply a field on the existing ring,
rather than a separately chosen scalar field. -/
instance endField : Field (EndField ρ) :=
  (irreducible_intertwining_endomorphisms_isField ρ).toField

instance endCharP [CharP K 2] : CharP (EndField ρ) 2 :=
  charP_of_injective_algebraMap (algebraMap K (EndField ρ)).injective 2

/-- Exact moving-rank tower law for the unchanged action. -/
theorem moving_finrank_eq (g : G) :
    Module.finrank K (ρ g - LinearMap.id).range =
      Module.finrank K (EndField ρ) *
        Module.finrank (EndField ρ) (overEnd ρ g - LinearMap.id).range := by
  have hres : (overEnd ρ g - LinearMap.id).restrictScalars K =
      ρ g - LinearMap.id := by ext v; rfl
  rw [← hres, LinearMap.range_restrictScalars]
  calc
    Module.finrank K ((overEnd ρ g - LinearMap.id).range.restrictScalars K) =
        Module.finrank K (overEnd ρ g - LinearMap.id).range :=
      ((Submodule.restrictScalarsEquiv K (EndField ρ) V
        (overEnd ρ g - LinearMap.id).range).restrictScalars K).finrank_eq
    _ = _ := (Module.finrank_mul_finrank K (EndField ρ)
      (overEnd ρ g - LinearMap.id).range).symm

/-- Odd-order nontrivial actions of a perfect group move at least twice the
ground-field degree of their actual commuting endomorphism field. -/
theorem two_mul_end_finrank_le_moving_finrank_of_odd_pow
    [CharP K 2] [Group.IsPerfect G] (g : G) (n : ℕ) (hn : Odd n)
    (hg : g ^ n = 1) (hne : ρ g ≠ 1) :
    2 * Module.finrank K (EndField ρ) ≤ Module.finrank K (ρ g - LinearMap.id).range := by
  have h := OddOrderMovingRank.two_le_moving_rank_of_perfect_of_odd_pow
    (overEnd ρ) g n hn hg (fun he => hne ((overEnd_eq_one_iff ρ g).mp he))
  rw [moving_finrank_eq ρ g, mul_comm 2]
  exact Nat.mul_le_mul_left _ h

theorem two_mul_end_finrank_le_moving_finrank
    [CharP K 2] [Group.IsPerfect G] (g : G) (hodd : Odd (orderOf g)) (hne : ρ g ≠ 1) :
    2 * Module.finrank K (EndField ρ) ≤ Module.finrank K (ρ g - LinearMap.id).range :=
  two_mul_end_finrank_le_moving_finrank_of_odd_pow ρ g (orderOf g) hodd
    (pow_orderOf_eq_one g) hne

end Irreducible
end Kourovka2135.MinimalEndMovingRank

namespace Kourovka2135
open scoped IsMulCommutative

/-- The bound on the actual quotient-group center representation. The simple
quotient and existing minimal-kernel hypotheses provide faithfulness. -/
theorem minimal_center_two_mul_end_finrank_le_moving_finrank
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R) [IsSimpleGroup (G ⧸ R)]
    [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]
    (g : G ⧸ R) (hodd : Odd (orderOf g)) (hne : g ≠ 1) :
    let ρ := minimalCenterRepresentation N hN hmin R hR
    2 * Module.finrank (ZMod 2) (ρ.IntertwiningMap ρ) ≤
      Module.finrank (ZMod 2) (ρ g - LinearMap.id).range := by
  let ρ := minimalCenterRepresentation N hN hmin R hR
  let : ρ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin 2 hN hnonabelian R hR
  apply MinimalEndMovingRank.two_mul_end_finrank_le_moving_finrank ρ g hodd
  intro h
  apply hne
  apply minimal_center_representation_injective_of_perfect N hN hmin hnonabelian R hR
  simpa only [map_one] using h

end Kourovka2135

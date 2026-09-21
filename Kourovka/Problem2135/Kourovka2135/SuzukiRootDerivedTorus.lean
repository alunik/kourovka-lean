import Kourovka2135.SuzukiRootDerivedCoordinates
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The actual split-torus conjugation on the full root subgroup and its
actual derived subgroup and abelianization. The two coordinate weights are
t times Tits(t), and t. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiRootDerivedTorus

open BenderSuzuki.MatrixGroups SuzukiGeometry SuzukiRootDerivedCoordinates
open scoped Matrix MatrixGroups

theorem torus_conj_mem (m : ℕ) (u : (K m)ˣ) (x : U m) :
    SuzukiTorusMovingRank.torusHom m u * x.val *
      (SuzukiTorusMovingRank.torusHom m u)⁻¹ ∈ root m := by
  obtain ⟨a, b, rfl⟩ := exists_coord m x
  change SuzukiTorusGL m u * SuzukiRootGL m a b * (SuzukiTorusGL m u)⁻¹ ∈ rootGL m
  rw [suzukiTorusGL_conj_root m (tits m) (SuzukiTorusMovingRank.tits_sq m)
    (SuzukiTorusMovingRank.tits_apply m)]
  exact Subgroup.subset_closure ⟨_, _, rfl⟩

/-- This automorphism is ambient conjugation, with normalization proved from
the matrix formula. -/
def rootTorusAut (m : ℕ) (u : (K m)ˣ) : MulAut (U m) where
  toFun x := ⟨SuzukiTorusMovingRank.torusHom m u * x.val *
    (SuzukiTorusMovingRank.torusHom m u)⁻¹, torus_conj_mem m u x⟩
  invFun x := ⟨SuzukiTorusMovingRank.torusHom m u⁻¹ * x.val *
    (SuzukiTorusMovingRank.torusHom m u⁻¹)⁻¹, torus_conj_mem m u⁻¹ x⟩
  left_inv x := by
    apply Subtype.ext
    change SuzukiTorusMovingRank.torusHom m u⁻¹ *
      (SuzukiTorusMovingRank.torusHom m u * x.val *
        (SuzukiTorusMovingRank.torusHom m u)⁻¹) *
      (SuzukiTorusMovingRank.torusHom m u⁻¹)⁻¹ = x.val
    rw [map_inv]
    group
  right_inv x := by
    apply Subtype.ext
    change SuzukiTorusMovingRank.torusHom m u *
      (SuzukiTorusMovingRank.torusHom m u⁻¹ * x.val *
        (SuzukiTorusMovingRank.torusHom m u⁻¹)⁻¹) *
      (SuzukiTorusMovingRank.torusHom m u)⁻¹ = x.val
    rw [map_inv]
    group
  map_mul' x y := by
    apply Subtype.ext
    change SuzukiTorusMovingRank.torusHom m u * (x.val * y.val) *
      (SuzukiTorusMovingRank.torusHom m u)⁻¹ =
      (SuzukiTorusMovingRank.torusHom m u * x.val *
        (SuzukiTorusMovingRank.torusHom m u)⁻¹) *
      (SuzukiTorusMovingRank.torusHom m u * y.val *
        (SuzukiTorusMovingRank.torusHom m u)⁻¹)
    group

@[simp] theorem rootTorusAut_coe (m : ℕ) (u : (K m)ˣ) (x : U m) :
    (rootTorusAut m u x : G m) = SuzukiTorusMovingRank.torusHom m u * x.val *
      (SuzukiTorusMovingRank.torusHom m u)⁻¹ := rfl

@[simp] theorem rootTorusAut_coord (m : ℕ) (u : (K m)ˣ) (a b : K m) :
    rootTorusAut m u (coord m a b) =
      coord m ((u : K m) * a) ((u : K m) * tits m (u : K m) * b) := by
  apply Subtype.ext
  apply Subtype.ext
  exact suzukiTorusGL_conj_root m (tits m) (SuzukiTorusMovingRank.tits_sq m)
    (SuzukiTorusMovingRank.tits_apply m) a b u

def rootTorusAction (m : ℕ) : (K m)ˣ →* MulAut (U m) where
  toFun := rootTorusAut m
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change SuzukiTorusMovingRank.torusHom m (u * v) * x.val *
      (SuzukiTorusMovingRank.torusHom m (u * v))⁻¹ =
      SuzukiTorusMovingRank.torusHom m u *
      (SuzukiTorusMovingRank.torusHom m v * x.val *
        (SuzukiTorusMovingRank.torusHom m v)⁻¹) *
      (SuzukiTorusMovingRank.torusHom m u)⁻¹
    rw [map_mul]
    group

def derivedTorusAction (m : ℕ) : (K m)ˣ →* MulAut (commutator (U m)) :=
  (MulAut.characteristic (commutator (U m))).comp (rootTorusAction m)

@[simp] theorem derivedTorusAction_coe (m : ℕ) (u : (K m)ˣ) (d : commutator (U m)) :
    (derivedTorusAction m u d : U m) = rootTorusAut m u d.val := rfl

def abelianizationTorusAut (m : ℕ) (u : (K m)ˣ) : MulAut (Abelianization (U m)) :=
  (rootTorusAut m u).abelianizationCongr

@[simp] theorem abelianizationTorusAut_of (m : ℕ) (u : (K m)ˣ) (x : U m) :
    abelianizationTorusAut m u (Abelianization.of x) =
      Abelianization.of (rootTorusAut m u x) := rfl

def abelianizationTorusAction (m : ℕ) : (K m)ˣ →* MulAut (Abelianization (U m)) where
  toFun := abelianizationTorusAut m
  map_one' := by
    apply MulEquiv.ext
    intro a
    refine QuotientGroup.induction_on a ?_
    intro x
    change Abelianization.of (rootTorusAction m 1 x) = Abelianization.of x
    rw [map_one]
    rfl
  map_mul' u v := by
    apply MulEquiv.ext
    intro a
    refine QuotientGroup.induction_on a ?_
    intro x
    change Abelianization.of (rootTorusAction m (u * v) x) =
      Abelianization.of (rootTorusAction m u (rootTorusAction m v x))
    rw [map_mul]
    rfl

theorem firstHom_torus (m : ℕ) (u : (K m)ˣ) (x : U m) :
    (firstHom m (rootTorusAut m u x)).toAdd = (u : K m) * (firstHom m x).toAdd := by
  obtain ⟨a, b, rfl⟩ := exists_coord m x
  simp

theorem derivedEquiv_torus (m : ℕ) (hm : 0 < m) (u : (K m)ˣ) (d : commutator (U m)) :
    (derivedEquiv m hm (derivedTorusAction m u d)).toAdd =
      (u : K m) * tits m (u : K m) * (derivedEquiv m hm d).toAdd := by
  obtain ⟨b, hb⟩ := (mem_Z_iff m d.val).mp (commutator_le_Z m d.property)
  have hd : d = ⟨coord m 0 b, zero_coord_mem_commutator m hm b⟩ := Subtype.ext hb.symm
  rw [hd]
  have he : derivedTorusAction m u ⟨coord m 0 b, zero_coord_mem_commutator m hm b⟩ =
      ⟨coord m 0 ((u : K m) * tits m (u : K m) * b),
        zero_coord_mem_commutator m hm _⟩ := by
    apply Subtype.ext
    simp
  rw [he, derivedEquiv_zero, derivedEquiv_zero]
  rfl

theorem abelianizationEquiv_torus (m : ℕ) (hm : 0 < m) (u : (K m)ˣ)
    (a : Abelianization (U m)) :
    (abelianizationEquiv m hm (abelianizationTorusAction m u a)).toAdd =
      (u : K m) * (abelianizationEquiv m hm a).toAdd := by
  refine QuotientGroup.induction_on a ?_
  intro x
  exact firstHom_torus m u x

/-- The actual additive group underlying the derived subgroup is Fq. -/
def derivedAddEquiv (m : ℕ) (hm : 0 < m) : Additive (commutator (U m)) ≃+ K m :=
  (derivedEquiv m hm).toAdditiveLeft

/-- The actual additive group underlying the abelianization is Fq. -/
def abelianizationAddEquiv (m : ℕ) (hm : 0 < m) : Additive (Abelianization (U m)) ≃+ K m :=
  (abelianizationEquiv m hm).toAdditiveLeft

theorem derivedAddEquiv_torus (m : ℕ) (hm : 0 < m) (u : (K m)ˣ)
    (d : Additive (commutator (U m))) :
    derivedAddEquiv m hm (Additive.ofMul (derivedTorusAction m u d.toMul)) =
      (u : K m) ^ (1 + 2 ^ (m + 1)) * derivedAddEquiv m hm d := by
  change (derivedEquiv m hm (derivedTorusAction m u d.toMul)).toAdd =
    (u : K m) ^ (1 + 2 ^ (m + 1)) * (derivedEquiv m hm d.toMul).toAdd
  rw [pow_add, pow_one, ← SuzukiTorusMovingRank.tits_apply]
  exact derivedEquiv_torus m hm u d.toMul

theorem abelianizationAddEquiv_torus (m : ℕ) (hm : 0 < m) (u : (K m)ˣ)
    (a : Additive (Abelianization (U m))) :
    abelianizationAddEquiv m hm (Additive.ofMul (abelianizationTorusAction m u a.toMul)) =
      (u : K m) * abelianizationAddEquiv m hm a :=
  abelianizationEquiv_torus m hm u a.toMul

end Kourovka2135.SuzukiRootDerivedTorus

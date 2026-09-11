import Kourovka.Problems.P21_68.Proof.Groups
import Kourovka.Problems.P21_68.Proof.Semiabelian
import Kourovka.Problems.P21_68.Proof.Obstruction
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The abelian extension and its weight inertia subgroup

The augmentation subgroup of `𝔽₃^(W/H)` has order 27. Its four coordinate
characters remain distinct, so the inertia subgroup of the character at the
identity coset is exactly `I = A ⋊ H`. The resulting group `G` has order 2592
and satisfies the notebook's actual subgroup-chain definition of semiabelianity.
-/

namespace Kourovka.P21_68

noncomputable section

/-- The four left cosets of the embedded quaternion extension. -/
abbrev X := W ⧸ Hsub
instance : Fintype X := Fintype.ofFinite X
instance : DecidableEq X := Classical.decEq X

def origin : X := QuotientGroup.mk 1

theorem card_X : Fintype.card X = 4 := by
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Hsub_index]

def augmentationSum : (X → ZMod 3) →+ ZMod 3 where
  toFun f := ∑ x, f x
  map_zero' := by simp
  map_add' := by intro f g; simp [Finset.sum_add_distrib]

/-- The additive augmentation subgroup, written multiplicatively for semidirect products. -/
abbrev A := Multiplicative augmentationSum.ker
instance : Fintype A := Fintype.ofFinite A

def xAction : W →* Equiv.Perm X := MulAction.toPermHom W X

def aReindex (w : W) (a : A) : A :=
  Multiplicative.ofAdd ⟨fun x => a.toAdd.val ((xAction w)⁻¹ x), by
    change (∑ x, a.toAdd.val ((xAction w).symm x)) = 0
    rw [(xAction w).symm.sum_comp]
    exact a.toAdd.property⟩

def aAction : W →* MulAut A where
  toFun w :=
    { toFun := aReindex w
      invFun := aReindex w⁻¹
      left_inv := by
        intro a
        apply Subtype.ext
        funext x
        change a.toAdd.val ((xAction w)⁻¹ ((xAction w⁻¹)⁻¹ x)) = a.toAdd.val x
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        funext x
        change a.toAdd.val ((xAction w⁻¹)⁻¹ ((xAction w)⁻¹ x)) = a.toAdd.val x
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        funext x
        rfl }
  map_one' := by
    ext a x
    change a.toAdd.val ((xAction 1)⁻¹ x) = a.toAdd.val x
    simp
  map_mul' := by
    intro a b
    ext e x
    change e.toAdd.val ((xAction (a * b))⁻¹ x) =
      e.toAdd.val ((xAction b)⁻¹ ((xAction a)⁻¹ x))
    simp

/-- The group witnessing the counterexample. -/
abbrev G := A ⋊[aAction] W
instance : Fintype G := Fintype.ofEquiv (A × W) SemidirectProduct.equivProd.symm

/-- The normal abelian subgroup of order 27. -/
def N : Subgroup G := (SemidirectProduct.inl : A →* G).range
/-- The preimage of `Hsub`, subsequently proved to be the exact weight inertia subgroup. -/
def I : Subgroup G := Hsub.comap SemidirectProduct.rightHom

instance : N.Normal := by
  dsimp [N]
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

def iProjection : I →* Hsub where
  toFun g := ⟨g.val.right, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem iProjection_surjective : Function.Surjective iProjection := by
  intro h
  exact ⟨⟨SemidirectProduct.inr h.val, h.property⟩, rfl⟩

def iA : A →* I := (SemidirectProduct.inl : A →* G).codRestrict I
  (by intro a; exact Hsub.one_mem)

theorem N_le_I : N ≤ I := by
  rintro g ⟨a, rfl⟩
  exact Hsub.one_mem

theorem iProjection_ker : iProjection.ker = N.subgroupOf I := by
  ext g
  change (⟨g.val.right, g.property⟩ : Hsub) = 1 ↔ g.val ∈ N
  rw [Subtype.ext_iff]
  simp only [N, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    SemidirectProduct.rightHom]
  rfl

theorem T_semiabelian : IsSemiabelian T :=
  (IsSemiabelian.of_commGroup C3).semidirect vAction

theorem W_semiabelian : IsSemiabelian W := T_semiabelian.semidirect eAction
theorem G_semiabelian : IsSemiabelian G := W_semiabelian.semidirect aAction

/-- A coordinate character, using the faithful standard character of `ZMod 3`. -/
def weight (x : X) : A →* ℂˣ where
  toFun a := Circle.toUnits (ZMod.toCircle (a.toAdd.val x))
  map_one' := by simp
  map_mul' := by
    intro a b
    change Circle.toUnits (ZMod.toCircle (a.toAdd.val x + b.toAdd.val x)) = _
    rw [AddChar.map_add_eq_mul, map_mul]

def lambda : A →* ℂˣ := weight origin

def separatingVector (x y : X) : A := Multiplicative.ofAdd
  ⟨fun z => (if z = x then 1 else 0) - (if z = y then 1 else 0), by
    change (∑ z, ((if z = x then 1 else 0) - (if z = y then 1 else 0) : ZMod 3)) = 0
    simp [Finset.sum_sub_distrib]⟩

theorem weight_injective : Function.Injective weight := by
  intro x y h
  by_contra hxy
  have hv := congrArg (fun f : A →* ℂˣ => (f (separatingVector x y) : ℂ)) h
  change ZMod.stdAddChar _ = ZMod.stdAddChar _ at hv
  have hz := ZMod.injective_stdAddChar hv
  have hf : (1 : ZMod 3) ≠ -1 := by decide +kernel
  apply hf
  simpa [separatingVector, hxy, Ne.symm hxy] using hz

theorem weight_comp_action (x : X) (w : W) :
    (weight x).comp (aAction w).toMonoidHom = weight (w⁻¹ • x) := by
  rfl

theorem origin_smul_eq_iff (w : W) : w • origin = origin ↔ w ∈ Hsub := by
  change w ∈ MulAction.stabilizer W ((1 : W) : W ⧸ Hsub) ↔ w ∈ Hsub
  rw [MulAction.stabilizer_quotient]

theorem lambda_inertia_iff (w : W) :
    lambda.comp (aAction w).toMonoidHom = lambda ↔ w ∈ Hsub := by
  simp only [lambda, weight_comp_action, weight_injective.eq_iff, origin_smul_eq_iff,
    inv_mem_iff]

theorem lambda_action (w : Hsub) (a : A) : lambda (aAction w.val a) = lambda a :=
  congrArg (fun f : A →* ℂˣ => f a) ((lambda_inertia_iff w.val).mpr w.property)

theorem augmentationSum_surjective : Function.Surjective augmentationSum := by
  intro z
  refine ⟨fun x => if x = origin then z else 0, ?_⟩
  simp [augmentationSum]

theorem card_A : Nat.card A = 27 := by
  have hi : augmentationSum.ker.index = 3 := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr augmentationSum_surjective]
    simp
  have hc := augmentationSum.ker.card_mul_index
  rw [hi] at hc
  have ht : Nat.card (X → ZMod 3) = 81 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, card_X]
    norm_num
  rw [ht] at hc
  change Nat.card augmentationSum.ker = 27
  omega

theorem card_G : Nat.card G = 2592 := by
  rw [SemidirectProduct.card, card_A, Nat.card_eq_fintype_card, card_W]

/-- The coordinate character extends across its stabilizer by ignoring the complement. -/
def lambdaExtended : I →* ℂˣ where
  toFun g := lambda g.val.left
  map_one' := lambda.map_one
  map_mul' g h := by
    change lambda (g.val.left * aAction g.val.right h.val.left) = _
    rw [map_mul, lambda_action ⟨g.val.right, g.property⟩]

@[simp] theorem lambdaExtended_iA (a : A) : lambdaExtended (iA a) = lambda a := rfl

@[simp] theorem iProjection_iA (a : A) : iProjection (iA a) = 1 := rfl

theorem I_index : I.index = 4 := by
  exact (Hsub.index_comap_of_surjective
    (show Function.Surjective (SemidirectProduct.rightHom : G →* W) from
      SemidirectProduct.rightHom_surjective)).trans Hsub_index

def nEquiv : A ≃* N := MulEquiv.ofBijective
  (SemidirectProduct.inl : A →* G).rangeRestrict
  ⟨fun _ _ h => SemidirectProduct.inl_injective (congrArg Subtype.val h),
    (SemidirectProduct.inl : A →* G).rangeRestrict_surjective⟩

theorem card_N : Nat.card N = 27 := by
  rw [← Nat.card_congr nEquiv.toEquiv, card_A]

def nWeight : N →* ℂˣ := lambda.comp nEquiv.symm.toMonoidHom

theorem conj_inl (g : G) (a : A) :
    g * SemidirectProduct.inl a * g⁻¹ = SemidirectProduct.inl (aAction g.right a) := by
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, mul_comm, mul_assoc]
  · simp

theorem lambda_conj_inl_iff (g : G) :
    (∀ a : A, lambda (g * SemidirectProduct.inl a * g⁻¹).left = lambda a) ↔ g ∈ I := by
  simp only [conj_inl, SemidirectProduct.left_inl]
  change (∀ a, lambda (aAction g.right a) = lambda a) ↔ g.right ∈ Hsub
  rw [← lambda_inertia_iff]
  constructor
  · intro h
    exact MonoidHom.ext h
  · intro h a
    exact DFunLike.congr_fun h a

@[simp] theorem nEquiv_apply_val (a : A) : (nEquiv a).val = SemidirectProduct.inl a := rfl

theorem nEquiv_symm_eq_left (n : N) : nEquiv.symm n = n.val.left := by
  exact congrArg (fun n : N => n.val.left) (nEquiv.apply_symm_apply n)

@[simp] theorem nWeight_apply (n : N) : nWeight n = lambda n.val.left := by
  change lambda (nEquiv.symm n) = _
  rw [nEquiv_symm_eq_left]

@[simp] theorem lambdaExtended_inclusion_N (n : N) :
    lambdaExtended (Subgroup.inclusion N_le_I n) = nWeight n := by
  rw [nWeight_apply]
  rfl

@[simp] theorem iProjection_inclusion_N (n : N) :
    iProjection (Subgroup.inclusion N_le_I n) = 1 := by
  obtain ⟨a, rfl⟩ := nEquiv.surjective n
  rfl

/-- The exact inertia calculation in the convention used by the general obstruction. -/
theorem nWeight_inertia : linearCharacterInertia N nWeight = I := by
  ext g
  change (∀ n : N, nWeight (MulAut.conjNormal g n) = nWeight n) ↔ g ∈ I
  rw [← lambda_conj_inl_iff]
  constructor
  · intro h a
    have ha := h (nEquiv a)
    simpa only [nWeight_apply, MulAut.conjNormal_apply, nEquiv_apply_val,
      SemidirectProduct.left_inl] using ha
  · intro h n
    obtain ⟨a, rfl⟩ := nEquiv.surjective n
    simpa only [nWeight_apply, MulAut.conjNormal_apply, nEquiv_apply_val,
      SemidirectProduct.left_inl] using h a


end

end Kourovka.P21_68

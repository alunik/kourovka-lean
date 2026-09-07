import Kourovka.Problems.P21_03.Proof.Basic
import Kourovka.Problems.P21_03.Proof.NaturalWreath
import Mathlib.Data.Fintype.Option
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Order.Atoms.Finite

/-!
# Recursive soluble permutation containers

This file supplies the structural interface used by the support-counting part of the
Kourovka 21.3 formalization.  A container is built without a Jordan classification:

* different orbits are put in a direct product (a forest);
* a transitive imprimitive action is put in a natural permutational wreath product;
* recursion stops at a primitive soluble action.

The core notion is an `ActionEmbedding`: an injective homomorphism of acting groups,
together with an equivariant equivalence of point sets.  Consequently it preserves
both degree and pointwise support exactly.
-/

open scoped Pointwise

namespace Kourovka213

universe u v

/-! ## Solubility of finite direct powers and wreath products -/

/-- The standard multiplicative equivalence
`(Option ι → G) ≃* G × (ι → G)`. -/
def piOptionMulEquiv (G : Type v) [Group G] (ι : Type u) :
    (Option ι → G) ≃* G × (ι → G) where
  toEquiv := Equiv.piOptionEquivProd
  map_mul' f g := by
    ext x <;> rfl

/-- A finite direct power of a soluble group is soluble.  Mathlib has the binary-product
instance; this is the finite-indexed version needed for wreath bases. -/
theorem isSolvable_pi_finite (G : Type v) [Group G] [Group.IsSolvable G]
    (ι : Type u) [Fintype ι] : Group.IsSolvable (ι → G) := by
  refine Fintype.induction_empty_option
    (P := fun ι ↦ Group.IsSolvable (ι → G)) ?_ ?_ ?_ ι
  · intro α β _ e ih
    exact Group.isSolvable_of_isSolvable_injective
      (f := (MulEquiv.arrowCongr e.symm (MulEquiv.refl G)).toMonoidHom)
      (MulEquiv.arrowCongr e.symm (MulEquiv.refl G)).injective
  · infer_instance
  · intro α _ ih
    let hPi : Group.IsSolvable (α → G) := ih
    let hProd : Group.IsSolvable (G × (α → G)) := by
      letI := hPi
      infer_instance
    letI := hProd
    exact Group.isSolvable_of_isSolvable_injective
      (f := (piOptionMulEquiv G α).toMonoidHom) (piOptionMulEquiv G α).injective

/-- A permutational wreath product over a finite index type is soluble when its two
factors are soluble. -/
theorem isSolvable_permWreath (X : Type v) (Q : Type v) (ι : Type u)
    [Group X] [Group Q] [MulAction Q ι] [Fintype ι]
    [Group.IsSolvable X] [Group.IsSolvable Q] :
    Group.IsSolvable (PermWreath X Q ι) := by
  let hBase : Group.IsSolvable (ι → X) := isSolvable_pi_finite X ι
  letI := hBase
  exact Group.isSolvable_of_ker_le_range
    (SemidirectProduct.inl : (ι → X) →* PermWreath X Q ι)
    (SemidirectProduct.rightHom : PermWreath X Q ι →* Q)
    (by rw [← SemidirectProduct.range_inl_eq_ker_rightHom])

/-! ## Finite faithful soluble actions and their embeddings -/

/-- A finite faithful permutation action of a finite soluble group.  Storing the actor
as a type (rather than only as a subgroup of a fixed symmetric group) makes products
and wreath products definitionally transparent. -/
structure SolubleAction where
  Point : Type u
  Actor : Type v
  pointFintype : Fintype Point
  pointDecidableEq : DecidableEq Point
  pointNonempty : Nonempty Point
  actorGroup : Group Actor
  actorFinite : Finite Actor
  action : MulAction Actor Point
  faithful : FaithfulSMul Actor Point
  soluble : Group.IsSolvable Actor

attribute [instance] SolubleAction.pointFintype SolubleAction.pointDecidableEq
  SolubleAction.pointNonempty
  SolubleAction.actorGroup SolubleAction.actorFinite SolubleAction.action
  SolubleAction.faithful SolubleAction.soluble

namespace SolubleAction

/-- Degree of a finite action. -/
def degree (A : SolubleAction) : ℕ := Fintype.card A.Point

/-- The faithful permutation representation of an action model. -/
def toPermHom (A : SolubleAction) : A.Actor →* Equiv.Perm A.Point :=
  MulAction.toPermHom A.Actor A.Point

theorem toPermHom_injective (A : SolubleAction) : Function.Injective A.toPermHom :=
  MulAction.toPerm_injective

/-- A soluble subgroup of a symmetric group, viewed as a faithful action model. -/
def ofSubgroup {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (H : Subgroup (Equiv.Perm α)) (hH : Group.IsSolvable H) : SolubleAction where
  Point := α
  Actor := H
  pointFintype := inferInstance
  pointDecidableEq := inferInstance
  pointNonempty := inferInstance
  actorGroup := inferInstance
  actorFinite := inferInstance
  action := inferInstance
  faithful := inferInstance
  soluble := hH

/-- The faithful image action associated to a possibly nonfaithful action of `A.Actor`.
It is soluble because it is a quotient image of `A.Actor`. -/
abbrev image (A : SolubleAction) (Y : Type u) [Fintype Y] [DecidableEq Y]
    [Nonempty Y] [MulAction A.Actor Y] : SolubleAction := by
  let ρ : A.Actor →* Equiv.Perm Y := MulAction.toPermHom A.Actor Y
  have hsol : Group.IsSolvable ρ.range := by
    exact Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  exact
    { Point := Y
      Actor := ρ.range
      pointFintype := inferInstance
      pointDecidableEq := inferInstance
      pointNonempty := inferInstance
      actorGroup := inferInstance
      actorFinite := inferInstance
      action := inferInstance
      faithful := inferInstance
      soluble := hsol }

/-- The canonical surjection from the original actor to its faithful image on `Y`. -/
def imageHom (A : SolubleAction) (Y : Type u) [Fintype Y] [DecidableEq Y]
    [Nonempty Y] [MulAction A.Actor Y] : A.Actor →* (A.image Y).Actor :=
  (MulAction.toPermHom A.Actor Y).rangeRestrict

@[simp]
theorem imageHom_smul (A : SolubleAction) (Y : Type u) [Fintype Y] [DecidableEq Y]
    [Nonempty Y] [MulAction A.Actor Y] (g : A.Actor) (y : Y) :
    (A.imageHom Y g).1 y = g • y := rfl

/-- Pretransitivity descends to the faithful permutation image. -/
theorem image_isPretransitive (A : SolubleAction) (Y : Type u)
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MulAction A.Actor Y]
    (h : MulAction.IsPretransitive A.Actor Y) :
    MulAction.IsPretransitive (A.image Y).Actor (A.image Y).Point := by
  let f : Y →ₑ[A.imageHom Y] (A.image Y).Point :=
    { toFun := id
      map_smul' := by
        intro g y
        exact (A.imageHom_smul Y g y).symm }
  exact MulAction.IsPretransitive.of_surjective_map
    (f := f) Function.surjective_id h

/-- Preprimitivity descends to the faithful permutation image. -/
theorem image_isPreprimitive (A : SolubleAction) (Y : Type u)
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MulAction A.Actor Y]
    (h : MulAction.IsPreprimitive A.Actor Y) :
    MulAction.IsPreprimitive (A.image Y).Actor (A.image Y).Point := by
  letI : MulAction.IsPreprimitive A.Actor Y := h
  let f : Y →ₑ[A.imageHom Y] (A.image Y).Point :=
    { toFun := id
      map_smul' := by
        intro g y
        exact (A.imageHom_smul Y g y).symm }
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

end SolubleAction

/-- An embedding of finite permutation actions.  The equivalence of point sets is part
of the data because later support counts must be preserved, not merely group order. -/
structure ActionEmbedding (A B : SolubleAction) where
  actorHom : A.Actor →* B.Actor
  actorHom_injective : Function.Injective actorHom
  pointEquiv : A.Point ≃ B.Point
  map_smul : ∀ (g : A.Actor) (x : A.Point),
    pointEquiv (g • x) = actorHom g • pointEquiv x

namespace ActionEmbedding

/-- Equivariance plus faithfulness of the source action forces the actor homomorphism
to be injective. -/
def ofEquivariant (A B : SolubleAction) (f : A.Actor →* B.Actor)
    (e : A.Point ≃ B.Point)
    (he : ∀ (g : A.Actor) (x : A.Point), e (g • x) = f g • e x) :
    ActionEmbedding A B where
  actorHom := f
  actorHom_injective := by
    intro g h hgh
    apply A.faithful.eq_of_smul_eq_smul
    intro x
    apply e.injective
    rw [he, he, hgh]
  pointEquiv := e
  map_smul := he

/-- Every faithful action embeds canonically into its own permutation image.  This
also normalizes the actor universe to the universe of the point type. -/
def toImage (A : SolubleAction) : ActionEmbedding A (A.image A.Point) :=
  ActionEmbedding.ofEquivariant A _ (A.imageHom A.Point) (Equiv.refl A.Point)
    (fun g x ↦ (A.imageHom_smul A.Point g x).symm)

/-- Identity embedding. -/
def refl (A : SolubleAction) : ActionEmbedding A A where
  actorHom := MonoidHom.id A.Actor
  actorHom_injective := Function.injective_id
  pointEquiv := Equiv.refl A.Point
  map_smul _ _ := rfl

/-- Composition of action embeddings. -/
def trans {A B C : SolubleAction} (f : ActionEmbedding A B)
    (g : ActionEmbedding B C) : ActionEmbedding A C where
  actorHom := g.actorHom.comp f.actorHom
  actorHom_injective := g.actorHom_injective.comp f.actorHom_injective
  pointEquiv := f.pointEquiv.trans g.pointEquiv
  map_smul a x := by
    calc
      g.pointEquiv (f.pointEquiv (a • x)) =
          g.pointEquiv (f.actorHom a • f.pointEquiv x) :=
        congrArg g.pointEquiv (f.map_smul a x)
      _ = g.actorHom (f.actorHom a) • g.pointEquiv (f.pointEquiv x) :=
        g.map_smul (f.actorHom a) (f.pointEquiv x)

theorem degree_eq {A B : SolubleAction} (f : ActionEmbedding A B) :
    A.degree = B.degree :=
  Fintype.card_congr f.pointEquiv

/-- An action embedding preserves the fixed-point predicate pointwise. -/
theorem map_fixed_iff {A B : SolubleAction} (f : ActionEmbedding A B)
    (g : A.Actor) (x : A.Point) :
    f.actorHom g • f.pointEquiv x = f.pointEquiv x ↔ g • x = x := by
  rw [← f.map_smul]
  exact f.pointEquiv.injective.eq_iff

/-- Hence it preserves support membership pointwise. -/
theorem map_moved_iff {A B : SolubleAction} (f : ActionEmbedding A B)
    (g : A.Actor) (x : A.Point) :
    f.actorHom g • f.pointEquiv x ≠ f.pointEquiv x ↔ g • x ≠ x :=
  not_congr (f.map_fixed_iff g x)

end ActionEmbedding

/-! ## Direct sums of actions -/

namespace SolubleAction

section SumAction

variable (A B : SolubleAction)

/-- Componentwise action of a product group on a disjoint union. -/
def sumSMul : SMul (A.Actor × B.Actor) (A.Point ⊕ B.Point) where
  smul g x := match x with
    | Sum.inl a => Sum.inl (g.1 • a)
    | Sum.inr b => Sum.inr (g.2 • b)

/-- The componentwise sum action satisfies the group-action laws. -/
def sumMulAction : MulAction (A.Actor × B.Actor) (A.Point ⊕ B.Point) := by
  letI := sumSMul A B
  exact
    { one_smul := by
        intro x
        cases x with
        | inl a =>
            change Sum.inl ((1 : A.Actor) • a) = Sum.inl a
            rw [one_smul]
        | inr b =>
            change Sum.inr ((1 : B.Actor) • b) = Sum.inr b
            rw [one_smul]
      mul_smul := by
        intro g h x
        cases x with
        | inl a =>
            change Sum.inl ((g.1 * h.1) • a) = Sum.inl (g.1 • h.1 • a)
            rw [mul_smul]
        | inr b =>
            change Sum.inr ((g.2 * h.2) • b) = Sum.inr (g.2 • h.2 • b)
            rw [mul_smul] }

/-- The product action on a disjoint union is faithful. -/
def sumFaithfulSMul : @FaithfulSMul (A.Actor × B.Actor) (A.Point ⊕ B.Point)
    (sumSMul A B) := by
  letI := sumSMul A B
  letI := sumMulAction A B
  exact
    { eq_of_smul_eq_smul := by
        intro g h heq
        apply Prod.ext
        · apply A.faithful.eq_of_smul_eq_smul
          intro a
          have ha := heq (Sum.inl a)
          exact Sum.inl.inj ha
        · apply B.faithful.eq_of_smul_eq_smul
          intro b
          have hb := heq (Sum.inr b)
          exact Sum.inr.inj hb }

/-- Direct sum of two finite soluble faithful actions. -/
abbrev sum : SolubleAction := by
  letI := sumSMul A B
  letI := sumMulAction A B
  exact
    { Point := A.Point ⊕ B.Point
      Actor := A.Actor × B.Actor
      pointFintype := inferInstance
      pointDecidableEq := inferInstance
      pointNonempty := inferInstance
      actorGroup := inferInstance
      actorFinite := inferInstance
      action := inferInstance
      faithful := sumFaithfulSMul A B
      soluble := inferInstance }

theorem degree_sum : (SolubleAction.sum A B).degree = A.degree + B.degree := by
  exact @Fintype.card_sum A.Point B.Point _ _

end SumAction

end SolubleAction

namespace ActionEmbedding

/-- Direct sum of two action embeddings. -/
def sum {A A' B B' : SolubleAction} (f : ActionEmbedding A A')
    (g : ActionEmbedding B B') :
    ActionEmbedding (SolubleAction.sum A B) (SolubleAction.sum A' B') where
  actorHom := MonoidHom.prodMap f.actorHom g.actorHom
  actorHom_injective := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    apply Prod.ext
    · exact f.actorHom_injective (congrArg Prod.fst h)
    · exact g.actorHom_injective (congrArg Prod.snd h)
  pointEquiv := f.pointEquiv.sumCongr g.pointEquiv
  map_smul h x := by
    rcases h with ⟨a, b⟩
    cases x with
    | inl x =>
        change Sum.inl (f.pointEquiv (a • x)) =
          Sum.inl (f.actorHom a • f.pointEquiv x)
        rw [f.map_smul]
    | inr x =>
        change Sum.inr (g.pointEquiv (b • x)) =
          Sum.inr (g.actorHom b • g.pointEquiv x)
        rw [g.map_smul]

end ActionEmbedding

/-! ## Wreath nodes -/

/-- Natural imprimitive wreath action constructed from a fibre action and a top action. -/
abbrev SolubleAction.wreath (F T : SolubleAction) : SolubleAction := by
  let hsol : Group.IsSolvable (PermWreath F.Actor T.Actor T.Point) :=
    isSolvable_permWreath F.Actor T.Actor T.Point
  let hfinite : Finite (PermWreath F.Actor T.Actor T.Point) :=
    Finite.of_injective
      (fun g : PermWreath F.Actor T.Actor T.Point ↦ (g.left, g.right))
      (fun _ _ h ↦ SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact
    { Point := T.Point × F.Point
      Actor := PermWreath F.Actor T.Actor T.Point
      pointFintype := inferInstance
      pointDecidableEq := inferInstance
      pointNonempty := inferInstance
      actorGroup := inferInstance
      actorFinite := hfinite
      action := permWreathNaturalMulAction F.Actor T.Actor T.Point F.Point
      faithful := permWreathNaturalFaithfulSMul F.Actor T.Actor T.Point F.Point
      soluble := hsol }

theorem SolubleAction.degree_wreath (F T : SolubleAction) :
    (SolubleAction.wreath F T).degree = T.degree * F.degree := by
  exact Fintype.card_prod T.Point F.Point

/-- Apply a homomorphism pointwise to the base of a permutational wreath product. -/
def PermWreath.mapBase {X Y Q : Type v} {ι : Type u}
    [Group X] [Group Y] [Group Q] [MulAction Q ι]
    (f : X →* Y) : PermWreath X Q ι →* PermWreath Y Q ι where
  toFun g := ⟨fun i ↦ f (g.left i), g.right⟩
  map_one' := by
    apply PermWreath.ext
    · funext i
      simp
    · rfl
  map_mul' g h := by
    apply PermWreath.ext
    · funext i
      simp
    · rfl

@[simp]
theorem PermWreath.mapBase_left {X Y Q : Type v} {ι : Type u}
    [Group X] [Group Y] [Group Q] [MulAction Q ι]
    (f : X →* Y) (g : PermWreath X Q ι) (i : ι) :
    (PermWreath.mapBase f g).left i = f (g.left i) := rfl

@[simp]
theorem PermWreath.mapBase_right {X Y Q : Type v} {ι : Type u}
    [Group X] [Group Y] [Group Q] [MulAction Q ι]
    (f : X →* Y) (g : PermWreath X Q ι) :
    (PermWreath.mapBase f g).right = g.right := rfl

theorem PermWreath.mapBase_injective {X Y Q : Type v} {ι : Type u}
    [Group X] [Group Y] [Group Q] [MulAction Q ι]
    {f : X →* Y} (hf : Function.Injective f) :
    Function.Injective
      (PermWreath.mapBase (X := X) (Y := Y) (Q := Q) (ι := ι) f) := by
  intro g h heq
  apply PermWreath.ext
  · funext i
    apply hf
    have hi := congrArg (fun z : PermWreath Y Q ι ↦ z.left i) heq
    exact hi
  · exact congrArg (fun z : PermWreath Y Q ι ↦ z.right) heq

namespace ActionEmbedding

/-- Lift an embedding of fibre actions through a wreath product while leaving the top
action unchanged. -/
def wreathBase {F F' T : SolubleAction} (f : ActionEmbedding F F') :
    ActionEmbedding (SolubleAction.wreath F T) (SolubleAction.wreath F' T) where
  actorHom := PermWreath.mapBase f.actorHom
  actorHom_injective := PermWreath.mapBase_injective f.actorHom_injective
  pointEquiv := (Equiv.refl T.Point).prodCongr f.pointEquiv
  map_smul g x := by
    rcases x with ⟨i, y⟩
    change
      (g.right • i, f.pointEquiv (g.left (g.right • i) • y)) =
        (g.right • i, f.actorHom (g.left (g.right • i)) • f.pointEquiv y)
    exact Prod.ext rfl (f.map_smul _ _)

end ActionEmbedding

/-- Explicit wreath coordinates for a transitive imprimitive action.  Constructing this
record is precisely the (Schreier-transversal) wreath-embedding step; once it is
available, faithfulness is automatic. -/
structure ImprimitiveCoordinates (A F T : SolubleAction) where
  actorHom : A.Actor →* (SolubleAction.wreath F T).Actor
  pointEquiv : A.Point ≃ T.Point × F.Point
  map_smul : ∀ (g : A.Actor) (x : A.Point),
    pointEquiv (g • x) = actorHom g • pointEquiv x

namespace ImprimitiveCoordinates

/-- Wreath coordinates give a support-preserving action embedding. -/
def embedding {A F T : SolubleAction} (C : ImprimitiveCoordinates A F T) :
    ActionEmbedding A (SolubleAction.wreath F T) :=
  ActionEmbedding.ofEquivariant A _ C.actorHom C.pointEquiv C.map_smul

end ImprimitiveCoordinates

/-! ## Recursive containers -/

/-- A primitive soluble action, used as a terminal or top node. -/
structure PrimitiveNode where
  action : SolubleAction.{u, u}
  preprimitive : MulAction.IsPreprimitive action.Actor action.Point

/-- A homogeneous rooted tree of primitive actions.  At a wreath node the child is the
action inside a block and the second argument is the primitive action on the blocks. -/
inductive TreeContainer where
  | primitive (leaf : PrimitiveNode.{u})
  | wreath (fibre : TreeContainer) (top : PrimitiveNode.{u})

namespace TreeContainer

/-- Action realized by a rooted container. -/
def action : TreeContainer.{u} → SolubleAction.{u, u}
  | primitive leaf => leaf.action
  | wreath fibre top => SolubleAction.wreath fibre.action top.action

/-- Number of leaves (permutation degree) of a rooted container. -/
def degree (T : TreeContainer.{u}) : ℕ := T.action.degree

@[simp]
theorem action_primitive (leaf : PrimitiveNode.{u}) :
    (TreeContainer.primitive leaf).action = leaf.action := rfl

@[simp]
theorem action_wreath (fibre : TreeContainer.{u}) (top : PrimitiveNode.{u}) :
    (TreeContainer.wreath fibre top).action =
      SolubleAction.wreath fibre.action top.action := rfl

@[simp]
theorem degree_wreath (fibre : TreeContainer.{u}) (top : PrimitiveNode.{u}) :
    (TreeContainer.wreath fibre top).degree =
      top.action.degree * fibre.degree :=
  SolubleAction.degree_wreath _ _

end TreeContainer

/-- A forest is a nonempty disjoint union of homogeneous rooted trees. -/
inductive ForestContainer where
  | tree (root : TreeContainer.{u})
  | sum (left right : ForestContainer)

namespace ForestContainer

/-- Action realized by a forest. -/
def action : ForestContainer.{u} → SolubleAction.{u, u}
  | tree root => root.action
  | sum left right => SolubleAction.sum left.action right.action

/-- Degree of a forest container. -/
def degree (F : ForestContainer.{u}) : ℕ := F.action.degree

@[simp]
theorem degree_tree (T : TreeContainer.{u}) :
    (ForestContainer.tree T).degree = T.degree := rfl

@[simp]
theorem degree_sum (F₁ F₂ : ForestContainer.{u}) :
    (ForestContainer.sum F₁ F₂).degree = F₁.degree + F₂.degree :=
  SolubleAction.degree_sum _ _

end ForestContainer

/-- A certificate that an action is contained in a recursive forest container. -/
abbrev ForestRealization (A : SolubleAction) (F : ForestContainer) :=
  ActionEmbedding A F.action

/-- Complete a transitive-imprimitive recursion step after recursively realizing the
action inside one block. -/
def ImprimitiveCoordinates.realizeWreath {A F : SolubleAction} {top : PrimitiveNode}
    (C : ImprimitiveCoordinates A F top.action)
    (fibre : TreeContainer) (hF : ActionEmbedding F fibre.action) :
    ForestRealization A (ForestContainer.tree (TreeContainer.wreath fibre top)) :=
  C.embedding.trans (ActionEmbedding.wreathBase hF)

/-! ## Intransitive recursion: splitting off an orbit -/

/-- Equivariant coordinates for a decomposition into two invariant summands.  The
actions on `Left` and `Right` need not be faithful; `SolubleAction.image` quotients
their kernels automatically. -/
structure InvariantSplit (A : SolubleAction) where
  Left : Type u
  Right : Type u
  leftFintype : Fintype Left
  rightFintype : Fintype Right
  leftDecidableEq : DecidableEq Left
  rightDecidableEq : DecidableEq Right
  leftNonempty : Nonempty Left
  rightNonempty : Nonempty Right
  leftAction : MulAction A.Actor Left
  rightAction : MulAction A.Actor Right
  coordinates : A.Point ≃ Left ⊕ Right
  map_smul_left : ∀ (g : A.Actor) (x : Left),
    coordinates (g • coordinates.symm (Sum.inl x)) = Sum.inl (g • x)
  map_smul_right : ∀ (g : A.Actor) (x : Right),
    coordinates (g • coordinates.symm (Sum.inr x)) = Sum.inr (g • x)

attribute [instance] InvariantSplit.leftFintype InvariantSplit.rightFintype
  InvariantSplit.leftDecidableEq InvariantSplit.rightDecidableEq
  InvariantSplit.leftNonempty InvariantSplit.rightNonempty
  InvariantSplit.leftAction InvariantSplit.rightAction

namespace InvariantSplit

variable {A : SolubleAction}

/-- The two faithful image actions attached to an invariant split. -/
abbrev leftModel (S : InvariantSplit A) : SolubleAction := A.image S.Left

abbrev rightModel (S : InvariantSplit A) : SolubleAction := A.image S.Right

/-- The original action embeds, support-preservingly, in the direct sum of the two
faithful image actions. -/
def embedding (S : InvariantSplit A) :
    ActionEmbedding A (SolubleAction.sum S.leftModel S.rightModel) := by
  let f : A.Actor →* S.leftModel.Actor × S.rightModel.Actor :=
    (A.imageHom S.Left).prod (A.imageHom S.Right)
  refine ActionEmbedding.ofEquivariant A _ f S.coordinates ?_
  intro g x
  rw [← S.coordinates.symm_apply_apply x]
  generalize hy : S.coordinates x = y
  cases y with
  | inl a =>
      change S.coordinates (g • S.coordinates.symm (Sum.inl a)) =
        (SolubleAction.sumSMul S.leftModel S.rightModel).smul (f g)
          (S.coordinates (S.coordinates.symm (Sum.inl a)))
      rw [S.coordinates.apply_symm_apply]
      change S.coordinates (g • S.coordinates.symm (Sum.inl a)) =
        Sum.inl ((A.imageHom S.Left g).1 a)
      rw [S.map_smul_left]
      exact congrArg Sum.inl (A.imageHom_smul S.Left g a).symm
  | inr b =>
      change S.coordinates (g • S.coordinates.symm (Sum.inr b)) =
        (SolubleAction.sumSMul S.leftModel S.rightModel).smul (f g)
          (S.coordinates (S.coordinates.symm (Sum.inr b)))
      rw [S.coordinates.apply_symm_apply]
      change S.coordinates (g • S.coordinates.symm (Sum.inr b)) =
        Sum.inr ((A.imageHom S.Right g).1 b)
      rw [S.map_smul_right]
      exact congrArg Sum.inr (A.imageHom_smul S.Right g b).symm

/-- Complete an intransitive recursion step after recursively realizing the two
faithful component actions. -/
def realizeSum (S : InvariantSplit A) (F₁ F₂ : ForestContainer)
    (h₁ : ForestRealization S.leftModel F₁)
    (h₂ : ForestRealization S.rightModel F₂) :
    ForestRealization A (ForestContainer.sum F₁ F₂) :=
  S.embedding.trans (ActionEmbedding.sum h₁ h₂)

end InvariantSplit

/-- The orbit of `x`, bundled as an invariant subaction. -/
def SolubleAction.orbitSubaction (A : SolubleAction) (x : A.Point) :
    SubMulAction A.Actor A.Point where
  carrier := MulAction.orbit A.Actor x
  smul_mem' g y hy := MulAction.mapsTo_smul_orbit g x hy

@[simp]
theorem SolubleAction.mem_orbitSubaction (A : SolubleAction) (x y : A.Point) :
    y ∈ A.orbitSubaction x ↔ y ∈ MulAction.orbit A.Actor x := Iff.rfl

/-- If the orbit of `x` is proper, it and its complement give an invariant split. -/
noncomputable def SolubleAction.orbitSplit (A : SolubleAction) (x : A.Point)
    (hproper : MulAction.orbit A.Actor x ≠ Set.univ) : InvariantSplit A := by
  classical
  let O : SubMulAction A.Actor A.Point := A.orbitSubaction x
  let Oc : SubMulAction A.Actor A.Point := Oᶜ
  have hOne : Nonempty O :=
    ⟨⟨x, MulAction.mem_orbit_self x⟩⟩
  have hCompl : Nonempty Oc := by
    by_contra hempty
    apply hproper
    apply Set.eq_univ_of_forall
    intro y
    by_contra hy
    exact hempty ⟨⟨y, hy⟩⟩
  letI : Nonempty O := hOne
  letI : Nonempty Oc := hCompl
  exact
    { Left := O
      Right := Oc
      leftFintype := inferInstance
      rightFintype := inferInstance
      leftDecidableEq := inferInstance
      rightDecidableEq := inferInstance
      leftNonempty := inferInstance
      rightNonempty := inferInstance
      leftAction := inferInstance
      rightAction := inferInstance
      coordinates := (Equiv.Set.sumCompl (O : Set A.Point)).symm
      map_smul_left := by
        intro g y
        change (Equiv.Set.sumCompl (O : Set A.Point)).symm (g • (y : A.Point)) =
          Sum.inl (g • y)
        rw [Equiv.Set.sumCompl_symm_apply_of_mem (O.smul_mem g y.property)]
        apply congrArg Sum.inl
        apply Subtype.ext
        rfl
      map_smul_right := by
        intro g y
        have hnot : g • (y : A.Point) ∉ (O : Set A.Point) := (g • y).property
        change (Equiv.Set.sumCompl (O : Set A.Point)).symm (g • (y : A.Point)) =
          Sum.inr (g • y)
        rw [Equiv.Set.sumCompl_symm_apply_of_notMem hnot]
        apply congrArg Sum.inr
        apply Subtype.ext
        rfl }

/-- Both orbit pieces in a proper orbit split have strictly smaller degree than the
original action. -/
theorem SolubleAction.card_orbitSubaction_lt (A : SolubleAction) (x : A.Point)
    (hproper : MulAction.orbit A.Actor x ≠ Set.univ) :
    Nat.card (A.orbitSubaction x) < A.degree := by
  classical
  letI := Fintype.ofFinite (A.orbitSubaction x)
  rw [← Fintype.card_eq_nat_card]
  apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
  intro hsurj
  apply hproper
  apply Set.eq_univ_of_forall
  intro y
  rcases hsurj y with ⟨z, rfl⟩
  exact z.property

theorem SolubleAction.card_orbit_compl_lt (A : SolubleAction) (x : A.Point) :
    Nat.card {y : A.Point // y ∉ MulAction.orbit A.Actor x} < A.degree := by
  classical
  letI := Fintype.ofFinite {y : A.Point // y ∉ MulAction.orbit A.Actor x}
  rw [← Fintype.card_eq_nat_card]
  apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
  intro hsurj
  obtain ⟨y, hy⟩ := hsurj x
  apply y.property
  rw [hy]
  exact MulAction.mem_orbit_self x

/-! ## Block systems and the imprimitive interface -/

/-- The type of translates of a fixed set `B`.  When `B` is a nonempty block in a
transitive action, Mathlib proves that these translates partition the point set. -/
abbrev BlockOrbit (A : SolubleAction) (B : Set A.Point) :=
  {C : Set A.Point // C ∈ Set.range fun g : A.Actor ↦ g • B}

namespace BlockOrbit

instance (A : SolubleAction) (B : Set A.Point) : Nonempty (BlockOrbit A B) :=
  ⟨⟨B, ⟨1, by simp⟩⟩⟩

noncomputable instance (A : SolubleAction) (B : Set A.Point) :
    Fintype (BlockOrbit A B) := Fintype.ofFinite _

noncomputable instance (A : SolubleAction) (B : Set A.Point) :
    DecidableEq (BlockOrbit A B) := Classical.decEq _

instance (A : SolubleAction) (B : Set A.Point) : SMul A.Actor (BlockOrbit A B) where
  smul g C := by
    refine ⟨g • (C : Set A.Point), ?_⟩
    rcases C.property with ⟨h, hh⟩
    refine ⟨g * h, ?_⟩
    rw [← hh]
    change (g * h) • B = g • (h • B)
    rw [mul_smul]

instance (A : SolubleAction) (B : Set A.Point) : MulAction A.Actor (BlockOrbit A B) where
  one_smul C := by
    apply Subtype.ext
    change (1 : A.Actor) • (C : Set A.Point) = (C : Set A.Point)
    rw [one_smul]
  mul_smul g h C := by
    apply Subtype.ext
    change (g * h) • (C : Set A.Point) = g • h • (C : Set A.Point)
    rw [mul_smul]

@[simp]
theorem coe_smul (A : SolubleAction) (B : Set A.Point) (g : A.Actor)
    (C : BlockOrbit A B) :
    ((g • C : BlockOrbit A B) : Set A.Point) = g • (C : Set A.Point) := rfl

/-- The original actor is transitive on the translates of `B`. -/
instance isPretransitive (A : SolubleAction) (B : Set A.Point) :
    MulAction.IsPretransitive A.Actor (BlockOrbit A B) where
  exists_smul_eq C D := by
    rcases C.property with ⟨c, hc⟩
    rcases D.property with ⟨d, hd⟩
    refine ⟨d * c⁻¹, ?_⟩
    apply Subtype.ext
    rw [coe_smul]
    rw [← hc, ← hd]
    simp [mul_smul]

end BlockOrbit

noncomputable section

/-- Faithful soluble image of the action on the translates of `B`. -/
noncomputable abbrev SolubleAction.blockOrbitModel (A : SolubleAction) (B : Set A.Point) :
    SolubleAction := A.image (BlockOrbit A B)

/-- If the setwise stabilizer of `B` is a maximal proper subgroup, then the faithful
action on the translates of `B` is primitive. -/
theorem SolubleAction.blockOrbitModel_isPreprimitive_of_isCoatom_stabilizer
    (A : SolubleAction) (B : Set A.Point)
    (hco : IsCoatom (MulAction.stabilizer A.Actor B)) :
    MulAction.IsPreprimitive
      (A.blockOrbitModel B).Actor (A.blockOrbitModel B).Point := by
  classical
  let C₀ : BlockOrbit A B := ⟨B, ⟨1, by simp⟩⟩
  have hstabC₀ : MulAction.stabilizer A.Actor C₀ =
      MulAction.stabilizer A.Actor B := by
    ext g
    change g • C₀ = C₀ ↔ g • B = B
    constructor
    · intro hg
      exact congrArg Subtype.val hg
    · intro hg
      apply Subtype.ext
      exact hg
  have hC₀coatom : IsCoatom (MulAction.stabilizer A.Actor C₀) := by
    rwa [hstabC₀]
  have hnontrivial : Nontrivial (BlockOrbit A B) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    have hfix : MulAction.stabilizer A.Actor C₀ = ⊤ := by
      ext g
      simp only [Subgroup.mem_top, iff_true]
      exact hsub.elim (g • C₀) C₀
    exact hC₀coatom.ne_top hfix
  letI : Nontrivial (BlockOrbit A B) := hnontrivial
  have hpre : MulAction.IsPreprimitive A.Actor (BlockOrbit A B) :=
    (MulAction.isCoatom_stabilizer_iff_preprimitive A.Actor C₀).mp hC₀coatom
  exact A.image_isPreprimitive (BlockOrbit A B) hpre

/-- A maximal proper block containing `a` has a primitive induced action on its
translates.  Maximality is expressed intrinsically by `IsCoatom` in Mathlib's
finite poset `BlockMem`. -/
theorem SolubleAction.blockOrbitModel_isPreprimitive_of_isCoatom_blockMem
    (A : SolubleAction) [MulAction.IsPretransitive A.Actor A.Point]
    (a : A.Point) (B : MulAction.BlockMem A.Actor a) (hBmax : IsCoatom B) :
    MulAction.IsPreprimitive
      (A.blockOrbitModel (B : Set A.Point)).Actor
      (A.blockOrbitModel (B : Set A.Point)).Point := by
  classical
  rcases B with ⟨B, haB, hB⟩
  let E := MulAction.block_stabilizerOrderIso A.Actor a
  have hcoIci : IsCoatom (E ⟨B, haB, hB⟩) :=
    (E.isCoatom_iff ⟨B, haB, hB⟩).mpr hBmax
  have hco : IsCoatom (MulAction.stabilizer A.Actor B) := by
    simpa [E, MulAction.block_stabilizerOrderIso] using
      IsCoatom.of_isCoatom_coe_Ici hcoIci
  exact A.blockOrbitModel_isPreprimitive_of_isCoatom_stabilizer B hco

/-- A finite transitive but imprimitive action has a proper nonempty block whose
induced faithful action on block translates is primitive.  The construction enlarges
a nontrivial block stabilizer to a maximal subgroup, so no classification theorem is
used. -/
theorem SolubleAction.exists_block_with_primitive_top (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point]
    (hnot : ¬ MulAction.IsPreprimitive A.Actor A.Point) :
    ∃ B : Set A.Point,
      MulAction.IsBlock A.Actor B ∧ B.Nonempty ∧ B ≠ Set.univ ∧
        MulAction.IsPreprimitive
          (A.blockOrbitModel B).Actor (A.blockOrbitModel B).Point := by
  classical
  letI : Fintype A.Actor := Fintype.ofFinite A.Actor
  letI : Finite (Subgroup A.Actor) :=
    Finite.of_injective (fun H : Subgroup A.Actor ↦ (H : Set A.Actor))
      SetLike.coe_injective
  let a : A.Point := Classical.choice A.pointNonempty
  have hwitness : ∃ W : Set A.Point,
      a ∈ W ∧ MulAction.IsBlock A.Actor W ∧
        ¬ W.Subsingleton ∧ W ≠ Set.univ := by
    by_contra h
    apply hnot
    refine MulAction.IsPreprimitive.of_isTrivialBlock_base a ?_
    intro W haW hW
    by_cases hs : W.Subsingleton
    · exact Or.inl hs
    · right
      by_contra hu
      exact h ⟨W, haW, hW, hs, hu⟩
  obtain ⟨W, haW, hW, _hWnonsingleton, hWproper⟩ := hwitness
  have hstabWproper : MulAction.stabilizer A.Actor W ≠ ⊤ := by
    intro htop
    apply hWproper
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq A.Actor a y
    have hg : g ∈ MulAction.stabilizer A.Actor W := by
      rw [htop]
      exact Subgroup.mem_top g
    have hga : g • a ∈ g • W := Set.smul_mem_smul_set_iff.mpr haW
    rwa [show g • W = W from hg] at hga
  obtain ⟨H, hHcoatom, hWH⟩ :=
    (eq_top_or_exists_le_coatom (MulAction.stabilizer A.Actor W)).resolve_left
      hstabWproper
  have hstab_a_H : MulAction.stabilizer A.Actor a ≤ H :=
    (hW.stabilizer_le haW).trans hWH
  let B : Set A.Point := MulAction.orbit H a
  have haB : a ∈ B := MulAction.mem_orbit_self a
  have hB : MulAction.IsBlock A.Actor B := MulAction.IsBlock.of_orbit hstab_a_H
  have hstabB : MulAction.stabilizer A.Actor B = H :=
    MulAction.stabilizer_orbit_eq hstab_a_H
  have hBproper : B ≠ Set.univ := by
    intro htop
    have hstabtop : MulAction.stabilizer A.Actor B = ⊤ := by
      rw [htop]
      ext g
      simp
    exact hHcoatom.ne_top (hstabB.symm.trans hstabtop)
  have hcoB : IsCoatom (MulAction.stabilizer A.Actor B) := by
    rwa [hstabB]
  exact ⟨B, hB, ⟨a, haB⟩, hBproper,
    A.blockOrbitModel_isPreprimitive_of_isCoatom_stabilizer B hcoB⟩

/-- The translates of a nonempty block form a partition.  This is the direct bridge
to Mathlib's block-system API used in the imprimitive recursion. -/
theorem SolubleAction.blockOrbit_isPartition (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    Setoid.IsPartition (Set.range fun g : A.Actor ↦ g • B) :=
  (hB.isBlockSystem hBne).1

/-- Degree factorization for a block and its system of translates. -/
theorem SolubleAction.ncard_block_mul_ncard_blockOrbit (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    Set.ncard B * Set.ncard (MulAction.orbit A.Actor B) = A.degree := by
  simpa [SolubleAction.degree, Nat.card_eq_fintype_card] using
    hB.ncard_block_mul_ncard_orbit_eq hBne

/-- Restrict the actor of a faithful soluble action to a subgroup. -/
abbrev SolubleAction.restrictActor (A : SolubleAction) (S : Subgroup A.Actor) :
    SolubleAction where
  Point := A.Point
  Actor := S
  pointFintype := inferInstance
  pointDecidableEq := inferInstance
  pointNonempty := inferInstance
  actorGroup := inferInstance
  actorFinite := inferInstance
  action := inferInstance
  faithful := inferInstance
  soluble := inferInstance

/-- The chosen block, as an invariant subaction of its setwise stabilizer. -/
def blockSubaction (A : SolubleAction) (B : Set A.Point) :
    SubMulAction (MulAction.stabilizer A.Actor B) A.Point where
  carrier := B
  smul_mem' g x hx := by
    have hx' : (g : A.Actor) • x ∈ (g : A.Actor) • B :=
      Set.smul_mem_smul_set_iff.mpr hx
    have hg : (g : A.Actor) • B = B := g.property
    rw [hg] at hx'
    exact hx'

/-- Faithful soluble image of the setwise block stabilizer on the chosen block. -/
noncomputable abbrev SolubleAction.blockFibreModel (A : SolubleAction)
    (B : Set A.Point) (hBne : B.Nonempty) : SolubleAction := by
  let Y := blockSubaction A B
  letI : Nonempty Y := ⟨⟨hBne.choose, hBne.choose_spec⟩⟩
  letI : Fintype Y := Fintype.ofFinite Y
  exact (A.restrictActor (MulAction.stabilizer A.Actor B)).image Y

/-- The setwise stabilizer of a block is transitive on that block, and hence so is
its faithful permutation image. -/
theorem SolubleAction.blockFibreModel_isPretransitive (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    MulAction.IsPretransitive
      (A.blockFibreModel B hBne).Actor (A.blockFibreModel B hBne).Point := by
  let Y := blockSubaction A B
  letI : Nonempty Y := ⟨⟨hBne.choose, hBne.choose_spec⟩⟩
  letI : Fintype Y := Fintype.ofFinite Y
  have hlocal : MulAction.IsPretransitive
      (MulAction.stabilizer A.Actor B) Y :=
    { exists_smul_eq := by
        intro x y
        obtain ⟨g, hg⟩ :=
          MulAction.exists_smul_eq A.Actor (x : A.Point) (y : A.Point)
        have hgy : g • (x : A.Point) ∈ B := by
          rw [hg]
          exact y.property
        have hgB : g • B = B := hB.smul_eq_of_mem x.property hgy
        refine ⟨⟨g, hgB⟩, ?_⟩
        apply Subtype.ext
        exact hg }
  let R := A.restrictActor (MulAction.stabilizer A.Actor B)
  change MulAction.IsPretransitive (R.image Y).Actor (R.image Y).Point
  exact R.image_isPretransitive Y hlocal

/-- A proper nonempty block has strictly smaller degree than the original action. -/
theorem SolubleAction.blockFibreModel_degree_lt (A : SolubleAction)
    {B : Set A.Point} (hBne : B.Nonempty) (hBproper : B ≠ Set.univ) :
    (A.blockFibreModel B hBne).degree < A.degree := by
  classical
  let Y := blockSubaction A B
  letI : Nonempty Y := ⟨⟨hBne.choose, hBne.choose_spec⟩⟩
  letI : Fintype Y := Fintype.ofFinite Y
  change Fintype.card Y < Fintype.card A.Point
  apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
  intro hsurj
  apply hBproper
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy]
  exact y.property

/-- A representative carrying `B` to the block `C`. -/
noncomputable def BlockOrbit.rep (A : SolubleAction) (B : Set A.Point)
    (C : BlockOrbit A B) : A.Actor :=
  Classical.choose C.property

theorem BlockOrbit.rep_spec (A : SolubleAction) (B : Set A.Point)
    (C : BlockOrbit A B) :
    BlockOrbit.rep A B C • B = (C : Set A.Point) :=
  Classical.choose_spec C.property

/-- A chosen representative identifies the base block with any translate. -/
noncomputable def BlockOrbit.fibreEquiv (A : SolubleAction) (B : Set A.Point)
    (C : BlockOrbit A B) : B ≃ (C : Set A.Point) where
  toFun x := by
    refine ⟨BlockOrbit.rep A B C • (x : A.Point), ?_⟩
    rw [← BlockOrbit.rep_spec A B C]
    exact Set.smul_mem_smul_set_iff.mpr x.property
  invFun y := by
    refine ⟨(BlockOrbit.rep A B C)⁻¹ • (y : A.Point), ?_⟩
    have hy : (y : A.Point) ∈ BlockOrbit.rep A B C • B := by
      rw [BlockOrbit.rep_spec A B C]
      exact y.property
    rcases Set.mem_smul_set.mp hy with ⟨z, hz, hzy⟩
    rw [← hzy]
    simpa using hz
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- The indexed translates of a nonempty block contain every point uniquely. -/
theorem BlockOrbit.existsUnique_mem (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) (x : A.Point) :
    ∃! C : BlockOrbit A B, x ∈ (C : Set A.Point) := by
  rcases (A.blockOrbit_isPartition hB hBne).2 x with ⟨C, ⟨hCrange, hx⟩, huniq⟩
  refine ⟨⟨C, hCrange⟩, hx, ?_⟩
  intro D hD
  apply Subtype.ext
  exact huniq (D : Set A.Point) ⟨D.property, hD⟩

/-- Canonical block coordinates obtained from a transversal of the block system. -/
noncomputable def BlockOrbit.pointEquiv (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    A.Point ≃ BlockOrbit A B × B :=
  (Set.sigmaEquiv (fun C : BlockOrbit A B ↦ (C : Set A.Point))
      (BlockOrbit.existsUnique_mem A hB hBne)).symm |>.trans
    (Equiv.sigmaEquivProdOfEquiv fun C ↦ (BlockOrbit.fibreEquiv A B C).symm)

/-- Decoding block coordinates has the expected transversal formula. -/
@[simp]
theorem BlockOrbit.pointEquiv_symm_apply (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty)
    (C : BlockOrbit A B) (x : B) :
    (BlockOrbit.pointEquiv A hB hBne).symm (C, x) =
      BlockOrbit.rep A B C • (x : A.Point) := rfl

/-- Canonical map from the setwise block stabilizer to its faithful action on `B`. -/
noncomputable def blockFibreHom (A : SolubleAction) (B : Set A.Point)
    (hBne : B.Nonempty) :
    MulAction.stabilizer A.Actor B →* (A.blockFibreModel B hBne).Actor := by
  let Y := blockSubaction A B
  letI : Nonempty Y := ⟨⟨hBne.choose, hBne.choose_spec⟩⟩
  letI : Fintype Y := Fintype.ofFinite Y
  exact (A.restrictActor (MulAction.stabilizer A.Actor B)).imageHom Y

@[simp]
theorem blockFibreHom_apply (A : SolubleAction) (B : Set A.Point)
    (hBne : B.Nonempty) (g : MulAction.stabilizer A.Actor B)
    (x : blockSubaction A B) :
    (blockFibreHom A B hBne g).1 x = g • x := rfl

/-- The local Schreier section attached to `g` at the output block `C`. -/
noncomputable def blockSection (A : SolubleAction) (B : Set A.Point)
    (g : A.Actor) (C : BlockOrbit A B) : MulAction.stabilizer A.Actor B := by
  let D : BlockOrbit A B := g⁻¹ • C
  refine ⟨(BlockOrbit.rep A B C)⁻¹ * g * BlockOrbit.rep A B D, ?_⟩
  change ((BlockOrbit.rep A B C)⁻¹ * g * BlockOrbit.rep A B D) • B = B
  calc
    ((BlockOrbit.rep A B C)⁻¹ * g * BlockOrbit.rep A B D) • B =
        (BlockOrbit.rep A B C)⁻¹ •
          (g • (BlockOrbit.rep A B D • B)) := by simp only [mul_smul]
    _ = (BlockOrbit.rep A B C)⁻¹ •
          (g • (D : Set A.Point)) := by rw [BlockOrbit.rep_spec]
    _ = (BlockOrbit.rep A B C)⁻¹ •
          (g • (g⁻¹ • (C : Set A.Point))) := by
            rw [BlockOrbit.coe_smul]
    _ = (BlockOrbit.rep A B C)⁻¹ • (C : Set A.Point) := by simp
    _ = (BlockOrbit.rep A B C)⁻¹ •
          (BlockOrbit.rep A B C • B) := by rw [BlockOrbit.rep_spec]
    _ = B := by simp

@[simp]
theorem blockSection_one (A : SolubleAction) (B : Set A.Point)
    (C : BlockOrbit A B) : blockSection A B 1 C = 1 := by
  apply Subtype.ext
  simp [blockSection]

/-- Schreier sections satisfy the cocycle identity used by wreath multiplication. -/
theorem blockSection_mul (A : SolubleAction) (B : Set A.Point)
    (g h : A.Actor) (C : BlockOrbit A B) :
    blockSection A B (g * h) C =
      blockSection A B g C * blockSection A B h (g⁻¹ • C) := by
  apply Subtype.ext
  simp only [blockSection, Subgroup.coe_mk, Subgroup.coe_mul]
  change
    (BlockOrbit.rep A B C)⁻¹ * (g * h) *
        BlockOrbit.rep A B ((g * h)⁻¹ • C) =
      ((BlockOrbit.rep A B C)⁻¹ * g * BlockOrbit.rep A B (g⁻¹ • C)) *
        ((BlockOrbit.rep A B (g⁻¹ • C))⁻¹ * h *
          BlockOrbit.rep A B (h⁻¹ • (g⁻¹ • C)))
  rw [mul_inv_rev, mul_smul]
  group

@[simp]
theorem coe_blockSection_smul (A : SolubleAction) (B : Set A.Point)
    (g : A.Actor) (C : BlockOrbit A B) :
    (blockSection A B g (g • C) : A.Actor) =
      (BlockOrbit.rep A B (g • C))⁻¹ * g * BlockOrbit.rep A B C := by
  simp [blockSection]

/-- The canonical Schreier homomorphism into the natural wreath product. -/
noncomputable def blockWreathHom (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    A.Actor →*
      (SolubleAction.wreath (A.blockFibreModel B hBne) (A.blockOrbitModel B)).Actor where
  toFun g :=
    ⟨fun C ↦ blockFibreHom A B hBne (blockSection A B g C),
      A.imageHom (BlockOrbit A B) g⟩
  map_one' := by
    apply PermWreath.ext
    · funext C
      simp
    · change A.imageHom (BlockOrbit A B) 1 = 1
      rw [map_one]
  map_mul' g h := by
    apply PermWreath.ext
    · funext C
      change blockFibreHom A B hBne (blockSection A B (g * h) C) =
        blockFibreHom A B hBne (blockSection A B g C) *
          blockFibreHom A B hBne
            (blockSection A B h ((A.imageHom (BlockOrbit A B) g)⁻¹ • C))
      rw [blockSection_mul]
      rw [map_mul]
      congr 2
    · change A.imageHom (BlockOrbit A B) (g * h) =
        A.imageHom (BlockOrbit A B) g * A.imageHom (BlockOrbit A B) h
      rw [map_mul]

/-- Decoding after the wreath action agrees with the original action. -/
theorem BlockOrbit.pointEquiv_symm_wreath_smul (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty)
    (g : A.Actor) (C : BlockOrbit A B) (x : blockSubaction A B) :
    (BlockOrbit.pointEquiv A hB hBne).symm
        (blockWreathHom A hB hBne g • (C, x)) =
      g • (BlockOrbit.pointEquiv A hB hBne).symm (C, x) := by
  change
    BlockOrbit.rep A B (g • C) •
        ((blockSection A B g (g • C) : A.Actor) • (x : A.Point)) =
      g • (BlockOrbit.rep A B C • (x : A.Point))
  rw [coe_blockSection_smul]
  simp [mul_smul]

/-- The same coordinate equivalence with its codomain stated through the two action
models, which makes the stored wreath action available to typeclass inference. -/
noncomputable abbrev BlockOrbit.modelPointEquiv (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    A.Point ≃ (A.blockOrbitModel B).Point × (A.blockFibreModel B hBne).Point :=
  BlockOrbit.pointEquiv A hB hBne

/-- Encoding is equivariant for the canonical Schreier wreath homomorphism. -/
theorem BlockOrbit.pointEquiv_wreath_smul (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty)
    (g : A.Actor) (x : A.Point) :
    BlockOrbit.modelPointEquiv A hB hBne (g • x) =
      blockWreathHom A hB hBne g • BlockOrbit.modelPointEquiv A hB hBne x := by
  let E := BlockOrbit.modelPointEquiv A hB hBne
  have hd := BlockOrbit.pointEquiv_symm_wreath_smul A hB hBne g (E x).1 (E x).2
  change E.symm (blockWreathHom A hB hBne g • E x) =
    g • E.symm (E x) at hd
  apply E.symm.injective
  calc
    E.symm (E (g • x)) = g • x := E.symm_apply_apply _
    _ = E.symm (blockWreathHom A hB hBne g • E x) := by
      simpa only [Prod.eta, E.symm_apply_apply] using hd.symm

/-- The canonical transversal construction supplies the full equivariant wreath
coordinates; no classification theorem is used. -/
noncomputable def canonicalImprimitiveCoordinates (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty) :
    ImprimitiveCoordinates A (A.blockFibreModel B hBne) (A.blockOrbitModel B) where
  actorHom := blockWreathHom A hB hBne
  pointEquiv := BlockOrbit.modelPointEquiv A hB hBne
  map_smul := BlockOrbit.pointEquiv_wreath_smul A hB hBne

/-- A chosen block system together with explicit Schreier wreath coordinates.  This
record is the exact constructive input needed to turn a transitive-imprimitive node
into the abstract `ImprimitiveCoordinates` used above. -/
structure BlockWreathData (A F : SolubleAction) (B : Set A.Point) where
  topPrimitive :
    MulAction.IsPreprimitive (A.blockOrbitModel B).Actor (A.blockOrbitModel B).Point
  coordinates : ImprimitiveCoordinates A F (A.blockOrbitModel B)

namespace BlockWreathData

/-- The canonical transversal construction fills the wreath-coordinate part of a
block certificate.  The only remaining structural choice is a block whose induced
top action is primitive (for example, a maximal proper block). -/
noncomputable def canonical (A : SolubleAction)
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty)
    (hTop : MulAction.IsPreprimitive
      (A.blockOrbitModel B).Actor (A.blockOrbitModel B).Point) :
    BlockWreathData A (A.blockFibreModel B hBne) B where
  topPrimitive := hTop
  coordinates := canonicalImprimitiveCoordinates A hB hBne

/-- A block-wreath certificate performs one recursive wreath step. -/
def realize {A F : SolubleAction} {B : Set A.Point} (D : BlockWreathData A F B)
    (fibre : TreeContainer) (hF : ActionEmbedding F fibre.action) :
    ForestRealization A
      (ForestContainer.tree
        (TreeContainer.wreath fibre ⟨A.blockOrbitModel B, D.topPrimitive⟩)) :=
  D.coordinates.realizeWreath fibre hF

/-- One canonical imprimitive recursion step, stated directly from a block and the
primitivity of its induced top action. -/
noncomputable def realizeCanonical {A : SolubleAction}
    [MulAction.IsPretransitive A.Actor A.Point] {B : Set A.Point}
    (hB : MulAction.IsBlock A.Actor B) (hBne : B.Nonempty)
    (hTop : MulAction.IsPreprimitive
      (A.blockOrbitModel B).Actor (A.blockOrbitModel B).Point)
    (fibre : TreeContainer)
    (hF : ActionEmbedding (A.blockFibreModel B hBne) fibre.action) :
    ForestRealization A
      (ForestContainer.tree
        (TreeContainer.wreath fibre ⟨A.blockOrbitModel B, hTop⟩)) :=
  (canonical A hB hBne hTop).realize fibre hF

end BlockWreathData

/-! ## Complete degree induction -/

/-- A transitive finite faithful soluble action, with actor and points in the same
universe, embeds in one recursive primitive-wreath tree. -/
theorem SolubleAction.exists_tree_realization_sameUniverse
    (A : SolubleAction.{u, u}) [MulAction.IsPretransitive A.Actor A.Point] :
    Nonempty (Σ T : TreeContainer.{u}, ActionEmbedding A T.action) := by
  let P : ℕ → Prop := fun n ↦ ∀ A : SolubleAction.{u, u},
    MulAction.IsPretransitive A.Actor A.Point → A.degree = n →
      Nonempty (Σ T : TreeContainer.{u}, ActionEmbedding A T.action)
  refine (Nat.strong_induction_on A.degree (p := P) ?_) A (inferInstance) rfl
  intro n ih A htrans hdegree
  letI : MulAction.IsPretransitive A.Actor A.Point := htrans
  by_cases hprimitive : MulAction.IsPreprimitive A.Actor A.Point
  · exact ⟨⟨TreeContainer.primitive ⟨A, hprimitive⟩,
      ActionEmbedding.refl A⟩⟩
  · obtain ⟨B, hB, hBne, hBproper, hTop⟩ :=
      A.exists_block_with_primitive_top hprimitive
    let F := A.blockFibreModel B hBne
    have htransF : MulAction.IsPretransitive F.Actor F.Point :=
      A.blockFibreModel_isPretransitive hB hBne
    have hlt : F.degree < n := by
      rw [← hdegree]
      exact A.blockFibreModel_degree_lt hBne hBproper
    obtain ⟨⟨T, hT⟩⟩ := ih F.degree hlt F htransF rfl
    let top : PrimitiveNode.{u} := ⟨A.blockOrbitModel B, hTop⟩
    refine ⟨⟨TreeContainer.wreath T top, ?_⟩⟩
    exact BlockWreathData.realizeCanonical hB hBne hTop T hT

/-- An arbitrary finite faithful soluble action embeds in a recursive forest after
normalizing its actor to its faithful permutation image.  The point equivalence in
the returned `ActionEmbedding` makes the container degree exactly `A.degree`. -/
theorem SolubleAction.exists_forest_realization_sameUniverse
    (A : SolubleAction.{u, u}) :
    Nonempty (Σ F : ForestContainer.{u}, ForestRealization A F) := by
  let P : ℕ → Prop := fun n ↦ ∀ A : SolubleAction.{u, u}, A.degree = n →
    Nonempty (Σ F : ForestContainer.{u}, ForestRealization A F)
  refine (Nat.strong_induction_on A.degree (p := P) ?_) A rfl
  intro n ih A hdegree
  by_cases htrans : MulAction.IsPretransitive A.Actor A.Point
  · letI : MulAction.IsPretransitive A.Actor A.Point := htrans
    obtain ⟨⟨T, hT⟩⟩ := A.exists_tree_realization_sameUniverse
    exact ⟨⟨ForestContainer.tree T, hT⟩⟩
  · let x : A.Point := Classical.choice A.pointNonempty
    have horbitProper : MulAction.orbit A.Actor x ≠ Set.univ := by
      intro horbit
      apply htrans
      exact (MulAction.isPretransitive_iff_orbit_eq_univ x).mpr horbit
    let S := A.orbitSplit x horbitProper
    have hsum : A.degree = S.leftModel.degree + S.rightModel.degree := by
      calc
        A.degree = (SolubleAction.sum S.leftModel S.rightModel).degree :=
          S.embedding.degree_eq
        _ = S.leftModel.degree + S.rightModel.degree :=
          SolubleAction.degree_sum _ _
    have hleftPos : 0 < S.leftModel.degree := Fintype.card_pos
    have hrightPos : 0 < S.rightModel.degree := Fintype.card_pos
    have hleftLt : S.leftModel.degree < n := by omega
    have hrightLt : S.rightModel.degree < n := by omega
    obtain ⟨⟨F₁, hF₁⟩⟩ := ih S.leftModel.degree hleftLt S.leftModel rfl
    obtain ⟨⟨F₂, hF₂⟩⟩ := ih S.rightModel.degree hrightLt S.rightModel rfl
    exact ⟨⟨ForestContainer.sum F₁ F₂, S.realizeSum F₁ F₂ hF₁ hF₂⟩⟩

/-- Universe-polymorphic transitive form of the tree realization theorem. -/
theorem SolubleAction.exists_tree_realization (A : SolubleAction.{u, v})
    [MulAction.IsPretransitive A.Actor A.Point] :
    Nonempty (Σ T : TreeContainer.{u}, ActionEmbedding A T.action) := by
  let I : SolubleAction.{u, u} := A.image A.Point
  have htransI : MulAction.IsPretransitive I.Actor I.Point :=
    A.image_isPretransitive A.Point (inferInstance :
      MulAction.IsPretransitive A.Actor A.Point)
  letI : MulAction.IsPretransitive I.Actor I.Point := htransI
  obtain ⟨⟨T, hT⟩⟩ := I.exists_tree_realization_sameUniverse
  exact ⟨⟨T, (ActionEmbedding.toImage A).trans hT⟩⟩

/-- Every finite faithful soluble action embeds, with exact degree and exact support
preservation, in a forest of iterated primitive permutational wreath products. -/
theorem SolubleAction.exists_forest_realization (A : SolubleAction.{u, v}) :
    Nonempty (Σ F : ForestContainer.{u}, ForestRealization A F) := by
  let I : SolubleAction.{u, u} := A.image A.Point
  obtain ⟨⟨F, hF⟩⟩ := I.exists_forest_realization_sameUniverse
  exact ⟨⟨F, (ActionEmbedding.toImage A).trans hF⟩⟩

/-- A chosen forest certificate, useful to downstream counting code that needs data
rather than mere nonemptiness. -/
noncomputable def SolubleAction.forestRealizationData (A : SolubleAction.{u, v}) :
    Σ F : ForestContainer.{u}, ForestRealization A F :=
  Classical.choice A.exists_forest_realization

/-! ## Symmetric-group specialization, including degree zero -/

/-- In degree zero every subgroup of the symmetric group is trivial. -/
theorem SolubleSubgroup.eq_bot_of_degree_zero (H : SolubleSubgroup 0) :
    H = SolubleSubgroup.bot 0 := by
  apply SolubleSubgroup.ext
  apply (Subgroup.eq_bot_iff_forall H.carrier).mpr
  intro g _hg
  exact Subsingleton.elim g 1

/-- The faithful action associated to a positive-degree soluble subgroup. -/
noncomputable def SolubleSubgroup.positiveAction {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) : SolubleAction.{0, 0} := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact SolubleAction.ofSubgroup H.carrier H.isSolvable

@[simp]
theorem SolubleSubgroup.positiveAction_degree {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) :
    (H.positiveAction hn).degree = n := by
  exact Fintype.card_fin n

/-- Every positive-degree soluble subgroup of `Sym n` has a support-preserving
embedding into a recursive primitive-wreath forest of degree exactly `n`.  Degree
zero is covered separately by `SolubleSubgroup.eq_bot_of_degree_zero`. -/
theorem SolubleSubgroup.exists_forest_realization {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) :
    Nonempty (Σ F : ForestContainer.{0},
      ForestRealization (H.positiveAction hn) F) :=
  (H.positiveAction hn).exists_forest_realization

end

end Kourovka213

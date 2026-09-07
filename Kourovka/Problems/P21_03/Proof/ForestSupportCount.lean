import Kourovka.Problems.P21_03.Proof.ForestContainer
import Kourovka.Problems.P21_03.Proof.NoncoreReduction
import Kourovka.Problems.P21_03.Proof.PrimitiveSolvable
import Kourovka.Problems.P21_03.Proof.AtomCountArithmetic
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Support counting through recursive forest containers

This file records the exact, classification-free interface between the structural
forest embedding and later support-slice estimates.  An `ActionEmbedding` preserves
the moved-point set up to equivalence, hence preserves support cardinality exactly
and injects every support slice into the corresponding slice of the container.
-/

namespace Kourovka213

universe u v w z

/-- Conjugating permutations along an equivalence is a multiplicative equivalence. -/
def permCongrMulEquiv {X : Type u} {Y : Type w} (e : X ≃ Y) :
    Equiv.Perm X ≃* Equiv.Perm Y where
  toEquiv := e.permCongr
  map_mul' f g := by
    ext x
    simp [Equiv.permCongr_apply]

namespace SolubleAction

/-- The moved points of an actor element. -/
def supportFinset (A : SolubleAction) (g : A.Actor) : Finset A.Point :=
  Finset.univ.filter fun x ↦ g • x ≠ x

@[simp]
theorem mem_supportFinset (A : SolubleAction) (g : A.Actor) (x : A.Point) :
    x ∈ A.supportFinset g ↔ g • x ≠ x := by
  simp [supportFinset]

/-- Support size in an abstract finite faithful action. -/
def supportCard (A : SolubleAction) (g : A.Actor) : ℕ :=
  (A.supportFinset g).card

/-- Elements of the acting group having support exactly `s`. -/
noncomputable def actionSupportSlice (A : SolubleAction) (s : ℕ) : Finset A.Actor := by
  classical
  letI : Fintype A.Actor := Fintype.ofFinite A.Actor
  exact Finset.univ.filter fun g ↦ A.supportCard g = s

@[simp]
theorem mem_actionSupportSlice (A : SolubleAction) (s : ℕ) (g : A.Actor) :
    g ∈ A.actionSupportSlice s ↔ A.supportCard g = s := by
  classical
  simp [actionSupportSlice]

end SolubleAction

namespace ActionEmbedding

/-- Transport the full target actor back to permutations of the source point set. -/
def transportedTargetHom {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : B.Actor →* Equiv.Perm A.Point :=
  (permCongrMulEquiv f.pointEquiv.symm).toMonoidHom.comp B.toPermHom

/-- Transporting a faithful target action along a point equivalence remains faithful. -/
theorem transportedTargetHom_injective
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : Function.Injective f.transportedTargetHom := by
  intro g h hgh
  apply B.toPermHom_injective
  apply (permCongrMulEquiv f.pointEquiv.symm).injective
  exact hgh

@[simp]
theorem transportedTargetHom_actorHom_apply
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : A.Actor) (x : A.Point) :
    f.transportedTargetHom (f.actorHom g) x = g • x := by
  change f.pointEquiv.symm (f.actorHom g • f.pointEquiv x) = g • x
  rw [← f.map_smul, f.pointEquiv.symm_apply_apply]

/-- The full target permutation group, transported to the original point set. -/
def targetEnvelope {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : Subgroup (Equiv.Perm A.Point) :=
  f.transportedTargetHom.range

/-- The full target actor is isomorphic to its transported permutation envelope. -/
noncomputable def targetEnvelopeMulEquiv
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : B.Actor ≃* f.targetEnvelope :=
  MulEquiv.ofBijective f.transportedTargetHom.rangeRestrict
    ⟨(fun _ _ h ↦ f.transportedTargetHom_injective (congrArg Subtype.val h)),
      f.transportedTargetHom.rangeRestrict_surjective⟩

@[simp]
theorem targetEnvelopeMulEquiv_coe
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : B.Actor) :
    ((f.targetEnvelopeMulEquiv g : f.targetEnvelope) : Equiv.Perm A.Point) =
      f.transportedTargetHom g := rfl

/-- Pointwise description of the transported target permutation. -/
@[simp]
theorem transportedTargetHom_apply
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : B.Actor) (x : A.Point) :
    f.transportedTargetHom g x = f.pointEquiv.symm (g • f.pointEquiv x) := rfl

/-- The transported target permutation and the original target actor have
equivalent moved-point sets. -/
def transportedSupportEquiv
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : B.Actor) :
    {y : B.Point // y ∈ B.supportFinset g} ≃
      {x : A.Point // x ∈ (f.transportedTargetHom g).support} where
  toFun y := ⟨f.pointEquiv.symm y, by
    rw [Equiv.Perm.mem_support]
    simp only [f.transportedTargetHom_apply, f.pointEquiv.apply_symm_apply]
    exact fun h ↦ (B.mem_supportFinset g y).mp y.property
      (f.pointEquiv.symm.injective h)⟩
  invFun x := ⟨f.pointEquiv x, by
    rw [B.mem_supportFinset]
    intro h
    apply Equiv.Perm.mem_support.mp x.property
    rw [f.transportedTargetHom_apply, h, f.pointEquiv.symm_apply_apply]⟩
  left_inv y := by
    apply Subtype.ext
    exact f.pointEquiv.apply_symm_apply y
  right_inv x := by
    apply Subtype.ext
    exact f.pointEquiv.symm_apply_apply x

/-- The target-envelope isomorphism preserves support cardinality exactly. -/
theorem targetEnvelopeMulEquiv_supportCard
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : B.Actor) :
    ((f.targetEnvelopeMulEquiv g : f.targetEnvelope) : Equiv.Perm A.Point).support.card =
      B.supportCard g := by
  calc
    ((f.targetEnvelopeMulEquiv g : f.targetEnvelope) : Equiv.Perm A.Point).support.card =
        Fintype.card {x // x ∈ (f.transportedTargetHom g).support} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {y // y ∈ B.supportFinset g} :=
      Fintype.card_congr (f.transportedSupportEquiv g).symm
    _ = B.supportCard g := Fintype.card_coe _

/-- The transported target is soluble. -/
theorem targetEnvelope_isSolvable
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : Group.IsSolvable f.targetEnvelope :=
  Group.isSolvable_of_surjective f.transportedTargetHom.rangeRestrict_surjective

/-- The original permutation image is contained in the transported target. -/
theorem sourceRange_le_targetEnvelope
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) : A.toPermHom.range ≤ f.targetEnvelope := by
  rintro q ⟨g, rfl⟩
  refine ⟨f.actorHom g, ?_⟩
  ext x
  exact f.transportedTargetHom_actorHom_apply g x

/-- The point equivalence of an action embedding restricts to an equivalence of
moved-point sets. -/
def supportEquiv {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : A.Actor) :
    {x : A.Point // x ∈ A.supportFinset g} ≃
      {y : B.Point // y ∈ B.supportFinset (f.actorHom g)} where
  toFun x := ⟨f.pointEquiv x, by
    rw [B.mem_supportFinset, f.map_moved_iff]
    exact (A.mem_supportFinset g x).mp x.property⟩
  invFun y := ⟨f.pointEquiv.symm y, by
    rw [A.mem_supportFinset]
    rw [← f.map_moved_iff]
    simpa using (B.mem_supportFinset (f.actorHom g) y).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact f.pointEquiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact f.pointEquiv.apply_symm_apply y

/-- Action embeddings preserve support cardinality exactly. -/
theorem supportCard_map {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (g : A.Actor) :
    B.supportCard (f.actorHom g) = A.supportCard g := by
  change (B.supportFinset (f.actorHom g)).card = (A.supportFinset g).card
  calc
    (B.supportFinset (f.actorHom g)).card =
        Fintype.card {y // y ∈ B.supportFinset (f.actorHom g)} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {x // x ∈ A.supportFinset g} :=
      Fintype.card_congr (f.supportEquiv g).symm
    _ = (A.supportFinset g).card := Fintype.card_coe _

/-- The actor injection restricts to an embedding of every exact-support slice. -/
noncomputable def supportSliceEmbedding
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (s : ℕ) :
    {g : A.Actor // g ∈ A.actionSupportSlice s} ↪
      {h : B.Actor // h ∈ B.actionSupportSlice s} where
  toFun g := ⟨f.actorHom g, by
    rw [B.mem_actionSupportSlice, f.supportCard_map]
    exact (A.mem_actionSupportSlice s g).mp g.property⟩
  inj' := by
    intro g h heq
    apply Subtype.ext
    apply f.actorHom_injective
    exact congrArg Subtype.val heq

/-- Consequently, a structural container can only enlarge an exact-support slice. -/
theorem card_actionSupportSlice_le
    {A : SolubleAction.{u, v}} {B : SolubleAction.{w, z}}
    (f : ActionEmbedding A B) (s : ℕ) :
    (A.actionSupportSlice s).card ≤ (B.actionSupportSlice s).card := by
  classical
  letI : Fintype A.Actor := Fintype.ofFinite A.Actor
  letI : Fintype B.Actor := Fintype.ofFinite B.Actor
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (f.supportSliceEmbedding s)
      (f.supportSliceEmbedding s).injective

end ActionEmbedding

/-! ## Exponential order bounds for recursive containers -/

/-- A primitive node has order at most `256^(degree-1)`, including the trivial
actor case. -/
theorem PrimitiveNode.actor_natCard_le (P : PrimitiveNode.{u}) :
    Nat.card P.action.Actor ≤ 256 ^ (P.action.degree - 1) := by
  classical
  by_cases hP : Nontrivial P.action.Actor
  · letI : Nontrivial P.action.Actor := hP
    letI : MulAction.IsPreprimitive P.action.Actor P.action.Point := P.preprimitive
    exact natCard_le_256_pow_pred_of_primitive_solvable
      P.action.Actor P.action.Point
  · haveI : Subsingleton P.action.Actor := not_nontrivial_iff_subsingleton.mp hP
    rw [Nat.card_unique]
    exact Nat.one_le_pow' (P.action.degree - 1) 255

/-- The underlying set of a permutational wreath product injects into the product
of its base-function and top coordinates. -/
def permWreathToProdEmbedding (X Q ι : Type*) [Group X] [Group Q]
    [MulAction Q ι] : PermWreath X Q ι ↪ (ι → X) × Q where
  toFun g := (g.left, g.right)
  inj' _ _ h := SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- Every rooted recursive container inherits the sharp exponential order budget
needed to label a portrait atom. -/
theorem TreeContainer.actor_natCard_le : ∀ T : TreeContainer.{u},
    Nat.card T.action.Actor ≤ 256 ^ (T.degree - 1)
  | .primitive P => P.actor_natCard_le
  | .wreath fibre top => by
      classical
      let d := top.action.degree
      let m := fibre.degree
      have hd : 0 < d := Fintype.card_pos
      have hm : 0 < m := Fintype.card_pos
      have hbase := TreeContainer.actor_natCard_le fibre
      have htop := top.actor_natCard_le
      have hcoord :
          Nat.card (TreeContainer.wreath fibre top).action.Actor ≤
            Nat.card ((top.action.Point → fibre.action.Actor) × top.action.Actor) :=
        Nat.card_le_card_of_injective
          (permWreathToProdEmbedding fibre.action.Actor top.action.Actor top.action.Point)
          (permWreathToProdEmbedding fibre.action.Actor top.action.Actor
            top.action.Point).injective
      have hexp : (m - 1) * d + (d - 1) = d * m - 1 := by
        rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm d m]
        have hdm : d ≤ m * d := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hm
        omega
      calc
        Nat.card (TreeContainer.wreath fibre top).action.Actor ≤
            Nat.card ((top.action.Point → fibre.action.Actor) × top.action.Actor) := hcoord
        _ = Nat.card fibre.action.Actor ^ d * Nat.card top.action.Actor := by
          rw [Nat.card_prod, Nat.card_pi]
          simp only [Finset.prod_const, Finset.card_univ]
          rfl
        _ ≤ (256 ^ (m - 1)) ^ d * 256 ^ (d - 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hbase d) htop
        _ = 256 ^ ((m - 1) * d + (d - 1)) := by
          rw [← pow_mul, ← pow_add]
        _ = 256 ^ (d * m - 1) := by rw [hexp]
        _ = 256 ^ ((TreeContainer.wreath fibre top).degree - 1) := by
          rw [TreeContainer.degree_wreath]

/-- A forest actor also has exponential order in its total degree. -/
theorem ForestContainer.actor_natCard_le : ∀ F : ForestContainer.{u},
    Nat.card F.action.Actor ≤ 256 ^ F.degree
  | .tree T => by
      exact (T.actor_natCard_le.trans
        (pow_le_pow_right' (by omega : 1 ≤ (256 : ℕ)) (Nat.sub_le T.degree 1)))
  | .sum F₁ F₂ => by
      calc
        Nat.card (ForestContainer.sum F₁ F₂).action.Actor =
            Nat.card F₁.action.Actor * Nat.card F₂.action.Actor := Nat.card_prod _ _
        _ ≤ 256 ^ F₁.degree * 256 ^ F₂.degree :=
          Nat.mul_le_mul F₁.actor_natCard_le F₂.actor_natCard_le
        _ = 256 ^ (F₁.degree + F₂.degree) := (pow_add _ _ _).symm
        _ = 256 ^ (ForestContainer.sum F₁ F₂).degree := by
          rw [ForestContainer.degree_sum]

/-! ## Nontrivial node locations -/

/-- Locations of nontrivial primitive local actions in a rooted container.
Using `PLift (Nontrivial G)` makes an inert node contribute no location and an
active node contribute exactly one. -/
abbrev ActiveNodeLocation (G : Type u) :=
  ULift.{u} (PLift (Nontrivial G))

noncomputable instance activeNodeLocationFintype (G : Type u) :
    Fintype (ActiveNodeLocation G) := by
  letI : Fintype (PLift (Nontrivial G)) := Fintype.ofFinite _
  exact Fintype.ofFinite _

def ActiveTreeLocation : TreeContainer.{u} → Type u
  | .primitive P => ActiveNodeLocation P.action.Actor
  | .wreath fibre top =>
      ActiveNodeLocation top.action.Actor ⊕
        (top.action.Point × ActiveTreeLocation fibre)

noncomputable instance activeTreeLocationFintype (T : TreeContainer.{u}) :
    Fintype (ActiveTreeLocation T) := by
  induction T with
  | primitive P =>
      simp only [ActiveTreeLocation]
      exact Fintype.ofFinite _
  | wreath fibre top ih =>
      letI : Fintype (ActiveTreeLocation fibre) := ih
      simp only [ActiveTreeLocation]
      infer_instance

private theorem card_plift_nontrivial_le_degree_pred (A : SolubleAction.{u, u}) :
    Nat.card (ActiveNodeLocation A.Actor) ≤ A.degree - 1 := by
  classical
  by_cases hA : Nontrivial A.Actor
  · letI : Nontrivial A.Actor := hA
    letI : Nonempty (ActiveNodeLocation A.Actor) := ⟨⟨⟨hA⟩⟩⟩
    have hdegree : 2 ≤ A.degree :=
      two_le_card_of_faithful_action A.Actor A.Point
    rw [Nat.card_unique]
    omega
  · haveI : IsEmpty (ActiveNodeLocation A.Actor) :=
      ⟨fun h ↦ hA h.down.down⟩
    simp

/-- The number of active local-action locations in a rooted container is at
most one less than its number of leaves. -/
theorem TreeContainer.card_activeTreeLocation_le : ∀ T : TreeContainer.{u},
    Fintype.card (ActiveTreeLocation T) ≤ T.degree - 1
  | .primitive P => by
      rw [← Nat.card_eq_fintype_card]
      exact card_plift_nontrivial_le_degree_pred P.action
  | .wreath fibre top => by
      classical
      let d := top.action.degree
      let m := fibre.degree
      have hd : 0 < d := Fintype.card_pos
      have hm : 0 < m := Fintype.card_pos
      have hroot := card_plift_nontrivial_le_degree_pred top.action
      have hchild := TreeContainer.card_activeTreeLocation_le fibre
      have hcard :
          Fintype.card (ActiveTreeLocation (TreeContainer.wreath fibre top)) =
            Nat.card (ActiveNodeLocation top.action.Actor) +
              d * Fintype.card (ActiveTreeLocation fibre) := by
        have hcardNat :
            Nat.card (ActiveTreeLocation (TreeContainer.wreath fibre top)) =
              Nat.card (ActiveNodeLocation top.action.Actor) +
                d * Nat.card (ActiveTreeLocation fibre) := by
          change Nat.card (_ ⊕ (_ × _)) = _
          rw [Nat.card_sum, Nat.card_prod]
          simp [d, SolubleAction.degree, Nat.card_eq_fintype_card]
        simpa only [Nat.card_eq_fintype_card] using hcardNat
      have hexp : (d - 1) + d * (m - 1) = d * m - 1 := by
        rw [Nat.mul_sub_left_distrib]
        have hdm : d ≤ d * m := by
          simpa using Nat.mul_le_mul_left d hm
        omega
      rw [hcard]
      calc
        Nat.card (ActiveNodeLocation top.action.Actor) +
              d * Fintype.card (ActiveTreeLocation fibre) ≤
            (d - 1) + d * (m - 1) :=
          Nat.add_le_add hroot (Nat.mul_le_mul_left d hchild)
        _ = d * m - 1 := hexp
        _ = (TreeContainer.wreath fibre top).degree - 1 := by
          rw [TreeContainer.degree_wreath]

/-- Active locations in a forest are the disjoint union of the active locations
in its component trees. -/
def ForestLocation : ForestContainer.{u} → Type u
  | .tree T => ActiveTreeLocation T
  | .sum F₁ F₂ => ForestLocation F₁ ⊕ ForestLocation F₂

noncomputable instance forestLocationFintype (F : ForestContainer.{u}) :
    Fintype (ForestLocation F) := by
  induction F with
  | tree => simp only [ForestLocation]; infer_instance
  | sum F₁ F₂ ih₁ ih₂ =>
      letI : Fintype (ForestLocation F₁) := ih₁
      letI : Fintype (ForestLocation F₂) := ih₂
      simp only [ForestLocation]
      infer_instance

/-- There are at most `degree` active locations in a forest. -/
theorem ForestContainer.card_forestLocation_le : ∀ F : ForestContainer.{u},
    Fintype.card (ForestLocation F) ≤ F.degree
  | .tree T => by
      exact T.card_activeTreeLocation_le.trans (Nat.sub_le T.degree 1)
  | .sum F₁ F₂ => by
      change Fintype.card (ForestLocation F₁ ⊕ ForestLocation F₂) ≤ _
      rw [Fintype.card_sum, ForestContainer.degree_sum]
      exact Nat.add_le_add F₁.card_forestLocation_le F₂.card_forestLocation_le

/-- The abstract support size of a positive-degree subgroup action is the usual
permutation support size. -/
theorem SolubleSubgroup.positiveAction_supportCard {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) (g : H.carrier) :
    (H.positiveAction hn).supportCard g = g.1.support.card := by
  classical
  congr 1

/-- The full recursively constructed forest group, transported back to `Fin n`.
Unlike the image of `H`, this envelope contains every independent product and wreath
section supplied by the forest, which is the right object for atom counting. -/
noncomputable def SolubleSubgroup.forestEnvelope {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) : SolubleSubgroup n := by
  let D := (H.positiveAction hn).forestRealizationData
  exact
    { carrier := D.2.targetEnvelope
      isSolvable := D.2.targetEnvelope_isSolvable }

/-- The original soluble subgroup is contained in its full forest envelope. -/
theorem SolubleSubgroup.le_forestEnvelope {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) :
    H.carrier ≤ (H.forestEnvelope hn).carrier := by
  intro g hg
  let D := (H.positiveAction hn).forestRealizationData
  change g ∈ D.2.targetEnvelope
  apply D.2.sourceRange_le_targetEnvelope
  refine ⟨⟨g, hg⟩, ?_⟩
  ext x
  rfl

/-- Every exact-support slice of a positive-degree soluble permutation subgroup
injects into the corresponding slice of its chosen recursive forest container. -/
theorem SolubleSubgroup.card_actionSupportSlice_le_forest {n : ℕ}
    (H : SolubleSubgroup n) (hn : 0 < n) :
    let D := (H.positiveAction hn).forestRealizationData
    ∀ s : ℕ, ((H.positiveAction hn).actionSupportSlice s).card ≤
      (D.1.action.actionSupportSlice s).card := by
  intro D s
  exact D.2.card_actionSupportSlice_le s

end Kourovka213

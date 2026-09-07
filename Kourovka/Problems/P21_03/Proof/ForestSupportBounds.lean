import Kourovka.Problems.P21_03.Proof.ForestSupportCount
import Kourovka.Problems.P21_03.Proof.WreathSupport
import Kourovka.Problems.P21_03.Proof.MovingWreathDegree
import Kourovka.Problems.P21_03.Proof.RawWeightedFunction
import Kourovka.Problems.P21_03.Proof.WreathCoreLift
import Kourovka.Problems.P21_03.Proof.SumCoreLift

namespace Kourovka213

universe u

open scoped BigOperators

def nontrivialOfNeOne {G : Type u} [One G] (g : G) (hg : g ≠ 1) : Nontrivial G :=
  ⟨⟨g, 1, hg⟩⟩

/-! Function-valued portraits; this is the representation used in the proof. -/

def TreeAtomLabel : (T : TreeContainer.{u}) → ActiveTreeLocation T → Type u
  | .primitive P, _ => {g : P.action.Actor // g ≠ 1}
  | .wreath fibre top, Sum.inl _ =>
      {g : (TreeContainer.wreath fibre top).action.Actor // g.right ≠ 1}
  | .wreath fibre _, Sum.inr p => TreeAtomLabel fibre p.2

instance activeTreeLocationSubsingleton_primitive (P : PrimitiveNode.{u}) :
    Subsingleton (ActiveTreeLocation (.primitive P)) := by
  constructor
  rintro ⟨⟨h⟩⟩ ⟨⟨h'⟩⟩
  have : h = h' := Subsingleton.elim _ _
  cases this
  rfl

def TreeAtomLabel.weight : {T : TreeContainer.{u}} →
    {l : ActiveTreeLocation T} → TreeAtomLabel T l → ℕ
  | .primitive P, _, g => P.action.supportCard g.1
  | .wreath fibre top, Sum.inl _, g =>
      (TreeContainer.wreath fibre top).action.supportCard g.1
  | .wreath fibre _, Sum.inr _, a => TreeAtomLabel.weight (T := fibre) a

noncomputable def TreeContainer.portrait :
    (T : TreeContainer.{u}) → T.action.Actor →
      ∀ l : ActiveTreeLocation T, Option (TreeAtomLabel T l)
  | .primitive P, g, _ => by
      classical
      exact if hg : g ≠ 1 then some ⟨g, hg⟩ else none
  | .wreath fibre top, g, Sum.inl _ => by
      classical
      exact if hq : g.right ≠ 1 then
        some ⟨g, hq⟩ else none
  | .wreath fibre _, g, Sum.inr p => by
      classical
      exact if g.right = 1 then portrait fibre (g.left p.1) p.2 else none

theorem TreeContainer.portrait_injective : ∀ T : TreeContainer.{u},
    Function.Injective T.portrait
  | .primitive P => by
      classical
      intro g h heq
      by_cases hg : g ≠ 1
      · let l : ActiveTreeLocation (.primitive P) :=
          ⟨⟨nontrivialOfNeOne g hg⟩⟩
        have hl := congrFun heq l
        by_cases hh : h ≠ 1
        · dsimp only [portrait] at hl
          rw [dif_pos hg, dif_pos hh] at hl
          exact congrArg Subtype.val (Option.some.inj hl)
        · dsimp only [portrait] at hl
          rw [dif_pos hg, dif_neg hh] at hl
          exact (Option.some_ne_none _ hl).elim
      · have hg1 : g = 1 := not_ne_iff.mp hg
        by_cases hh : h ≠ 1
        · let l : ActiveTreeLocation (.primitive P) :=
            ⟨⟨nontrivialOfNeOne h hh⟩⟩
          have hl := congrFun heq l
          dsimp only [portrait] at hl
          rw [dif_neg hg, dif_pos hh] at hl
          exact (Option.some_ne_none _ hl.symm).elim
        · exact hg1.trans (not_ne_iff.mp hh).symm
  | .wreath fibre top => by
      classical
      intro g h heq
      by_cases hg : g.right ≠ 1
      · let l : ActiveTreeLocation (.wreath fibre top) :=
          Sum.inl ⟨⟨nontrivialOfNeOne g.right hg⟩⟩
        have hl := congrFun heq l
        by_cases hh : h.right ≠ 1
        · dsimp only [l, portrait] at hl
          rw [dif_pos hg, dif_pos hh] at hl
          exact congrArg Subtype.val (Option.some.inj hl)
        · dsimp only [l, portrait] at hl
          rw [dif_pos hg, dif_neg hh] at hl
          exact (Option.some_ne_none _ hl).elim
      · have hg1 : g.right = 1 := not_ne_iff.mp hg
        by_cases hh : h.right ≠ 1
        · let l : ActiveTreeLocation (.wreath fibre top) :=
            Sum.inl ⟨⟨nontrivialOfNeOne h.right hh⟩⟩
          have hl := congrFun heq l
          dsimp only [l, portrait] at hl
          rw [dif_neg hg, dif_pos hh] at hl
          exact (Option.some_ne_none _ hl.symm).elim
        · have hh1 : h.right = 1 := not_ne_iff.mp hh
          apply PermWreath.ext
          · funext i
            apply TreeContainer.portrait_injective fibre
            funext l
            have hl := congrFun heq (Sum.inr (i, l))
            change
              (if g.right = 1 then fibre.portrait (g.left i) l else none) =
                if h.right = 1 then fibre.portrait (h.left i) l else none at hl
            rw [if_pos hg1, if_pos hh1] at hl
            exact hl
          · exact hg1.trans hh1.symm

def portraitWeight {T : TreeContainer.{u}} (p : ∀ l, Option (TreeAtomLabel T l))
    (l : ActiveTreeLocation T) : ℕ :=
  (p l).elim 0 TreeAtomLabel.weight

noncomputable def TreeContainer.portraitLocations (T : TreeContainer.{u})
    (g : T.action.Actor) : Finset (ActiveTreeLocation T) := by
  classical
  exact Finset.univ.filter fun l ↦ (T.portrait g l).isSome

theorem SolubleAction.supportCard_eq_toPerm_support (A : SolubleAction.{u, u})
    (g : A.Actor) : A.supportCard g = (A.toPermHom g).support.card := by
  rfl

@[simp]
theorem SolubleAction.supportCard_one (A : SolubleAction.{u, u}) :
    A.supportCard 1 = 0 := by
  simp [SolubleAction.supportCard, SolubleAction.supportFinset]

noncomputable def TreeContainer.portraitTotalWeight (T : TreeContainer.{u})
    (g : T.action.Actor) : ℕ :=
  ∑ l, portraitWeight (T.portrait g) l

private theorem sum_activeTreeLocation_wreath
    (fibre : TreeContainer.{u}) (top : PrimitiveNode.{u})
    (f : ActiveTreeLocation (.wreath fibre top) → ℕ) :
    (∑ x, f x) =
      (∑ r : ActiveNodeLocation top.action.Actor, f (Sum.inl r)) +
        ∑ i : top.action.Point, ∑ l : ActiveTreeLocation fibre, f (Sum.inr (i, l)) := by
  let e : ActiveTreeLocation (.wreath fibre top) ≃
      ActiveNodeLocation top.action.Actor ⊕
        (top.action.Point × ActiveTreeLocation fibre) := Equiv.refl _
  calc
    (∑ x, f x) = ∑ y, f (e.symm y) := by
      simpa using e.sum_comp (fun y ↦ f (e.symm y))
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      rfl

theorem TreeContainer.portraitTotalWeight_eq_supportCard :
    ∀ (T : TreeContainer.{u}) (g : T.action.Actor),
      T.portraitTotalWeight g = T.action.supportCard g
  | .primitive P, g => by
      classical
      by_cases hg : g ≠ 1
      · let l : ActiveTreeLocation (.primitive P) :=
          ⟨⟨nontrivialOfNeOne g hg⟩⟩
        letI : Unique (ActiveTreeLocation (.primitive P)) :=
          { default := l
            uniq := fun _ ↦ Subsingleton.elim _ _ }
        rw [portraitTotalWeight, Fintype.sum_unique]
        change (if hg' : g ≠ 1 then some (⟨g, hg'⟩ :
          {x : P.action.Actor // x ≠ 1}) else none).elim 0
            (fun x : {x : P.action.Actor // x ≠ 1} ↦
              P.action.supportCard x.1) = P.action.supportCard g
        rw [dif_pos hg]
        rfl
      · have hg1 : g = 1 := not_ne_iff.mp hg
        subst g
        rw [portraitTotalWeight]
        have hleft :
            (∑ l : ActiveTreeLocation (.primitive P),
              portraitWeight ((TreeContainer.primitive P).portrait 1) l) = 0 := by
          apply Finset.sum_eq_zero
          intro l _hl
          change (if h : (1 : P.action.Actor) ≠ 1 then
            some (⟨1, h⟩ : {x : P.action.Actor // x ≠ 1}) else none).elim 0 _ = 0
          rw [dif_neg (not_ne_iff.mpr rfl)]
          rfl
        rw [hleft]
        exact P.action.supportCard_one.symm
  | .wreath fibre top, g => by
      classical
      by_cases hg : g.right ≠ 1
      · let l : ActiveNodeLocation top.action.Actor :=
          ⟨⟨nontrivialOfNeOne g.right hg⟩⟩
        letI : Subsingleton (ActiveNodeLocation top.action.Actor) := inferInstance
        letI : Unique (ActiveNodeLocation top.action.Actor) :=
          { default := l
            uniq := fun _ ↦ Subsingleton.elim _ _ }
        rw [portraitTotalWeight,
          sum_activeTreeLocation_wreath fibre top, Fintype.sum_unique]
        have hroot :
            portraitWeight ((TreeContainer.wreath fibre top).portrait g) (Sum.inl l) =
              (TreeContainer.wreath fibre top).action.supportCard g := by
          change
            (if hq : g.right ≠ 1 then
              some (⟨g, hq⟩ :
                {x : (TreeContainer.wreath fibre top).action.Actor // x.right ≠ 1})
            else none).elim 0
              (fun x ↦ (TreeContainer.wreath fibre top).action.supportCard x.1) =
                (TreeContainer.wreath fibre top).action.supportCard g
          rw [dif_pos hg]
          rfl
        rw [hroot]
        simp [portraitWeight, portrait, hg]
      · have hg1 : g.right = 1 := not_ne_iff.mp hg
        rw [portraitTotalWeight, sum_activeTreeLocation_wreath fibre top]
        have hroot :
            (∑ l : ActiveNodeLocation top.action.Actor,
              portraitWeight ((TreeContainer.wreath fibre top).portrait g) (Sum.inl l)) = 0 := by
          simp [portraitWeight, portrait, hg]
        rw [hroot, zero_add]
        calc
          (∑ i : top.action.Point, ∑ l : ActiveTreeLocation fibre,
              portraitWeight ((TreeContainer.wreath fibre top).portrait g) (Sum.inr (i, l))) =
              ∑ i : top.action.Point, fibre.action.supportCard (g.left i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            calc
              (∑ l : ActiveTreeLocation fibre,
                  portraitWeight ((TreeContainer.wreath fibre top).portrait g)
                    (Sum.inr (i, l))) =
                  ∑ l : ActiveTreeLocation fibre,
                    portraitWeight (fibre.portrait (g.left i)) l := by
                apply Finset.sum_congr rfl
                intro l _hl
                change
                  (if g.right = 1 then fibre.portrait (g.left i) l else none).elim 0
                      (fun x ↦ TreeAtomLabel.weight x) =
                    (fibre.portrait (g.left i) l).elim 0
                      (fun x ↦ TreeAtomLabel.weight x)
                rw [if_pos hg1]
              _ = fibre.action.supportCard (g.left i) :=
                TreeContainer.portraitTotalWeight_eq_supportCard fibre (g.left i)
          _ = (TreeContainer.wreath fibre top).action.supportCard g := by
            let gw : PermWreath fibre.action.Actor top.action.Actor top.action.Point := g
            have hsupport := PermWreath.card_support_naturalToPerm_eq_sum
              fibre.action.Actor top.action.Actor top.action.Point fibre.action.Point gw
            rw [SolubleAction.supportCard_eq_toPerm_support]
            change (∑ i : top.action.Point, fibre.action.supportCard (gw.left i)) =
              (PermWreath.naturalToPerm fibre.action.Actor top.action.Actor
                top.action.Point fibre.action.Point gw).support.card
            rw [hsupport]
            apply Finset.sum_congr rfl
            intro i _hi
            have hfix : gw.right • i = i := by simp [gw, hg1]
            rw [if_neg (not_ne_iff.mpr hfix),
              SolubleAction.supportCard_eq_toPerm_support]
            rfl

private theorem SolubleAction.card_fixedBy_eq_degree_sub_supportCard
    (A : SolubleAction.{u, u}) (g : A.Actor) :
    Nat.card (MulAction.fixedBy A.Point g) = A.degree - A.supportCard g := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter fun x : A.Point ↦
      x ∈ MulAction.fixedBy A.Point g).card =
    Fintype.card A.Point -
      (Finset.univ.filter fun x : A.Point ↦ g • x ≠ x).card
  simp only [MulAction.mem_fixedBy]
  have hcompl :
      (Finset.univ.filter fun x : A.Point ↦ g • x = x) =
        (Finset.univ.filter fun x : A.Point ↦ g • x ≠ x)ᶜ := by
    ext x
    simp
  rw [hcompl, Finset.card_compl]

theorem PrimitiveNode.degree_le_two_mul_supportCard
    (P : PrimitiveNode.{u}) (g : P.action.Actor) (hg : g ≠ 1) :
    P.action.degree ≤ 2 * P.action.supportCard g := by
  letI : MulAction.IsPreprimitive P.action.Actor P.action.Point := P.preprimitive
  have hfixed := primitive_solvable_two_mul_card_fixedBy_le
    P.action.Actor P.action.Point g hg
  rw [P.action.card_fixedBy_eq_degree_sub_supportCard] at hfixed
  have hs : P.action.supportCard g ≤ P.action.degree := by
    exact (P.action.supportFinset g).card_le_univ
  change 2 * (P.action.degree - P.action.supportCard g) ≤
      P.action.degree at hfixed
  omega

theorem SolubleAction.two_le_supportCard_of_ne_one
    (A : SolubleAction.{u, u}) (g : A.Actor) (hg : g ≠ 1) :
    2 ≤ A.supportCard g := by
  by_contra h
  have hle : (A.toPermHom g).support.card ≤ 1 := by
    rw [← A.supportCard_eq_toPerm_support]
    omega
  have hone : A.toPermHom g = 1 := Equiv.Perm.card_support_le_one.mp hle
  apply hg
  apply A.toPermHom_injective
  simpa using hone

theorem TreeAtomLabel.two_le_weight :
    ∀ (T : TreeContainer.{u}) (l : ActiveTreeLocation T)
      (a : TreeAtomLabel T l), 2 ≤ a.weight
  | .primitive P, l, a =>
      P.action.two_le_supportCard_of_ne_one a.1 a.2
  | .wreath fibre top, Sum.inl l, a => by
      apply (TreeContainer.wreath fibre top).action.two_le_supportCard_of_ne_one a.1
      intro ha
      apply a.2
      calc
        a.1.right = (1 : (TreeContainer.wreath fibre top).action.Actor).right :=
          congrArg (fun g : (TreeContainer.wreath fibre top).action.Actor ↦ g.right) ha
        _ = 1 := SemidirectProduct.one_right
  | .wreath fibre top, Sum.inr p, a =>
      TreeAtomLabel.two_le_weight fibre p.2 a

noncomputable def treeAtomLabelFintype :
    ∀ (T : TreeContainer.{u}) (l : ActiveTreeLocation T),
      Fintype (TreeAtomLabel T l)
  | .primitive P, l => by
      classical
      letI : Fintype P.action.Actor := Fintype.ofFinite _
      change Fintype {g : P.action.Actor // g ≠ 1}
      infer_instance
  | .wreath fibre top, Sum.inl l => by
      classical
      letI : Fintype (TreeContainer.wreath fibre top).action.Actor := Fintype.ofFinite _
      change Fintype
        {g : (TreeContainer.wreath fibre top).action.Actor // g.right ≠ 1}
      infer_instance
  | .wreath fibre top, Sum.inr p => treeAtomLabelFintype fibre p.2

attribute [instance] treeAtomLabelFintype

abbrev TreeAtomLabelOfWeight (T : TreeContainer.{u})
    (l : ActiveTreeLocation T) (a : ℕ) :=
  {z : TreeAtomLabel T l // z.weight = a}

theorem TreeAtomLabel.card_ofWeight_le :
    ∀ (T : TreeContainer.{u}) (l : ActiveTreeLocation T) (a : ℕ),
      Nat.card (TreeAtomLabelOfWeight T l a) ≤ 256 ^ (2 * a)
  | .primitive P, l, a => by
      classical
      by_cases hne : Nonempty (TreeAtomLabelOfWeight (.primitive P) l a)
      · obtain ⟨z⟩ := hne
        have hdeg : P.action.degree ≤ 2 * a := by
          have hz := P.degree_le_two_mul_supportCard z.1.1 z.1.2
          have hzweight := z.2
          change P.action.supportCard z.1.1 = a at hzweight
          omega
        calc
          Nat.card (TreeAtomLabelOfWeight (.primitive P) l a) ≤
              Nat.card P.action.Actor :=
            Nat.card_le_card_of_injective
              (fun x : TreeAtomLabelOfWeight (.primitive P) l a ↦ x.1.1)
              (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
          _ ≤ 256 ^ (P.action.degree - 1) := P.actor_natCard_le
          _ ≤ 256 ^ (2 * a) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      · haveI : IsEmpty (TreeAtomLabelOfWeight (.primitive P) l a) :=
          not_nonempty_iff.mp hne
        simp
  | .wreath fibre top, Sum.inl l, a => by
      classical
      by_cases hne : Nonempty
          (TreeAtomLabelOfWeight (.wreath fibre top) (Sum.inl l) a)
      · obtain ⟨z⟩ := hne
        letI : MulAction.IsPreprimitive top.action.Actor top.action.Point :=
          top.preprimitive
        have hmove := degree_mul_le_two_mul_wreathSupport_of_right_ne_one
          top.action fibre.action z.1.1 z.1.2
        have hdeg : (TreeContainer.wreath fibre top).degree ≤ 2 * a := by
          rw [TreeContainer.degree_wreath]
          have hzweight := z.2
          change (TreeContainer.wreath fibre top).action.supportCard z.1.1 = a at hzweight
          rw [SolubleAction.supportCard_eq_toPerm_support] at hzweight
          exact hmove.trans_eq (congrArg (fun x ↦ 2 * x) hzweight)
        calc
          Nat.card
              (TreeAtomLabelOfWeight (.wreath fibre top) (Sum.inl l) a) ≤
              Nat.card (TreeContainer.wreath fibre top).action.Actor :=
            Nat.card_le_card_of_injective
              (fun x : TreeAtomLabelOfWeight
                (.wreath fibre top) (Sum.inl l) a ↦ x.1.1)
              (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
          _ ≤ 256 ^ ((TreeContainer.wreath fibre top).degree - 1) :=
            (TreeContainer.wreath fibre top).actor_natCard_le
          _ ≤ 256 ^ (2 * a) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
      · haveI : IsEmpty
            (TreeAtomLabelOfWeight (.wreath fibre top) (Sum.inl l) a) :=
          not_nonempty_iff.mp hne
        simp
  | .wreath fibre top, Sum.inr p, a => by
      simpa only [TreeAtomLabelOfWeight, TreeAtomLabel, TreeAtomLabel.weight] using
        TreeAtomLabel.card_ofWeight_le fibre p.2 a

noncomputable def TreeAtomLabel.ofWeightEmbedding
    (T : TreeContainer.{u}) (l : ActiveTreeLocation T) (a : ℕ) :
    TreeAtomLabelOfWeight T l a ↪ Fin ((256 ^ 2) ^ a) := by
  classical
  have hcard : Fintype.card (TreeAtomLabelOfWeight T l a) ≤ (256 ^ 2) ^ a := by
    rw [← Nat.card_eq_fintype_card]
    simpa only [pow_mul] using TreeAtomLabel.card_ofWeight_le T l a
  exact
    { toFun := fun z ↦ Fin.castLE hcard (Fintype.equivFin _ z)
      inj' := fun _ _ h ↦ (Fintype.equivFin _).injective (Fin.castLE_injective hcard h) }

noncomputable def TreeContainer.portraitValue (T : TreeContainer.{u})
    (g : T.action.Actor) (x : T.portraitLocations g) : TreeAtomLabel T x.1 :=
  (T.portrait g x.1).get (by
    have hx := x.2
    simp only [portraitLocations, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx)

theorem TreeContainer.some_portraitValue (T : TreeContainer.{u})
    (g : T.action.Actor) (x : T.portraitLocations g) :
    some (T.portraitValue g x) = T.portrait g x.1 := by
  exact Option.some_get _

theorem TreeContainer.portraitValue_weight_eq (T : TreeContainer.{u})
    (g : T.action.Actor) (x : T.portraitLocations g) :
    (T.portraitValue g x).weight = portraitWeight (T.portrait g) x.1 := by
  unfold portraitWeight
  rw [← T.some_portraitValue g x]
  rfl

theorem TreeContainer.sum_portraitValue_weight (T : TreeContainer.{u})
    (g : T.action.Actor) :
    (∑ x : T.portraitLocations g, (T.portraitValue g x).weight) =
      T.action.supportCard g := by
  calc
    (∑ x : T.portraitLocations g, (T.portraitValue g x).weight) =
        ∑ x : T.portraitLocations g,
          portraitWeight (T.portrait g) x.1 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact T.portraitValue_weight_eq g x
    _ = (∑ l ∈ T.portraitLocations g,
          portraitWeight (T.portrait g) l) := by
      exact (Finset.sum_subtype (T.portraitLocations g)
        (fun _ ↦ Iff.rfl) (portraitWeight (T.portrait g))).symm
    _ = ∑ l, portraitWeight (T.portrait g) l := by
      rw [portraitLocations, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _hl
      unfold portraitWeight
      cases h : T.portrait g l with
      | none => simp [h]
      | some z => simp [h]
    _ = T.action.supportCard g := T.portraitTotalWeight_eq_supportCard g

noncomputable def TreeContainer.rawPortrait (T : TreeContainer.{u})
    (g : T.action.Actor) :
    RawWeightedConfiguration (ActiveTreeLocation T) (256 ^ 2)
      (T.action.supportCard g) (T.portraitLocations g).card where
  locations := T.portraitLocations g
  card_locations := rfl
  weight x := (T.portraitValue g x).weight
  weight_pos x := (T.portraitValue g x).two_le_weight.trans' (by omega)
  weight_sum := T.sum_portraitValue_weight g
  label x := TreeAtomLabel.ofWeightEmbedding T x.1 (T.portraitValue g x).weight
    ⟨T.portraitValue g x, rfl⟩

noncomputable def TreeAtomLabel.encode (T : TreeContainer.{u})
    (l : ActiveTreeLocation T) (z : TreeAtomLabel T l) :
    Σ a : ℕ, Fin ((256 ^ 2) ^ a) :=
  ⟨z.weight, TreeAtomLabel.ofWeightEmbedding T l z.weight ⟨z, rfl⟩⟩

theorem TreeAtomLabel.encode_injective (T : TreeContainer.{u})
    (l : ActiveTreeLocation T) :
    Function.Injective (TreeAtomLabel.encode T l) := by
  let pre : TreeAtomLabel T l → Σ a : ℕ, TreeAtomLabelOfWeight T l a :=
    fun z ↦ ⟨z.weight, ⟨z, rfl⟩⟩
  let post : (Σ a : ℕ, TreeAtomLabelOfWeight T l a) →
      Σ a : ℕ, Fin ((256 ^ 2) ^ a) :=
    fun z ↦ ⟨z.1, TreeAtomLabel.ofWeightEmbedding T l z.1 z.2⟩
  have hpre : Function.Injective pre := by
    intro z w h
    exact congrArg (fun q : Σ a : ℕ, TreeAtomLabelOfWeight T l a ↦ q.2.1) h
  have hpost : Function.Injective post := by
    rintro ⟨a, z⟩ ⟨b, w⟩ h
    have hab : a = b := congrArg Sigma.fst h
    subst b
    have hzw :
        TreeAtomLabel.ofWeightEmbedding T l a z =
          TreeAtomLabel.ofWeightEmbedding T l a w :=
      eq_of_heq (Sigma.ext_iff.mp h).2
    have := (TreeAtomLabel.ofWeightEmbedding T l a).injective hzw
    subst w
    rfl
  intro z w h
  apply hpre
  apply hpost
  exact h

noncomputable def TreeContainer.encodedPortrait (T : TreeContainer.{u})
    (g : T.action.Actor) (l : ActiveTreeLocation T) :
    Option (Σ a : ℕ, Fin ((256 ^ 2) ^ a)) :=
  (T.portrait g l).map (TreeAtomLabel.encode T l)

theorem TreeContainer.encodedPortrait_injective (T : TreeContainer.{u}) :
    Function.Injective T.encodedPortrait := by
  intro g h heq
  apply T.portrait_injective
  funext l
  apply Option.map_injective (TreeAtomLabel.encode_injective T l)
  exact congrFun heq l

noncomputable def TreeContainer.packedRawPortrait (T : TreeContainer.{u})
    (g : T.action.Actor) :
    Σ s : ℕ, Σ k : ℕ,
      RawWeightedConfiguration (ActiveTreeLocation T) (256 ^ 2) s k :=
  ⟨T.action.supportCard g, (T.portraitLocations g).card, T.rawPortrait g⟩

theorem TreeContainer.rawPortrait_toFunction (T : TreeContainer.{u})
    (g : T.action.Actor) :
    (T.rawPortrait g).toFunction = T.encodedPortrait g := by
  classical
  funext l
  by_cases hl : l ∈ T.portraitLocations g
  · rw [RawWeightedConfiguration.toFunction_apply_of_mem _ l hl]
    let x : T.portraitLocations g := ⟨l, hl⟩
    change some ⟨(T.portraitValue g x).weight,
        TreeAtomLabel.ofWeightEmbedding T l (T.portraitValue g x).weight
          ⟨T.portraitValue g x, rfl⟩⟩ =
      (T.portrait g l).map (TreeAtomLabel.encode T l)
    rw [← T.some_portraitValue g x]
    rfl
  · rw [RawWeightedConfiguration.toFunction_apply_of_not_mem _ l hl]
    unfold encodedPortrait
    cases hp : T.portrait g l with
    | none => rfl
    | some z =>
        exfalso
        apply hl
        simp [portraitLocations, hp]

theorem TreeContainer.packedRawPortrait_injective (T : TreeContainer.{u}) :
    Function.Injective T.packedRawPortrait := by
  intro g h heq
  let read :
      (Σ s : ℕ, Σ k : ℕ,
        RawWeightedConfiguration (ActiveTreeLocation T) (256 ^ 2) s k) →
        ActiveTreeLocation T → Option (Σ a : ℕ, Fin ((256 ^ 2) ^ a)) :=
    fun c ↦ c.2.2.toFunction
  apply T.encodedPortrait_injective
  rw [← T.rawPortrait_toFunction g, ← T.rawPortrait_toFunction h]
  exact congrArg read heq

/-! Forest portraits are disjoint sums of the rooted-tree portraits. -/

def ForestAtomLabel : (F : ForestContainer.{u}) → ForestLocation F → Type u
  | .tree T, l => TreeAtomLabel T l
  | .sum F₁ F₂, Sum.inl l => ForestAtomLabel F₁ l
  | .sum F₁ F₂, Sum.inr l => ForestAtomLabel F₂ l

def ForestAtomLabel.weight : {F : ForestContainer.{u}} →
    {l : ForestLocation F} → ForestAtomLabel F l → ℕ
  | .tree T, _, z => TreeAtomLabel.weight z
  | .sum F₁ F₂, Sum.inl _, z => ForestAtomLabel.weight (F := F₁) z
  | .sum F₁ F₂, Sum.inr _, z => ForestAtomLabel.weight (F := F₂) z

noncomputable def ForestContainer.portrait :
    (F : ForestContainer.{u}) → F.action.Actor →
      ∀ l : ForestLocation F, Option (ForestAtomLabel F l)
  | .tree T, g, l => T.portrait g l
  | .sum F₁ F₂, g, Sum.inl l => F₁.portrait g.1 l
  | .sum F₁ F₂, g, Sum.inr l => F₂.portrait g.2 l

theorem ForestContainer.portrait_injective : ∀ F : ForestContainer.{u},
    Function.Injective F.portrait
  | .tree T => T.portrait_injective
  | .sum F₁ F₂ => by
      intro g h heq
      apply Prod.ext
      · apply F₁.portrait_injective
        funext l
        exact congrFun heq (Sum.inl l)
      · apply F₂.portrait_injective
        funext l
        exact congrFun heq (Sum.inr l)

def forestPortraitWeight {F : ForestContainer.{u}}
    (p : ∀ l, Option (ForestAtomLabel F l)) (l : ForestLocation F) : ℕ :=
  (p l).elim 0 ForestAtomLabel.weight

noncomputable def ForestContainer.portraitLocations (F : ForestContainer.{u})
    (g : F.action.Actor) : Finset (ForestLocation F) := by
  classical
  exact Finset.univ.filter fun l ↦ (F.portrait g l).isSome

private def SolubleAction.sumSupportEquiv (A B : SolubleAction.{u, u})
    (g : (SolubleAction.sum A B).Actor) :
    {p : (SolubleAction.sum A B).Point // p ∈ (SolubleAction.sum A B).supportFinset g} ≃
      {x : A.Point // x ∈ A.supportFinset g.1} ⊕
        {y : B.Point // y ∈ B.supportFinset g.2} where
  toFun p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl x =>
        apply Sum.inl
        refine ⟨x, (A.mem_supportFinset g.1 x).mpr ?_⟩
        intro hx
        apply ((SolubleAction.sum A B).mem_supportFinset g (Sum.inl x)).mp hp
        exact congrArg Sum.inl hx
    | inr y =>
        apply Sum.inr
        refine ⟨y, (B.mem_supportFinset g.2 y).mpr ?_⟩
        intro hy
        apply ((SolubleAction.sum A B).mem_supportFinset g (Sum.inr y)).mp hp
        exact congrArg Sum.inr hy
  invFun p := by
    cases p with
    | inl x =>
        refine ⟨Sum.inl x.1,
          ((SolubleAction.sum A B).mem_supportFinset g (Sum.inl x.1)).mpr ?_⟩
        intro h
        exact (A.mem_supportFinset g.1 x.1).mp x.2 (Sum.inl.inj h)
    | inr y =>
        refine ⟨Sum.inr y.1,
          ((SolubleAction.sum A B).mem_supportFinset g (Sum.inr y.1)).mpr ?_⟩
        intro h
        exact (B.mem_supportFinset g.2 y.1).mp y.2 (Sum.inr.inj h)
  left_inv
    | ⟨Sum.inl x, hx⟩ => by
        apply Subtype.ext
        rfl
    | ⟨Sum.inr y, hy⟩ => by
        apply Subtype.ext
        rfl
  right_inv
    | Sum.inl ⟨x, hx⟩ => by
        congr 1
    | Sum.inr ⟨y, hy⟩ => by
        congr 1

theorem SolubleAction.supportCard_sum (A B : SolubleAction.{u, u})
    (g : (SolubleAction.sum A B).Actor) :
    (SolubleAction.sum A B).supportCard g =
      A.supportCard g.1 + B.supportCard g.2 := by
  calc
    (SolubleAction.sum A B).supportCard g =
        Fintype.card
          {p // p ∈ (SolubleAction.sum A B).supportFinset g} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ({x // x ∈ A.supportFinset g.1} ⊕
          {y // y ∈ B.supportFinset g.2}) :=
      Fintype.card_congr (SolubleAction.sumSupportEquiv A B g)
    _ = Fintype.card {x // x ∈ A.supportFinset g.1} +
        Fintype.card {y // y ∈ B.supportFinset g.2} := Fintype.card_sum
    _ = A.supportCard g.1 + B.supportCard g.2 := by
      rw [Fintype.card_coe, Fintype.card_coe]
      rfl

noncomputable def ForestContainer.portraitTotalWeight (F : ForestContainer.{u})
    (g : F.action.Actor) : ℕ :=
  ∑ l, forestPortraitWeight (F.portrait g) l

private theorem sum_forestLocation_sum
    (F₁ F₂ : ForestContainer.{u})
    (f : ForestLocation (.sum F₁ F₂) → ℕ) :
    (∑ x, f x) =
      (∑ l : ForestLocation F₁, f (Sum.inl l)) +
        ∑ r : ForestLocation F₂, f (Sum.inr r) := by
  let e : ForestLocation (.sum F₁ F₂) ≃
      ForestLocation F₁ ⊕ ForestLocation F₂ := Equiv.refl _
  calc
    (∑ x, f x) = ∑ y, f (e.symm y) := by
      simpa using e.sum_comp (fun y ↦ f (e.symm y))
    _ = _ := by
      rw [Fintype.sum_sum_type]
      rfl

theorem ForestContainer.portraitTotalWeight_eq_supportCard :
    ∀ (F : ForestContainer.{u}) (g : F.action.Actor),
      F.portraitTotalWeight g = F.action.supportCard g
  | .tree T, g => T.portraitTotalWeight_eq_supportCard g
  | .sum F₁ F₂, g => by
      rw [portraitTotalWeight, sum_forestLocation_sum F₁ F₂]
      have hleft :
          (∑ l : ForestLocation F₁,
            forestPortraitWeight ((ForestContainer.sum F₁ F₂).portrait g)
              (Sum.inl l)) = F₁.action.supportCard g.1 := by
        change F₁.portraitTotalWeight g.1 = F₁.action.supportCard g.1
        exact ForestContainer.portraitTotalWeight_eq_supportCard F₁ g.1
      have hright :
          (∑ r : ForestLocation F₂,
            forestPortraitWeight ((ForestContainer.sum F₁ F₂).portrait g)
              (Sum.inr r)) = F₂.action.supportCard g.2 := by
        change F₂.portraitTotalWeight g.2 = F₂.action.supportCard g.2
        exact ForestContainer.portraitTotalWeight_eq_supportCard F₂ g.2
      rw [hleft, hright]
      let gs : F₁.action.Actor × F₂.action.Actor := g
      change F₁.action.supportCard gs.1 + F₂.action.supportCard gs.2 =
        (SolubleAction.sum F₁.action F₂.action).supportCard gs
      exact (SolubleAction.supportCard_sum F₁.action F₂.action gs).symm

theorem ForestAtomLabel.two_le_weight :
  ∀ (F : ForestContainer.{u}) (l : ForestLocation F)
      (z : ForestAtomLabel F l), 2 ≤ z.weight
  | .tree T, l, z => TreeAtomLabel.two_le_weight T l z
  | .sum F₁ F₂, Sum.inl l, z =>
      ForestAtomLabel.two_le_weight F₁ l z
  | .sum F₁ F₂, Sum.inr l, z =>
      ForestAtomLabel.two_le_weight F₂ l z

noncomputable def forestAtomLabelFintype :
    ∀ (F : ForestContainer.{u}) (l : ForestLocation F),
      Fintype (ForestAtomLabel F l)
  | .tree T, l => treeAtomLabelFintype T l
  | .sum F₁ F₂, Sum.inl l => forestAtomLabelFintype F₁ l
  | .sum F₁ F₂, Sum.inr l => forestAtomLabelFintype F₂ l

attribute [instance] forestAtomLabelFintype

abbrev ForestAtomLabelOfWeight (F : ForestContainer.{u})
    (l : ForestLocation F) (a : ℕ) :=
  {z : ForestAtomLabel F l // z.weight = a}

theorem ForestAtomLabel.card_ofWeight_le :
    ∀ (F : ForestContainer.{u}) (l : ForestLocation F) (a : ℕ),
      Nat.card (ForestAtomLabelOfWeight F l a) ≤ 256 ^ (2 * a)
  | .tree T, l, a => TreeAtomLabel.card_ofWeight_le T l a
  | .sum F₁ F₂, Sum.inl l, a =>
      ForestAtomLabel.card_ofWeight_le F₁ l a
  | .sum F₁ F₂, Sum.inr l, a =>
      ForestAtomLabel.card_ofWeight_le F₂ l a

noncomputable def ForestAtomLabel.ofWeightEmbedding
    (F : ForestContainer.{u}) (l : ForestLocation F) (a : ℕ) :
    ForestAtomLabelOfWeight F l a ↪ Fin ((256 ^ 2) ^ a) := by
  classical
  have hcard : Fintype.card (ForestAtomLabelOfWeight F l a) ≤ (256 ^ 2) ^ a := by
    rw [← Nat.card_eq_fintype_card]
    simpa only [pow_mul] using ForestAtomLabel.card_ofWeight_le F l a
  exact
    { toFun := fun z ↦ Fin.castLE hcard (Fintype.equivFin _ z)
      inj' := fun _ _ h ↦ (Fintype.equivFin _).injective
        (Fin.castLE_injective hcard h) }

noncomputable def ForestContainer.portraitValue (F : ForestContainer.{u})
    (g : F.action.Actor) (x : F.portraitLocations g) : ForestAtomLabel F x.1 :=
  (F.portrait g x.1).get (by
    have hx := x.2
    simp only [portraitLocations, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx)

theorem ForestContainer.some_portraitValue (F : ForestContainer.{u})
    (g : F.action.Actor) (x : F.portraitLocations g) :
    some (F.portraitValue g x) = F.portrait g x.1 :=
  Option.some_get _

theorem ForestContainer.portraitValue_weight_eq (F : ForestContainer.{u})
    (g : F.action.Actor) (x : F.portraitLocations g) :
    (F.portraitValue g x).weight = forestPortraitWeight (F.portrait g) x.1 := by
  unfold forestPortraitWeight
  rw [← F.some_portraitValue g x]
  rfl

theorem ForestContainer.sum_portraitValue_weight (F : ForestContainer.{u})
    (g : F.action.Actor) :
    (∑ x : F.portraitLocations g, (F.portraitValue g x).weight) =
      F.action.supportCard g := by
  calc
    (∑ x : F.portraitLocations g, (F.portraitValue g x).weight) =
        ∑ x : F.portraitLocations g,
          forestPortraitWeight (F.portrait g) x.1 := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact F.portraitValue_weight_eq g x
    _ = (∑ l ∈ F.portraitLocations g,
          forestPortraitWeight (F.portrait g) l) := by
      exact (Finset.sum_subtype (F.portraitLocations g)
        (fun _ ↦ Iff.rfl) (forestPortraitWeight (F.portrait g))).symm
    _ = ∑ l, forestPortraitWeight (F.portrait g) l := by
      rw [portraitLocations, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _hl
      unfold forestPortraitWeight
      cases h : F.portrait g l with
      | none => simp
      | some z => simp
    _ = F.action.supportCard g := F.portraitTotalWeight_eq_supportCard g

noncomputable def ForestContainer.rawPortrait (F : ForestContainer.{u})
    (g : F.action.Actor) :
    RawWeightedConfiguration (ForestLocation F) (256 ^ 2)
      (F.action.supportCard g) (F.portraitLocations g).card where
  locations := F.portraitLocations g
  card_locations := rfl
  weight x := (F.portraitValue g x).weight
  weight_pos x := (F.portraitValue g x).two_le_weight.trans' (by omega)
  weight_sum := F.sum_portraitValue_weight g
  label x := ForestAtomLabel.ofWeightEmbedding F x.1 (F.portraitValue g x).weight
    ⟨F.portraitValue g x, rfl⟩

noncomputable def ForestAtomLabel.encode (F : ForestContainer.{u})
    (l : ForestLocation F) (z : ForestAtomLabel F l) :
    Σ a : ℕ, Fin ((256 ^ 2) ^ a) :=
  ⟨z.weight, ForestAtomLabel.ofWeightEmbedding F l z.weight ⟨z, rfl⟩⟩

theorem ForestAtomLabel.encode_injective (F : ForestContainer.{u})
    (l : ForestLocation F) : Function.Injective (ForestAtomLabel.encode F l) := by
  let pre : ForestAtomLabel F l → Σ a : ℕ, ForestAtomLabelOfWeight F l a :=
    fun z ↦ ⟨z.weight, ⟨z, rfl⟩⟩
  let post : (Σ a : ℕ, ForestAtomLabelOfWeight F l a) →
      Σ a : ℕ, Fin ((256 ^ 2) ^ a) :=
    fun z ↦ ⟨z.1, ForestAtomLabel.ofWeightEmbedding F l z.1 z.2⟩
  have hpre : Function.Injective pre := by
    intro z w h
    exact congrArg (fun q : Σ a : ℕ, ForestAtomLabelOfWeight F l a ↦ q.2.1) h
  have hpost : Function.Injective post := by
    rintro ⟨a, z⟩ ⟨b, w⟩ h
    have hab : a = b := congrArg Sigma.fst h
    subst b
    have hzw : ForestAtomLabel.ofWeightEmbedding F l a z =
        ForestAtomLabel.ofWeightEmbedding F l a w :=
      eq_of_heq (Sigma.ext_iff.mp h).2
    have := (ForestAtomLabel.ofWeightEmbedding F l a).injective hzw
    subst w
    rfl
  intro z w h
  apply hpre
  apply hpost
  exact h

noncomputable def ForestContainer.encodedPortrait (F : ForestContainer.{u})
    (g : F.action.Actor) (l : ForestLocation F) :
    Option (Σ a : ℕ, Fin ((256 ^ 2) ^ a)) :=
  (F.portrait g l).map (ForestAtomLabel.encode F l)

theorem ForestContainer.encodedPortrait_injective (F : ForestContainer.{u}) :
    Function.Injective F.encodedPortrait := by
  intro g h heq
  apply F.portrait_injective
  funext l
  apply Option.map_injective (ForestAtomLabel.encode_injective F l)
  exact congrFun heq l

noncomputable def ForestContainer.packedRawPortrait (F : ForestContainer.{u})
    (g : F.action.Actor) :
    Σ s : ℕ, Σ k : ℕ,
      RawWeightedConfiguration (ForestLocation F) (256 ^ 2) s k :=
  ⟨F.action.supportCard g, (F.portraitLocations g).card, F.rawPortrait g⟩

theorem ForestContainer.rawPortrait_toFunction (F : ForestContainer.{u})
    (g : F.action.Actor) :
    (F.rawPortrait g).toFunction = F.encodedPortrait g := by
  classical
  funext l
  by_cases hl : l ∈ F.portraitLocations g
  · rw [RawWeightedConfiguration.toFunction_apply_of_mem _ l hl]
    let x : F.portraitLocations g := ⟨l, hl⟩
    change some ⟨(F.portraitValue g x).weight,
        ForestAtomLabel.ofWeightEmbedding F l (F.portraitValue g x).weight
          ⟨F.portraitValue g x, rfl⟩⟩ =
      (F.portrait g l).map (ForestAtomLabel.encode F l)
    rw [← F.some_portraitValue g x]
    rfl
  · rw [RawWeightedConfiguration.toFunction_apply_of_not_mem _ l hl]
    unfold encodedPortrait
    cases hp : F.portrait g l with
    | none => rfl
    | some z =>
        exfalso
        apply hl
        simp [portraitLocations, hp]

theorem ForestContainer.packedRawPortrait_injective (F : ForestContainer.{u}) :
    Function.Injective F.packedRawPortrait := by
  intro g h heq
  let read :
      (Σ s : ℕ, Σ k : ℕ,
        RawWeightedConfiguration (ForestLocation F) (256 ^ 2) s k) →
        ForestLocation F → Option (Σ a : ℕ, Fin ((256 ^ 2) ^ a)) :=
    fun c ↦ c.2.2.toFunction
  apply F.encodedPortrait_injective
  rw [← F.rawPortrait_toFunction g, ← F.rawPortrait_toFunction h]
  exact congrArg read heq


/-- An actor element whose permutation support has size two is one of the
generators of the transposition core. -/
private theorem SolubleAction.toPerm_mem_transpositionCore_of_supportCard_eq_two
    (A : SolubleAction.{u, u}) (g : A.Actor) (hg : A.supportCard g = 2) :
    A.toPermHom g ∈ transpositionCore A.toPermHom.range := by
  change (A.toPermHom g).support.card = 2 at hg
  apply Subgroup.subset_closure
  exact ⟨Equiv.Perm.card_support_eq_two.mp hg, ⟨g, rfl⟩⟩

/-- If every selected atom in the recursive portrait has weight two, then the
represented permutation belongs to the transposition core. -/
theorem TreeContainer.toPerm_mem_transpositionCore_of_portrait_weights_two :
    ∀ (T : TreeContainer.{u}) (g : T.action.Actor),
      (∀ x : T.portraitLocations g, (T.portraitValue g x).weight = 2) →
        T.action.toPermHom g ∈ transpositionCore T.action.toPermHom.range
  | .primitive P, g => by
      classical
      intro hall
      by_cases hg : g ≠ 1
      · let l : ActiveTreeLocation (.primitive P) :=
          ⟨⟨nontrivialOfNeOne g hg⟩⟩
        have hl : l ∈ (TreeContainer.primitive P).portraitLocations g := by
          simp only [TreeContainer.portraitLocations, Finset.mem_filter,
            Finset.mem_univ, true_and]
          dsimp only [l, TreeContainer.portrait]
          rw [dif_pos hg]
          rfl
        let x : (TreeContainer.primitive P).portraitLocations g := ⟨l, hl⟩
        have hweight :
            portraitWeight ((TreeContainer.primitive P).portrait g) l = 2 :=
          ((TreeContainer.primitive P).portraitValue_weight_eq g x).symm.trans
            (hall x)
        apply P.action.toPerm_mem_transpositionCore_of_supportCard_eq_two g
        change (if hg' : g ≠ 1 then some ⟨g, hg'⟩ else none).elim 0
          (fun z : {z : P.action.Actor // z ≠ 1} ↦ P.action.supportCard z.1) = 2 at hweight
        rw [dif_pos hg] at hweight
        exact hweight
      · have hg1 : g = 1 := not_ne_iff.mp hg
        rw [hg1, map_one]
        exact Subgroup.one_mem _
  | .wreath fibre top, g => by
      classical
      change PermWreath fibre.action.Actor top.action.Actor top.action.Point at g
      intro hall
      by_cases hg : g.right ≠ 1
      · let l : ActiveTreeLocation (.wreath fibre top) :=
          Sum.inl ⟨⟨nontrivialOfNeOne g.right hg⟩⟩
        have hl : l ∈ (TreeContainer.wreath fibre top).portraitLocations g := by
          simp only [TreeContainer.portraitLocations, Finset.mem_filter,
            Finset.mem_univ, true_and]
          dsimp only [l, TreeContainer.portrait]
          rw [dif_pos hg]
          rfl
        let x : (TreeContainer.wreath fibre top).portraitLocations g := ⟨l, hl⟩
        have hweight : portraitWeight
            ((TreeContainer.wreath fibre top).portrait g) l = 2 :=
          ((TreeContainer.wreath fibre top).portraitValue_weight_eq g x).symm.trans
            (hall x)
        apply SolubleAction.toPerm_mem_transpositionCore_of_supportCard_eq_two
          (TreeContainer.wreath fibre top).action g
        change (if hq : g.right ≠ 1 then some ⟨g, hq⟩ else none).elim 0
          (fun z : {z : (TreeContainer.wreath fibre top).action.Actor //
            z.right ≠ 1} ↦
              (TreeContainer.wreath fibre top).action.supportCard z.1) = 2 at hweight
        rw [dif_pos hg] at hweight
        exact hweight
      · have hg1 : g.right = 1 := not_ne_iff.mp hg
        have hsections : ∀ i : top.action.Point,
            fibre.action.toPermHom (g.left i) ∈
              transpositionCore fibre.action.toPermHom.range := by
          intro i
          apply TreeContainer.toPerm_mem_transpositionCore_of_portrait_weights_two fibre
          intro y
          have hy := y.2
          simp only [TreeContainer.portraitLocations, Finset.mem_filter,
            Finset.mem_univ, true_and] at hy
          have hp :
              (TreeContainer.wreath fibre top).portrait g (Sum.inr (i, y.1)) =
                fibre.portrait (g.left i) y.1 := by
            change (if g.right = 1 then fibre.portrait (g.left i) y.1 else none) = _
            rw [if_pos hg1]
          have hl : Sum.inr (i, y.1) ∈
              (TreeContainer.wreath fibre top).portraitLocations g := by
            change Sum.inr (i, y.1) ∈ Finset.univ.filter
              (fun l ↦ ((TreeContainer.wreath fibre top).portrait g l).isSome)
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [hp]
            exact hy
          let x : (TreeContainer.wreath fibre top).portraitLocations g :=
            ⟨Sum.inr (i, y.1), hl⟩
          have hwhole : portraitWeight
              ((TreeContainer.wreath fibre top).portrait g) (Sum.inr (i, y.1)) = 2 :=
            ((TreeContainer.wreath fibre top).portraitValue_weight_eq g x).symm.trans
              (hall x)
          have hchild : portraitWeight (fibre.portrait (g.left i)) y.1 = 2 := by
            unfold portraitWeight at hwhole ⊢
            rw [hp] at hwhole
            exact hwhole
          exact (fibre.portraitValue_weight_eq (g.left i) y).trans hchild
        have hbase := PermWreath.naturalToPerm_base_mem_transpositionCore_of_forall
          fibre.action.Actor top.action.Actor top.action.Point fibre.action.Point
          g.left hsections
        have hgeq : g = PermWreath.base fibre.action.Actor top.action.Actor
            top.action.Point g.left := by
          apply PermWreath.ext
          · simp
          · simpa using hg1
        rw [hgeq]
        exact hbase


theorem ForestContainer.toPerm_mem_transpositionCore_of_portrait_weights_two :
    ∀ (F : ForestContainer.{u}) (g : F.action.Actor),
      (∀ x : F.portraitLocations g, (F.portraitValue g x).weight = 2) →
        F.action.toPermHom g ∈ transpositionCore F.action.toPermHom.range
  | .tree T, g => by
      intro hall
      exact T.toPerm_mem_transpositionCore_of_portrait_weights_two g hall
  | .sum F₁ F₂, g => by
      classical
      intro hall
      apply SolubleAction.sum_toPerm_mem_transpositionCore_of_components
      · apply ForestContainer.toPerm_mem_transpositionCore_of_portrait_weights_two F₁ g.1
        intro y
        have hy := y.2
        simp only [ForestContainer.portraitLocations, Finset.mem_filter,
          Finset.mem_univ, true_and] at hy
        let l : ForestLocation (ForestContainer.sum F₁ F₂) := by
          change ForestLocation F₁ ⊕ ForestLocation F₂
          exact Sum.inl y.1
        have hl : l ∈ (ForestContainer.sum F₁ F₂).portraitLocations g := by
          simp only [ForestContainer.portraitLocations, Finset.mem_filter,
            Finset.mem_univ, true_and]
          change ((ForestContainer.sum F₁ F₂).portrait g l).isSome = true
          rw [show l = Sum.inl y.1 by rfl, ForestContainer.portrait.eq_2]
          exact hy
        let x : (ForestContainer.sum F₁ F₂).portraitLocations g :=
          ⟨l, hl⟩
        have hwhole : forestPortraitWeight
            ((ForestContainer.sum F₁ F₂).portrait g) l = 2 :=
          ((ForestContainer.sum F₁ F₂).portraitValue_weight_eq g x).symm.trans
            (hall x)
        rw [F₁.portraitValue_weight_eq g.1 y]
        change forestPortraitWeight (F₁.portrait g.1) y.1 = 2 at hwhole
        exact hwhole
      · apply ForestContainer.toPerm_mem_transpositionCore_of_portrait_weights_two F₂ g.2
        intro y
        have hy := y.2
        simp only [ForestContainer.portraitLocations, Finset.mem_filter,
          Finset.mem_univ, true_and] at hy
        let l : ForestLocation (ForestContainer.sum F₁ F₂) := by
          change ForestLocation F₁ ⊕ ForestLocation F₂
          exact Sum.inr y.1
        have hl : l ∈ (ForestContainer.sum F₁ F₂).portraitLocations g := by
          simp only [ForestContainer.portraitLocations, Finset.mem_filter,
            Finset.mem_univ, true_and]
          change ((ForestContainer.sum F₁ F₂).portrait g l).isSome = true
          rw [show l = Sum.inr y.1 by rfl, ForestContainer.portrait.eq_3]
          exact hy
        let x : (ForestContainer.sum F₁ F₂).portraitLocations g :=
          ⟨l, hl⟩
        have hwhole : forestPortraitWeight
            ((ForestContainer.sum F₁ F₂).portrait g) l = 2 :=
          ((ForestContainer.sum F₁ F₂).portraitValue_weight_eq g x).symm.trans
            (hall x)
        rw [F₂.portraitValue_weight_eq g.2 y]
        change forestPortraitWeight (F₂.portrait g.2) y.1 = 2 at hwhole
        exact hwhole

theorem ForestContainer.two_mul_card_portraitLocations_le_supportCard
    (F : ForestContainer.{u}) (g : F.action.Actor) :
    2 * (F.portraitLocations g).card ≤ F.action.supportCard g := by
  have h := Finset.card_nsmul_le_sum Finset.univ
    (fun x : F.portraitLocations g ↦ (F.portraitValue g x).weight) 2
    (fun x _hx ↦ (F.portraitValue g x).two_le_weight)
  rw [F.sum_portraitValue_weight] at h
  simpa [Fintype.card_coe, mul_comm] using h

theorem ForestContainer.two_mul_card_portraitLocations_le_supportCard_sub_one_of_not_core
    (F : ForestContainer.{u}) (g : F.action.Actor)
    (hg : F.action.toPermHom g ∉ transpositionCore F.action.toPermHom.range) :
    2 * (F.portraitLocations g).card ≤ F.action.supportCard g - 1 := by
  classical
  have hnotall : ¬ ∀ x : F.portraitLocations g,
      (F.portraitValue g x).weight = 2 := by
    intro hall
    exact hg (F.toPerm_mem_transpositionCore_of_portrait_weights_two g hall)
  push_neg at hnotall
  obtain ⟨x, hx⟩ := hnotall
  have hlt :
      (∑ _y : F.portraitLocations g, 2) <
        ∑ y : F.portraitLocations g, (F.portraitValue g y).weight := by
    apply Finset.sum_lt_sum
    · intro y _hy
      exact (F.portraitValue g y).two_le_weight
    · exact ⟨x, Finset.mem_univ _, by
        have htwo := (F.portraitValue g x).two_le_weight
        omega⟩
  rw [F.sum_portraitValue_weight] at hlt
  have hlt' : 2 * (F.portraitLocations g).card < F.action.supportCard g := by
    simpa [Fintype.card_coe, mul_comm] using hlt
  omega


end Kourovka213

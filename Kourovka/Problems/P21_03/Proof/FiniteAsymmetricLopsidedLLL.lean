import Mathlib

/-!
# A finite asymmetric lopsided Lovasz local lemma

This file gives a cardinality-only form of the lopsided local lemma.  Events
are finsets in a finite sample space, so the statement and proof do not use
measure theory or division by conditional probabilities.
-/

namespace Kourovka213

open scoped BigOperators

section FiniteEvents

variable {Omega I : Type*} [Fintype Omega] [DecidableEq Omega] [DecidableEq I]

/-- Outcomes avoiding every event indexed by `S`. -/
def avoidEvents (E : I -> Finset Omega) (S : Finset I) : Finset Omega :=
  Finset.univ.filter fun omega => ∀ i ∈ S, omega ∉ E i

@[simp]
theorem mem_avoidEvents {E : I -> Finset Omega} {S : Finset I} {omega : Omega} :
    omega ∈ avoidEvents E S ↔ ∀ i ∈ S, omega ∉ E i := by
  simp [avoidEvents]

@[simp]
theorem avoidEvents_empty (E : I -> Finset Omega) :
    avoidEvents E ∅ = Finset.univ := by
  ext omega
  simp

theorem avoidEvents_insert (E : I -> Finset Omega) (i : I) (S : Finset I) :
    avoidEvents E (insert i S) = avoidEvents E S \ E i := by
  ext omega
  simp [and_comm]

theorem avoidEvents_anti {E : I -> Finset Omega} {S T : Finset I} (hST : S ⊆ T) :
    avoidEvents E T ⊆ avoidEvents E S := by
  intro omega homega
  rw [mem_avoidEvents] at homega ⊢
  exact fun i hi => homega i (hST hi)

/-- The exact partition of the outcomes avoiding `S` according to whether
the additional event `i` occurs. -/
theorem card_avoidEvents_insert_add_card_inter
    (E : I -> Finset Omega) (i : I) (S : Finset I) :
    ((avoidEvents E (insert i S)).card : Real) +
        ((E i ∩ avoidEvents E S).card : Real) =
      ((avoidEvents E S).card : Real) := by
  rw [avoidEvents_insert]
  exact_mod_cast (by
    simpa [Finset.inter_comm] using
      Finset.card_sdiff_add_card_inter (avoidEvents E S) (E i))

/-- A finite cardinality formulation of the lopsided conditional estimate.
For a set of indices outside the declared neighborhood of `i`, conditioning
on avoidance may increase the density of `E i` by at most the factor encoded
by `p i`. -/
def FiniteLopsidedBound (E : I -> Finset Omega) (N : I -> Finset I)
    (p : I -> Real) : Prop :=
  ∀ i S, i ∉ S -> (∀ j ∈ S, j ∉ N i) ->
    ((E i ∩ avoidEvents E S).card : Real) <=
      p i * ((avoidEvents E S).card : Real)

/-- The induction heart of the finite asymmetric lopsided local lemma.
Every event satisfies the desired conditional estimate after conditioning on
avoidance of an arbitrary finite set of other events. -/
theorem finiteLopsided_conditional_bound
    {E : I -> Finset Omega} {N : I -> Finset I} {p x : I -> Real}
    (hND : FiniteLopsidedBound E N p)
    (hx0 : ∀ i, 0 <= x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i <= x i * ∏ j ∈ N i, (1 - x j)) :
    ∀ S i, i ∉ S ->
      ((E i ∩ avoidEvents E S).card : Real) <=
        x i * ((avoidEvents E S).card : Real) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
      intro i hiS
      let R : Finset I := S.filter fun j => j ∈ N i
      let T : Finset I := S.filter fun j => j ∉ N i
      have hRsubS : R ⊆ S := by
        intro j hj
        exact (Finset.mem_filter.mp hj).1
      have hTsubS : T ⊆ S := by
        intro j hj
        exact (Finset.mem_filter.mp hj).1
      have hRsubN : R ⊆ N i := by
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      have hToutside : ∀ j ∈ T, j ∉ N i := by
        intro j hj
        exact (Finset.mem_filter.mp hj).2
      have hRT : T ∪ R = S := by
        ext j
        simp [R, T]
        tauto
      have hdisj : Disjoint T R := by
        rw [Finset.disjoint_left]
        intro j hjT hjR
        exact (Finset.mem_filter.mp hjT).2 (Finset.mem_filter.mp hjR).2
      have hND_T :
          ((E i ∩ avoidEvents E T).card : Real) <=
            p i * ((avoidEvents E T).card : Real) :=
        hND i T (fun hiT => hiS (hTsubS hiT)) hToutside
      have hAvoid :
          (∏ j ∈ R, (1 - x j)) * ((avoidEvents E T).card : Real) <=
            ((avoidEvents E S).card : Real) := by
        have hsubproduct : ∀ U : Finset I, U ⊆ R ->
            (∏ j ∈ U, (1 - x j)) * ((avoidEvents E T).card : Real) <=
              ((avoidEvents E (T ∪ U)).card : Real) := by
          intro U
          induction U using Finset.induction_on with
          | empty => intro _; simp
          | @insert a U haU hU =>
              intro hUR
              have hUsubR : U ⊆ R := by
                intro j hj
                exact hUR (Finset.mem_insert_of_mem hj)
              have haR : a ∈ R := hUR (Finset.mem_insert_self a U)
              have haS : a ∈ S := hRsubS haR
              have haT : a ∉ T := by
                intro haT
                exact Finset.disjoint_left.mp hdisj haT haR
              have haTU : a ∉ T ∪ U := by simp [haT, haU]
              have hTUSub : T ∪ U ⊆ S := by
                exact Finset.union_subset hTsubS (hUsubR.trans hRsubS)
              have hTUStrict : T ∪ U ⊂ S := by
                rw [Finset.ssubset_iff_subset_ne]
                refine ⟨hTUSub, ?_⟩
                intro heq
                exact haTU (heq.symm ▸ haS)
              have hconditional := ih (T ∪ U) hTUStrict a haTU
              have hpartition := card_avoidEvents_insert_add_card_inter E a (T ∪ U)
              have hstep :
                  (1 - x a) * ((avoidEvents E (T ∪ U)).card : Real) <=
                    ((avoidEvents E (insert a (T ∪ U))).card : Real) := by
                nlinarith
              have hfactor : 0 <= 1 - x a := sub_nonneg.mpr (le_of_lt (hx1 a))
              calc
                (∏ j ∈ insert a U, (1 - x j)) *
                      ((avoidEvents E T).card : Real) =
                    (1 - x a) *
                      ((∏ j ∈ U, (1 - x j)) *
                        ((avoidEvents E T).card : Real)) := by
                          rw [Finset.prod_insert haU]
                          ring
                _ <= (1 - x a) * ((avoidEvents E (T ∪ U)).card : Real) :=
                  mul_le_mul_of_nonneg_left (hU hUsubR) hfactor
                _ <= ((avoidEvents E (T ∪ insert a U)).card : Real) := by
                  simpa [Finset.union_insert] using hstep
        simpa [hRT] using hsubproduct R (fun _ h => h)
      have hbad_mono :
          ((E i ∩ avoidEvents E S).card : Real) <=
            ((E i ∩ avoidEvents E T).card : Real) := by
        exact_mod_cast Finset.card_le_card (by
          intro omega homega
          rw [Finset.mem_inter] at homega ⊢
          exact ⟨homega.1, avoidEvents_anti hTsubS homega.2⟩)
      have hprodNR :
          (∏ j ∈ N i, (1 - x j)) <= ∏ j ∈ R, (1 - x j) := by
        exact Finset.prod_le_prod_of_subset_of_le_one hRsubN
          (fun j _ => sub_nonneg.mpr (le_of_lt (hx1 j)))
          (fun j _ _ => by linarith [hx0 j])
      have hcardT : 0 <= ((avoidEvents E T).card : Real) := by positivity
      have hcardS : 0 <= ((avoidEvents E S).card : Real) := by positivity
      calc
        ((E i ∩ avoidEvents E S).card : Real) <=
            ((E i ∩ avoidEvents E T).card : Real) := hbad_mono
        _ <= p i * ((avoidEvents E T).card : Real) := hND_T
        _ <= (x i * ∏ j ∈ N i, (1 - x j)) *
              ((avoidEvents E T).card : Real) :=
          mul_le_mul_of_nonneg_right (hp i) hcardT
        _ <= (x i * ∏ j ∈ R, (1 - x j)) *
              ((avoidEvents E T).card : Real) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprodNR (hx0 i)) hcardT
        _ <= x i * ((avoidEvents E S).card : Real) := by
          have := mul_le_mul_of_nonneg_left hAvoid (hx0 i)
          nlinarith

/-- Finite asymmetric lopsided local lemma, with the conclusion stated for
an arbitrary finite set of event indices. -/
theorem finite_asymmetric_lopsided_lll_on
    {E : I -> Finset Omega} {N : I -> Finset I} {p x : I -> Real}
    (hND : FiniteLopsidedBound E N p)
    (hx0 : ∀ i, 0 <= x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i <= x i * ∏ j ∈ N i, (1 - x j))
    (S : Finset I) :
    (∏ i ∈ S, (1 - x i)) * Fintype.card Omega <=
      ((avoidEvents E S).card : Real) := by
  have hconditional := finiteLopsided_conditional_bound hND hx0 hx1 hp
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hiS hS =>
      have hpartition := card_avoidEvents_insert_add_card_inter E i S
      have hibad := hconditional S i hiS
      have histep :
          (1 - x i) * ((avoidEvents E S).card : Real) <=
            ((avoidEvents E (insert i S)).card : Real) := by
        nlinarith
      have hifactor : 0 <= 1 - x i := sub_nonneg.mpr (le_of_lt (hx1 i))
      calc
        (∏ j ∈ insert i S, (1 - x j)) * Fintype.card Omega =
            (1 - x i) *
              ((∏ j ∈ S, (1 - x j)) * Fintype.card Omega) := by
                rw [Finset.prod_insert hiS]
                ring
        _ <= (1 - x i) * ((avoidEvents E S).card : Real) :=
          mul_le_mul_of_nonneg_left hS hifactor
        _ <= ((avoidEvents E (insert i S)).card : Real) := histep

/-- Once the core events satisfy the local-lemma conditional estimate, an
additional event can be bounded after conditioning on avoidance of all core
events.  Only the core events in `R` are allowed to interact with the
additional event.  The product is kept on the left, so this statement needs
no positivity or division hypothesis for the conditioned sample space. -/
theorem finiteLopsided_conditioned_external_bound
    {E : I -> Finset Omega} {N : I -> Finset I} {p x : I -> Real}
    (hND : FiniteLopsidedBound E N p)
    (hx0 : ∀ i, 0 <= x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i <= x i * ∏ j ∈ N i, (1 - x j))
    (A : Finset Omega) (R S : Finset I) (q : Real) (hq : 0 <= q)
    (hExternal : ∀ T : Finset I,
      (∀ j ∈ T, j ∉ R) ->
        ((A ∩ avoidEvents E T).card : Real) <=
          q * ((avoidEvents E T).card : Real)) :
    (∏ j ∈ S.filter fun j => j ∈ R, (1 - x j)) *
        ((A ∩ avoidEvents E S).card : Real) <=
      q * ((avoidEvents E S).card : Real) := by
  let U : Finset I := S.filter fun j => j ∈ R
  let T : Finset I := S.filter fun j => j ∉ R
  have hTsubS : T ⊆ S := fun _ h => (Finset.mem_filter.mp h).1
  have hUsubS : U ⊆ S := fun _ h => (Finset.mem_filter.mp h).1
  have hToutside : ∀ j ∈ T, j ∉ R :=
    fun _ h => (Finset.mem_filter.mp h).2
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro j hjT hjU
    exact (Finset.mem_filter.mp hjT).2 (Finset.mem_filter.mp hjU).2
  have hTU : T ∪ U = S := by
    ext j
    simp [T, U]
    tauto
  have hconditional := finiteLopsided_conditional_bound hND hx0 hx1 hp
  have hAvoid :
      (∏ j ∈ U, (1 - x j)) * ((avoidEvents E T).card : Real) <=
        ((avoidEvents E S).card : Real) := by
    have hsubproduct : ∀ V : Finset I, V ⊆ U ->
        (∏ j ∈ V, (1 - x j)) * ((avoidEvents E T).card : Real) <=
          ((avoidEvents E (T ∪ V)).card : Real) := by
      intro V
      induction V using Finset.induction_on with
      | empty => intro _; simp
      | @insert a V haV hV =>
          intro hVU
          have hVsubU : V ⊆ U := fun j hj =>
            hVU (Finset.mem_insert_of_mem hj)
          have haU : a ∈ U := hVU (Finset.mem_insert_self a V)
          have haT : a ∉ T := by
            intro haT
            exact Finset.disjoint_left.mp hdisj haT haU
          have haTV : a ∉ T ∪ V := by simp [haT, haV]
          have hbad := hconditional (T ∪ V) a haTV
          have hpartition := card_avoidEvents_insert_add_card_inter E a (T ∪ V)
          have hstep :
              (1 - x a) * ((avoidEvents E (T ∪ V)).card : Real) <=
                ((avoidEvents E (insert a (T ∪ V))).card : Real) := by
            nlinarith
          have hfactor : 0 <= 1 - x a := sub_nonneg.mpr (le_of_lt (hx1 a))
          calc
            (∏ j ∈ insert a V, (1 - x j)) *
                  ((avoidEvents E T).card : Real) =
                (1 - x a) *
                  ((∏ j ∈ V, (1 - x j)) *
                    ((avoidEvents E T).card : Real)) := by
                      rw [Finset.prod_insert haV]
                      ring
            _ <= (1 - x a) * ((avoidEvents E (T ∪ V)).card : Real) :=
              mul_le_mul_of_nonneg_left (hV hVsubU) hfactor
            _ <= ((avoidEvents E (T ∪ insert a V)).card : Real) := by
              simpa [Finset.union_insert] using hstep
    simpa [hTU] using hsubproduct U (fun _ h => h)
  have hbad_mono :
      ((A ∩ avoidEvents E S).card : Real) <=
        ((A ∩ avoidEvents E T).card : Real) := by
    exact_mod_cast Finset.card_le_card (by
      intro omega homega
      rw [Finset.mem_inter] at homega ⊢
      exact ⟨homega.1, avoidEvents_anti hTsubS homega.2⟩)
  have hExternalT := hExternal T hToutside
  have hprod_nonneg : 0 <= ∏ j ∈ U, (1 - x j) :=
    Finset.prod_nonneg fun j _ => sub_nonneg.mpr (le_of_lt (hx1 j))
  calc
    (∏ j ∈ S.filter fun j => j ∈ R, (1 - x j)) *
          ((A ∩ avoidEvents E S).card : Real) =
        (∏ j ∈ U, (1 - x j)) *
          ((A ∩ avoidEvents E S).card : Real) := by rfl
    _ <= (∏ j ∈ U, (1 - x j)) *
          ((A ∩ avoidEvents E T).card : Real) :=
      mul_le_mul_of_nonneg_left hbad_mono hprod_nonneg
    _ <= (∏ j ∈ U, (1 - x j)) *
          (q * ((avoidEvents E T).card : Real)) :=
      mul_le_mul_of_nonneg_left hExternalT hprod_nonneg
    _ = q * ((∏ j ∈ U, (1 - x j)) *
          ((avoidEvents E T).card : Real)) := by ring
    _ <= q * ((avoidEvents E S).card : Real) :=
      mul_le_mul_of_nonneg_left hAvoid hq

/-- The usual full-index-set form of the finite asymmetric lopsided local
lemma. -/
theorem finite_asymmetric_lopsided_lll
    [Fintype I]
    {E : I -> Finset Omega} {N : I -> Finset I} {p x : I -> Real}
    (hND : FiniteLopsidedBound E N p)
    (hx0 : ∀ i, 0 <= x i) (hx1 : ∀ i, x i < 1)
    (hp : ∀ i, p i <= x i * ∏ j ∈ N i, (1 - x j)) :
    (∏ i : I, (1 - x i)) * Fintype.card Omega <=
      ((avoidEvents E Finset.univ).card : Real) := by
  simpa using finite_asymmetric_lopsided_lll_on hND hx0 hx1 hp
    (Finset.univ : Finset I)

end FiniteEvents

end Kourovka213

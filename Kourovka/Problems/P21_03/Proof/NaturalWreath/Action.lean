import Kourovka.Problems.P21_03.Proof.NaturalWreath.Defs
import Mathlib.GroupTheory.Perm.Support

/-!
# The natural (imprimitive) action of a permutational wreath product

For `g = (f,q)` the action on the disjoint union of copies of `Δ`, represented
as `ι × Δ`, is

`g • (i,d) = (q • i, f (q • i) • d)`.

This is the natural imprimitive action, rather than the product action on
`ι → Δ` in the source `Saxl/PermWreath/Action.lean`.
-/

namespace Kourovka213

variable (X Q ι Δ : Type*)
variable [Group X] [Group Q] [MulAction Q ι] [MulAction X Δ]

/-- The natural imprimitive scalar action on `ι × Δ`. -/
instance permWreathNaturalSMul : SMul (PermWreath X Q ι) (ι × Δ) where
  smul g p := (g.right • p.1, g.left (g.right • p.1) • p.2)

/-- The defining formula for the natural action. -/
@[simp]
theorem permWreath_natural_smul (g : PermWreath X Q ι) (p : ι × Δ) :
    g • p = (g.right • p.1, g.left (g.right • p.1) • p.2) := rfl

/-- The scalar action satisfies the group-action laws. -/
instance permWreathNaturalMulAction : MulAction (PermWreath X Q ι) (ι × Δ) where
  one_smul p := by
    change ((1 : Q) • p.1, (1 : X) • p.2) = p
    ext <;> simp
  mul_smul g h p := by
    change
      ((g.right * h.right) • p.1,
        (g.left ((g.right * h.right) • p.1) *
            h.left (g.right⁻¹ • ((g.right * h.right) • p.1))) • p.2) =
      (g.right • (h.right • p.1),
        g.left (g.right • (h.right • p.1)) •
          (h.left (h.right • p.1) • p.2))
    ext <;> simp [mul_smul]

/-- The defining formula, split into coordinates. -/
@[simp]
theorem permWreath_natural_smul_mk (g : PermWreath X Q ι) (i : ι) (d : Δ) :
    g • (i, d) = (g.right • i, g.left (g.right • i) • d) := rfl

/-- A base-group element fixes the block index and acts independently inside
each block. -/
@[simp]
theorem base_natural_smul (f : ι → X) (i : ι) (d : Δ) :
    PermWreath.base X Q ι f • (i, d) = (i, f i • d) := by
  simp

/-- A top-group element permutes the blocks and does not change the inner
coordinate. -/
@[simp]
theorem top_natural_smul (q : Q) (i : ι) (d : Δ) :
    PermWreath.top X Q ι q • (i, d) = (q • i, d) := by
  simp

/-- A single-coordinate element acts only in its selected block. -/
@[simp]
theorem coordinate_natural_smul [DecidableEq ι]
    (i : ι) (x : X) (j : ι) (d : Δ) :
    PermWreath.coordinate X Q ι i x • (j, d) =
      if j = i then (j, x • d) else (j, d) := by
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The permutation representation afforded by the natural action. -/
def PermWreath.naturalToPerm : PermWreath X Q ι →* Equiv.Perm (ι × Δ) :=
  MulAction.toPermHom (PermWreath X Q ι) (ι × Δ)

@[simp]
theorem PermWreath.naturalToPerm_apply
    (g : PermWreath X Q ι) (i : ι) (d : Δ) :
    PermWreath.naturalToPerm X Q ι Δ g (i, d) =
      (g.right • i, g.left (g.right • i) • d) := rfl

/-- Pointwise support criterion for the natural permutation representation. -/
@[simp]
theorem PermWreath.mem_support_naturalToPerm_iff
    [Fintype ι] [Fintype Δ] [DecidableEq ι] [DecidableEq Δ]
    (g : PermWreath X Q ι) (i : ι) (d : Δ) :
    (i, d) ∈ (PermWreath.naturalToPerm X Q ι Δ g).support ↔
      g.right • i ≠ i ∨ g.left (g.right • i) • d ≠ d := by
  rw [Equiv.Perm.mem_support]
  simp only [PermWreath.naturalToPerm_apply]
  constructor
  · intro h
    by_contra hnone
    simp only [not_or, not_not] at hnone
    exact h (Prod.ext hnone.1 hnone.2)
  · rintro (hi | hd) hpair
    · exact hi (congrArg Prod.fst hpair)
    · exact hd (congrArg Prod.snd hpair)

/-- Support criterion for a pure base-group element. -/
@[simp]
theorem PermWreath.mem_support_naturalToPerm_base_iff
    [Fintype ι] [Fintype Δ] [DecidableEq ι] [DecidableEq Δ]
    (f : ι → X) (i : ι) (d : Δ) :
    (i, d) ∈
        (PermWreath.naturalToPerm X Q ι Δ (PermWreath.base X Q ι f)).support ↔
      f i • d ≠ d := by
  simp

/-- Support criterion for a pure top-group element.  A moved block contributes
all of its points. -/
@[simp]
theorem PermWreath.mem_support_naturalToPerm_top_iff
    [Fintype ι] [Fintype Δ] [DecidableEq ι] [DecidableEq Δ]
    (q : Q) (i : ι) (d : Δ) :
    (i, d) ∈
        (PermWreath.naturalToPerm X Q ι Δ (PermWreath.top X Q ι q)).support ↔
      q • i ≠ i := by
  simp

/-- Support criterion for a single-coordinate base element. -/
@[simp]
theorem PermWreath.mem_support_naturalToPerm_coordinate_iff
    [Fintype ι] [Fintype Δ] [DecidableEq ι] [DecidableEq Δ]
    (i : ι) (x : X) (j : ι) (d : Δ) :
    (j, d) ∈
        (PermWreath.naturalToPerm X Q ι Δ
          (PermWreath.coordinate X Q ι i x)).support ↔
      j = i ∧ x • d ≠ d := by
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- If both component actions are faithful and the inner point type is
nonempty, then the natural wreath action is faithful. -/
instance permWreathNaturalFaithfulSMul
    [FaithfulSMul X Δ] [FaithfulSMul Q ι] [Nonempty Δ] :
    FaithfulSMul (PermWreath X Q ι) (ι × Δ) where
  eq_of_smul_eq_smul := by
    intro g h hsmul
    have hright : g.right = h.right := by
      have hfaithQ : FaithfulSMul Q ι := inferInstance
      apply hfaithQ.eq_of_smul_eq_smul
      intro i
      let d : Δ := Classical.choice inferInstance
      exact congrArg Prod.fst (hsmul (i, d))
    apply PermWreath.ext
    · funext i
      have hfaithX : FaithfulSMul X Δ := inferInstance
      apply hfaithX.eq_of_smul_eq_smul
      intro d
      have hp := congrArg Prod.snd (hsmul (g.right⁻¹ • i, d))
      simpa [hright] using hp
    · exact hright

/-- Consequently the natural permutation representation is injective. -/
theorem PermWreath.naturalToPerm_injective
    [FaithfulSMul X Δ] [FaithfulSMul Q ι] [Nonempty Δ] :
    Function.Injective (PermWreath.naturalToPerm X Q ι Δ) :=
  MulAction.toPerm_injective

end Kourovka213

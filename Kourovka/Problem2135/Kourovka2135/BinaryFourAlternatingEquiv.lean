import Kourovka2135.SLTwoPrincipalSeriesAugmentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Data.Fintype.EquivFin

/-! An actual isomorphism SL2(F) ≃ A5 for a characteristic-two field with four
elements. The projective permutation comes from inverse row multiplication.
Its kernel is checked on infinity, zero, and one; perfectness kills its sign,
and the checked cardinalities make the embedding surjective. No exceptional
group isomorphism or classification is assumed.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinaryFourAlternatingEquiv

open SLTwoHomogeneousFunctions SLTwoPrincipalSeries

attribute [local instance] Classical.propDecidable

variable {F : Type u} [Field F]

theorem projectiveIndex_eq_none_iff (z : Point F) :
    projectiveIndex z = none ↔ z.val 0 = 0 := by
  classical
  by_cases hz : z.val 0 = 0 <;> simp [projectiveIndex, hz]

theorem projectiveIndex_eq_some_iff (z : Point F) (t : F) :
    projectiveIndex z = some t ↔ z.val 0 ≠ 0 ∧ z.val 1 = t * z.val 0 := by
  classical
  by_cases hz : z.val 0 = 0
  · simp [projectiveIndex, hz]
  · simp [projectiveIndex, hz, div_eq_iff hz]

@[simp] theorem projectivePermutation_one :
    projectivePermutation (1 : SLTwo.SL2 F) = 1 := by
  apply Equiv.ext
  intro t
  change projectiveIndex (pointAction 1 (projectiveRepresentative t)) = t
  rw [pointAction_one, projectiveIndex_representative]

/-- Row multiplication gives an antihomomorphism on projective points. -/
theorem projectivePermutation_mul (g h : SLTwo.SL2 F) :
    projectivePermutation (g * h) = projectivePermutation h * projectivePermutation g := by
  apply Equiv.ext
  intro t
  change projectiveIndex (pointAction (g * h) (projectiveRepresentative t)) =
    projectiveIndex (pointAction h (projectiveRepresentative
      (projectiveIndex (pointAction g (projectiveRepresentative t)))))
  rw [pointAction_mul]
  exact projectiveIndex_action_representative h
    (pointAction g (projectiveRepresentative t))

/-- Inverting the matrix gives the actual left permutation action. -/
def projectiveHom : SLTwo.SL2 F →* Equiv.Perm (Option F) where
  toFun g := projectivePermutation g⁻¹
  map_one' := by rw [inv_one, projectivePermutation_one]
  map_mul' g h := by rw [mul_inv_rev, projectivePermutation_mul]

@[simp] theorem projectiveHom_apply (g : SLTwo.SL2 F) (t : Option F) :
    projectiveHom g t =
      projectiveIndex (pointAction g⁻¹ (projectiveRepresentative t)) := rfl

section CharacteristicTwo
variable [CharP F 2]

/-- Fixing three explicit projective points forces a characteristic-two SL2
matrix to be the identity. This is the actual kernel calculation. -/
theorem eq_one_of_projectivePermutation_eq_one (g : SLTwo.SL2 F)
    (hg : projectivePermutation g = 1) : g = 1 := by
  have hinf := Equiv.congr_fun hg none
  change projectiveIndex (pointAction g (infinity F)) = none at hinf
  have hc : g.val 1 0 = 0 := by
    have h := (projectiveIndex_eq_none_iff _).mp hinf
    simpa [pointAction, infinity, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  have hzero := Equiv.congr_fun hg (some (0 : F))
  change projectiveIndex (pointAction g (affine (0 : F))) = some 0 at hzero
  have hb : g.val 0 1 = 0 := by
    have h := ((projectiveIndex_eq_some_iff _ _).mp hzero).2
    simpa [pointAction, affine, Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h
  have hone := Equiv.congr_fun hg (some (1 : F))
  change projectiveIndex (pointAction g (affine (1 : F))) = some 1 at hone
  have hd : g.val 1 1 = g.val 0 0 := by
    have h := ((projectiveIndex_eq_some_iff _ _).mp hone).2
    simpa [pointAction, affine, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb, hc] using h
  have hdet : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  have hsq : g.val 0 0 ^ 2 = 1 := by
    simpa only [hb, hc, hd, mul_zero, sub_zero, pow_two] using hdet
  have ha : g.val 0 0 = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp hsq
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem projectiveHom_injective : Function.Injective (projectiveHom (F := F)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have h : g⁻¹ = 1 := eq_one_of_projectivePermutation_eq_one g⁻¹ hg
  exact inv_eq_one.mp h

variable [Fintype F]

omit [CharP F 2] in
/-- Cardinality four supplies a field element different from zero and one. -/
theorem exists_nonzero_ne_one (hcard : Fintype.card F = 4) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  have hlt : ({(0 : F), 1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_pair zero_ne_one, Finset.card_univ, hcard]
    decide
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, ?_⟩
  simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using ha

/-- Perfectness comes from the actual SL2 transvection calculation in mathlib. -/
theorem isPerfect_of_card_four (hcard : Fintype.card F = 4) :
    Group.IsPerfect (SLTwo.SL2 F) := by
  obtain ⟨a, ha, ha1⟩ := exists_nonzero_ne_one hcard
  have hsq : a ^ 2 ≠ 1 := by
    intro h
    apply ha1
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp h
  exact ⟨Matrix.SL2.commutator_eq_top ha hsq⟩

/-- Choose actual labels for the five projective points. -/
def projectiveLabels (hcard : Fintype.card F = 4) : Option F ≃ Fin 5 :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_option, hcard])

/-- Relabel the actual faithful action onto the fixed five-point type. -/
def fivePointHom (hcard : Fintype.card F = 4) :
    SLTwo.SL2 F →* Equiv.Perm (Fin 5) :=
  (projectiveLabels hcard).permCongrHom.toMonoidHom.comp projectiveHom

omit [CharP F 2] in
@[simp] theorem fivePointHom_apply (hcard : Fintype.card F = 4)
    (g : SLTwo.SL2 F) (i : Fin 5) :
    fivePointHom hcard g i = projectiveLabels hcard
      (projectiveHom g ((projectiveLabels hcard).symm i)) := rfl

theorem fivePointHom_injective (hcard : Fintype.card F = 4) :
    Function.Injective (fivePointHom hcard) :=
  (projectiveLabels hcard).permCongrHom.injective.comp projectiveHom_injective

/-- The sign homomorphism kills the actual perfect image. -/
theorem fivePointHom_mem_alternatingGroup (hcard : Fintype.card F = 4)
    (g : SLTwo.SL2 F) : fivePointHom hcard g ∈ alternatingGroup (Fin 5) := by
  let : Group.IsPerfect (SLTwo.SL2 F) := isPerfect_of_card_four hcard
  let s : SLTwo.SL2 F →* ℤˣ := Equiv.Perm.sign.comp (fivePointHom hcard)
  have hs : commutator (SLTwo.SL2 F) ≤ s.ker := Abelianization.commutator_subset_ker s
  exact hs (Group.IsPerfect.mem_commutator (g := g))

/-- The actual projective action with its codomain restricted to A5. -/
def alternatingHom (hcard : Fintype.card F = 4) :
    SLTwo.SL2 F →* alternatingGroup (Fin 5) where
  toFun g := ⟨fivePointHom hcard g, fivePointHom_mem_alternatingGroup hcard g⟩
  map_one' := Subtype.ext (map_one (fivePointHom hcard))
  map_mul' g h := Subtype.ext (map_mul (fivePointHom hcard) g h)

@[simp] theorem alternatingHom_coe (hcard : Fintype.card F = 4) (g : SLTwo.SL2 F) :
    (alternatingHom hcard g : Equiv.Perm (Fin 5)) = fivePointHom hcard g := rfl

theorem alternatingHom_injective (hcard : Fintype.card F = 4) :
    Function.Injective (alternatingHom hcard) := by
  intro g h hgh
  apply fivePointHom_injective hcard
  exact congrArg Subtype.val hgh

omit [CharP F 2] in
theorem card_slTwo (hcard : Fintype.card F = 4) :
    Fintype.card (SLTwo.SL2 F) = 60 := by
  classical
  have h := SLTwo.sl2_card_formula (K := F)
  simpa [Nat.card_eq_fintype_card, hcard] using h

theorem card_alternating_five : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup]
  norm_num

theorem alternatingHom_bijective (hcard : Fintype.card F = 4) :
    Function.Bijective (alternatingHom hcard) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨alternatingHom_injective hcard,
    (card_slTwo hcard).trans card_alternating_five.symm⟩

/-- Actual exceptional isomorphism, constructed from the projective action. -/
def equiv (hcard : Fintype.card F = 4) :
    SLTwo.SL2 F ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective (alternatingHom hcard) (alternatingHom_bijective hcard)

@[simp] theorem equiv_apply (hcard : Fintype.card F = 4) (g : SLTwo.SL2 F) :
    equiv hcard g = alternatingHom hcard g := rfl

end CharacteristicTwo
end Kourovka2135.BinaryFourAlternatingEquiv

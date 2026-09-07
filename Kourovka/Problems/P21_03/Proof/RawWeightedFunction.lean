import Kourovka.Problems.P21_03.Proof.WeightedConfiguration

/-!
# A pointwise encoding of raw weighted configurations

The encoding records `none` away from the selected locations and records the
dependent weight-label pair at every selected location.  It is lossless and
does not require choosing an order on the site type.
-/

namespace Kourovka213

universe u

namespace RawWeightedConfiguration

/-- Encode a raw weighted configuration as an optional dependent label at each
site. -/
noncomputable def toFunction
    {Site : Type u} [Fintype Site]
    (c : RawWeightedConfiguration Site D s k) :
    Site → Option (Σ a : ℕ, Fin (D ^ a)) := by
  classical
  intro i
  exact if hi : i ∈ c.locations then
    some ⟨c.weight ⟨i, hi⟩, c.label ⟨i, hi⟩⟩
  else none

@[simp]
theorem toFunction_apply_of_mem
    {Site : Type u} [Fintype Site]
    (c : RawWeightedConfiguration Site D s k) (i : Site)
    (hi : i ∈ c.locations) :
    c.toFunction i =
      some ⟨c.weight ⟨i, hi⟩, c.label ⟨i, hi⟩⟩ := by
  classical
  simp [toFunction, hi]

@[simp]
theorem toFunction_apply_of_not_mem
    {Site : Type u} [Fintype Site]
    (c : RawWeightedConfiguration Site D s k) (i : Site)
    (hi : i ∉ c.locations) :
    c.toFunction i = none := by
  classical
  simp [toFunction, hi]

/-- Equality of the pointwise encodings forces equality of the raw dependent
configurations. -/
theorem eq_of_toFunction_eq
    {Site : Type u} [Fintype Site]
    {c d : RawWeightedConfiguration Site D s k}
    (h : c.toFunction = d.toFunction) : c = d := by
  classical
  have hloc : c.locations = d.locations := by
    ext i
    have hi := congrFun h i
    by_cases hc : i ∈ c.locations <;> by_cases hd : i ∈ d.locations
    · simp [hc, hd]
    · simp [toFunction, hc, hd] at hi
    · simp [toFunction, hc, hd] at hi
    · simp [hc, hd]
  rcases c with ⟨L, hL, w, hwpos, hwsum, label⟩
  rcases d with ⟨L', hL', w', hwpos', hwsum', label'⟩
  dsimp only at hloc
  subst L'
  have hhL : hL' = hL := Subsingleton.elim _ _
  cases hhL
  have hw : w = w' := by
    funext x
    have hx := congrFun h x.1
    have hsigma :
        (⟨w x, label x⟩ : Σ a : ℕ, Fin (D ^ a)) =
          ⟨w' x, label' x⟩ := by
      exact Option.some.inj (by simpa [toFunction, x.2] using hx)
    exact congrArg Sigma.fst hsigma
  subst w'
  have hpos : hwpos' = hwpos := Subsingleton.elim _ _
  cases hpos
  have hsum : hwsum' = hwsum := Subsingleton.elim _ _
  cases hsum
  have hlabel : label = label' := by
    funext x
    have hx := congrFun h x.1
    have hsigma :
        (⟨w x, label x⟩ : Σ a : ℕ, Fin (D ^ a)) =
          ⟨w x, label' x⟩ := by
      exact Option.some.inj (by simpa [toFunction, x.2] using hx)
    exact eq_of_heq (Sigma.mk.inj hsigma).2
  subst label'
  rfl

/-- The pointwise optional-label encoding is injective. -/
theorem toFunction_injective
    {Site : Type u} [Fintype Site] :
    Function.Injective
      (RawWeightedConfiguration.toFunction :
        RawWeightedConfiguration Site D s k →
          Site → Option (Σ a : ℕ, Fin (D ^ a))) :=
  fun _c _d h ↦ eq_of_toFunction_eq h

end RawWeightedConfiguration

end Kourovka213

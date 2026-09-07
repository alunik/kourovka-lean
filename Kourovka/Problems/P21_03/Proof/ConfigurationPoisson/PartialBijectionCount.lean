import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Counting completions of a finite partial bijection

An equivalence between two finite subtypes of the same ambient finite type has
exactly `(N-m)!` extensions to a permutation.  This generalizes the two-point
completion count used for the first collision moment.
-/

namespace Kourovka213

section Completion

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
variable {p q : alpha → Prop} [DecidablePred p] [DecidablePred q]

private theorem subtypeCongr_apply_of_mem
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : alpha) (hx : p x) : Equiv.subtypeCongr e f x = e ⟨x, hx⟩ := by
  simp [Equiv.subtypeCongr, hx]

private theorem subtypeCongr_apply_of_not_mem
    (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x})
    (x : alpha) (hx : ¬p x) : Equiv.subtypeCongr e f x = f ⟨x, hx⟩ := by
  simp [Equiv.subtypeCongr, hx]

private theorem mem_iff_image_mem (e : {x // p x} ≃ {x // q x})
    (sigma : Equiv.Perm alpha) (hsigma : ∀ x : {x // p x}, sigma x = e x)
    (x : alpha) : p x ↔ q (sigma x) := by
  constructor
  · intro hx
    rw [hsigma ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro hx
    let y : {x // p x} := e.symm ⟨sigma x, hx⟩
    have hey : (e y : alpha) = sigma x := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨sigma x, hx⟩)
    have hxy : (y : alpha) = x := sigma.injective ((hsigma y).trans hey)
    exact hxy ▸ y.2

/-- Completing `e` to an ambient permutation is equivalent to choosing an
arbitrary equivalence of the complementary subtypes. -/
private noncomputable def partialBijectionCompletionEquiv
    (e : {x // p x} ≃ {x // q x}) :
    {sigma : Equiv.Perm alpha // ∀ x : {x // p x}, sigma x = e x} ≃
      ({x // ¬p x} ≃ {x // ¬q x}) where
  toFun sigma := sigma.1.subtypeEquiv fun x =>
    not_congr (mem_iff_image_mem e sigma.1 sigma.2 x)
  invFun f :=
    ⟨Equiv.subtypeCongr e f, fun x => by
      exact subtypeCongr_apply_of_mem e f x x.2⟩
  left_inv sigma := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : p x
    · calc
        Equiv.subtypeCongr e _ x = e ⟨x, hx⟩ :=
          subtypeCongr_apply_of_mem e _ x hx
        _ = sigma.1 x := (sigma.2 ⟨x, hx⟩).symm
    · refine (subtypeCongr_apply_of_not_mem e _ x hx).trans ?_
      rfl
  right_inv f := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change Equiv.subtypeCongr e f x.1 = (f x : alpha)
    exact subtypeCongr_apply_of_not_mem e f x.1 x.2

/-- Exact number of ambient permutations extending a fixed finite partial
bijection. -/
theorem card_perm_extending_subtype (e : {x // p x} ≃ {x // q x}) :
    Nat.card {sigma : Equiv.Perm alpha //
      ∀ x : {x // p x}, sigma x = e x} =
      (Fintype.card alpha - Fintype.card {x // p x}).factorial := by
  rw [Nat.card_congr (partialBijectionCompletionEquiv e)]
  calc
    Nat.card ({x // ¬p x} ≃ {x // ¬q x}) =
        (Fintype.card {x // ¬p x}).factorial :=
      Nat.card_eq_fintype_card.trans (Fintype.card_equiv e.toCompl)
    _ = (Fintype.card alpha - Fintype.card {x // p x}).factorial := by
      rw [Fintype.card_subtype_compl]

end Completion

section InjectivePrescription

variable {alpha iota : Type*} [Fintype alpha] [DecidableEq alpha] [Fintype iota]

/-- The canonical equivalence between the ranges of two injective indexed
families. -/
private noncomputable def rangeEquivOfInjective (f g : iota → alpha)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    {x // x ∈ Set.range f} ≃ {x // x ∈ Set.range g} :=
  (Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)

@[simp]
private theorem rangeEquivOfInjective_apply (f g : iota → alpha)
    (hf : Function.Injective f) (hg : Function.Injective g) (i : iota) :
    rangeEquivOfInjective f g hf hg ⟨f i, Set.mem_range_self i⟩ =
      ⟨g i, Set.mem_range_self i⟩ := by
  apply Subtype.ext
  simp [rangeEquivOfInjective]

private noncomputable def extendingPairEquivExtendingSubtype
    (f g : iota → alpha) (hf : Function.Injective f) (hg : Function.Injective g) :
    {sigma : Equiv.Perm alpha // ∀ i, sigma (f i) = g i} ≃
      {sigma : Equiv.Perm alpha //
        ∀ x : {x // x ∈ Set.range f},
          sigma x = rangeEquivOfInjective f g hf hg x} where
  toFun sigma := ⟨sigma.1, fun x => by
    obtain ⟨i, hi⟩ := x.2
    have hx : x = ⟨f i, Set.mem_range_self i⟩ := Subtype.ext hi.symm
    subst x
    simpa using sigma.2 i⟩
  invFun sigma := ⟨sigma.1, fun i => by
    simpa using sigma.2 ⟨f i, Set.mem_range_self i⟩⟩
  left_inv sigma := rfl
  right_inv sigma := rfl

/-- If `f` and `g` are injective `m`-point lists in an `N`-point type, then
exactly `(N-m)!` permutations satisfy `sigma (f i) = g i` for every index. -/
theorem card_perm_extending_injective_pair (f g : iota → alpha)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Nat.card {sigma : Equiv.Perm alpha // ∀ i, sigma (f i) = g i} =
      (Fintype.card alpha - Fintype.card iota).factorial := by
  rw [Nat.card_congr (extendingPairEquivExtendingSubtype f g hf hg),
    card_perm_extending_subtype (rangeEquivOfInjective f g hf hg)]
  congr 2
  exact Fintype.card_congr (Equiv.ofInjective f hf).symm

end InjectivePrescription

end Kourovka213

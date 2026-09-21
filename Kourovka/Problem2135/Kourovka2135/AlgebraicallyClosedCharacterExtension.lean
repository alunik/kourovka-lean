import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-! A unit-valued character of a subgroup of an abelian group extends to the
whole group over an algebraically closed field. The proof constructs divisible
field units and applies the existing additive Baer extension theorem. No
finiteness or characteristic-zero hypothesis is needed. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.AlgebraicallyClosedCharacterExtension

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Every positive power map on the units of an algebraically closed field is onto. -/
theorem units_pow_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (fun a : kˣ => a ^ n) := by
  intro a
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero hn)
  have hx0 : x ≠ 0 := by
    intro h
    apply a.ne_zero
    simpa only [h, zero_pow hn] using hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Units.ext
  exact hx

/-- Divisibility is constructed for the additive type tag of the units. -/
@[instance_reducible] def unitsDivisibleNat : DivisibleBy (Additive kˣ) ℕ :=
  divisibleByOfSMulRightSurj (Additive kˣ) ℕ fun {n} hn a => by
    obtain ⟨x, hx⟩ := units_pow_surjective (k := k) hn a.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-- Integer divisibility follows from natural-number divisibility. -/
@[instance_reducible] def unitsDivisibleInt : DivisibleBy (Additive kˣ) ℤ := by
  letI : DivisibleBy (Additive kˣ) ℕ := unitsDivisibleNat
  exact AddGroup.divisibleByIntOfDivisibleByNat (Additive kˣ)

/-- A character extends across any actual injective homomorphism of abelian groups. -/
theorem exists_extension_of_injective
    {A B : Type*} [CommGroup A] [CommGroup B]
    (i : A →* B) (hi : Function.Injective i) (χ : A →* kˣ) :
    ∃ ψ : B →* kˣ, ψ.comp i = χ := by
  let : DivisibleBy (Additive kˣ) ℤ := unitsDivisibleInt
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
    i.toAdditive hi χ.toAdditive
  refine ⟨MonoidHom.toAdditive.symm ψ, ?_⟩
  apply MonoidHom.ext
  intro a
  exact congrArg Additive.toMul
    (congrArg (fun f : Additive A →+ Additive kˣ => f (Additive.ofMul a)) hψ)

/-- A unit-valued character of any subgroup of an abelian group extends. -/
theorem exists_extension {A : Type*} [CommGroup A]
    (S : Subgroup A) (χ : S →* kˣ) :
    ∃ ψ : A →* kˣ, ψ.comp S.subtype = χ :=
  exists_extension_of_injective S.subtype Subtype.val_injective χ

/-- Choose the extension whose existence was proved above. -/
def extension {A : Type*} [CommGroup A] (S : Subgroup A) (χ : S →* kˣ) : A →* kˣ :=
  Classical.choose (exists_extension S χ)

@[simp] theorem extension_comp_subtype {A : Type*} [CommGroup A]
    (S : Subgroup A) (χ : S →* kˣ) : (extension S χ).comp S.subtype = χ :=
  Classical.choose_spec (exists_extension S χ)

@[simp] theorem extension_apply {A : Type*} [CommGroup A]
    (S : Subgroup A) (χ : S →* kˣ) (s : S) : extension S χ s = χ s :=
  congrArg (fun f : S →* kˣ => f s) (extension_comp_subtype S χ)

end Kourovka2135.AlgebraicallyClosedCharacterExtension

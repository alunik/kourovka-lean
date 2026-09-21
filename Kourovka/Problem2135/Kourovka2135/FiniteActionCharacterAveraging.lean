import Kourovka2135.CoprimeCharacterAveraging
import Kourovka2135.AlgebraicallyClosedCharacterExtension

/-! Average a character over an actual finite group action on an abelian
p-group. The finite orbit norm is invariant by right reindexing, and inverse
coprime powering preserves its original values on every pointwise fixed
subgroup. The final character extension uses the actual checked Baer map.
No cyclic-action, finite coefficient-group, or cohomology assumption is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.FiniteActionCharacterAveraging

open scoped BigOperators
attribute [local instance] Fintype.ofFinite

variable {A C : Type*} [CommGroup A] [Group C] [Finite C]
variable (φ : C →* MulAut A)

/-- The actual product over the entire finite acting group. -/
def norm : A →* A where
  toFun a := ∏ c : C, φ c a
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, Finset.prod_mul_distrib]

@[simp] theorem norm_apply (a : A) : norm φ a = ∏ c : C, φ c a := rfl

/-- Right reindexing proves invariance under every actual group element. -/
theorem norm_invariant (t : C) (a : A) : norm φ (φ t a) = norm φ a := by
  have hstep (c : C) : φ c (φ t a) = φ (c * t) a := by
    rw [map_mul]
    rfl
  change (∏ c : C, φ c (φ t a)) = ∏ c : C, φ c a
  simp only [hstep]
  exact Equiv.prod_comp (Equiv.mulRight t) (fun c : C => φ c a)

/-- Pointwise fixed elements have the actual group-cardinality norm. -/
theorem norm_of_fixed (a : A) (ha : ∀ c : C, φ c a = a) :
    norm φ a = a ^ Nat.card C := by
  simp only [norm_apply, ha, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable {p : ℕ} (hA : IsPGroup p A) (hcard : Nat.Coprime p (Nat.card C))
variable {B : Type*} [Monoid B]

/-- Correct the actual norm by the already constructed inverse power automorphism. -/
def average (χ : A →* B) : A →* B :=
  χ.comp ((CoprimeCharacterAveraging.powerAut (Nat.card C) hA hcard).symm.toMonoidHom.comp
    (norm φ))

/-- The actual averaged character is fixed by the entire finite acting group. -/
theorem average_invariant (χ : A →* B) (t : C) (a : A) :
    average φ hA hcard χ (φ t a) = average φ hA hcard χ a := by
  change χ ((CoprimeCharacterAveraging.powerAut (Nat.card C) hA hcard).symm
    (norm φ (φ t a))) = χ ((CoprimeCharacterAveraging.powerAut (Nat.card C) hA hcard).symm
    (norm φ a))
  rw [norm_invariant]

/-- Averaging retains every original character value on pointwise fixed elements. -/
theorem average_of_fixed (χ : A →* B) (a : A) (ha : ∀ c : C, φ c a = a) :
    average φ hA hcard χ a = χ a := by
  change χ ((CoprimeCharacterAveraging.powerAut (Nat.card C) hA hcard).symm
    (norm φ a)) = χ a
  rw [norm_of_fixed φ a ha]
  exact congrArg χ
    ((CoprimeCharacterAveraging.powerAut (Nat.card C) hA hcard).symm_apply_apply a)

include hA hcard in
/-- Extend an actual unit-valued character from an actual injective pointwise
fixed subgroup and obtain invariance under every element of the finite group. -/
theorem exists_extension
    {k Z : Type*} [Field k] [IsAlgClosed k] [CommGroup Z]
    (i : Z →* A) (hi : Function.Injective i)
    (hfix : ∀ (c : C) (z : Z), φ c (i z) = i z) (χ₀ : Z →* kˣ) :
    ∃ ψ : A →* kˣ, ψ.comp i = χ₀ ∧ ∀ (c : C) (a : A), ψ (φ c a) = ψ a := by
  obtain ⟨χ, hχ⟩ := AlgebraicallyClosedCharacterExtension.exists_extension_of_injective i hi χ₀
  let ψ := average φ hA hcard χ
  refine ⟨ψ, ?_, average_invariant φ hA hcard χ⟩
  apply MonoidHom.ext
  intro z
  change ψ (i z) = χ₀ z
  rw [average_of_fixed φ hA hcard χ (i z) (fun c => hfix c z)]
  exact DFunLike.congr_fun hχ z

end Kourovka2135.FiniteActionCharacterAveraging

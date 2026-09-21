import Kourovka2135.BinaryExteriorCharacter

/-! The actual residue algebra homomorphism of the squarefree coordinate
algebra. It kills the generators and sends every unipotent character to one. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryExteriorAugmentation

open Kourovka2135.BinaryExteriorAlgebra
open Kourovka2135.BinaryExteriorCharacter
open scoped CharTwo IsMulCommutative

variable (k : Type*) [CommRing k] [CharP k 2] (f : ℕ)

/-- The residue map induced by the zero linear map on the generators. -/
def augmentation : Carrier k f →ₐ[k] k :=
  ExteriorAlgebra.lift k ⟨(0 : (Fin f → k) →ₗ[k] k), by intro v; simp⟩

@[simp] theorem augmentation_generator (i : Fin f) :
    augmentation k f (generator k f i) = 0 := by
  simp [augmentation, generator, ExteriorAlgebra.lift_ι_apply]

@[simp] theorem augmentation_basis_empty :
    augmentation k f (basis k f ∅) = 1 := by
  rw [basis_empty, map_one]

theorem augmentation_basis_nonempty (I : Finset (Fin f)) (hI : I.Nonempty) :
    augmentation k f (basis k f I) = 0 := by
  have hb : (∏ i ∈ I, generator k f i) = basis k f I := by
    simpa using prod_smul_generator k f I (fun _ => (1 : k))
  rw [← hb, map_prod]
  obtain ⟨i, hi⟩ := hI
  exact Finset.prod_eq_zero hi (augmentation_generator k f i)

/-- The basis-coordinate description of the residue map. -/
theorem augmentation_basis (I : Finset (Fin f)) :
    augmentation k f (basis k f I) = if I = ∅ then 1 else 0 := by
  by_cases hI : I = ∅
  · subst I
    simp
  · rw [ite_eq_right hI]
    exact augmentation_basis_nonempty k f I (Finset.nonempty_iff_ne_empty.mpr hI)

/-- The residue map extracts the coefficient of the empty subset. -/
theorem augmentation_eq_repr_empty (a : Carrier k f) :
    augmentation k f a = (basis k f).repr a ∅ := by
  have h : (augmentation k f).toLinearMap = (basis k f).coord ∅ := by
    apply (basis k f).ext
    intro I
    simp [augmentation_basis, Module.Basis.coord_apply, Finsupp.single_apply]
  exact LinearMap.congr_fun h a

theorem augmentation_surjective : Function.Surjective (augmentation k f) := by
  intro a
  exact ⟨algebraMap k (Carrier k f) a, (augmentation k f).commutes a⟩

@[simp] theorem augmentation_character (t : k) :
    augmentation k f (character k f t) = 1 := by
  simp [character, map_prod, map_smul]

end Kourovka2135.BinaryExteriorAugmentation

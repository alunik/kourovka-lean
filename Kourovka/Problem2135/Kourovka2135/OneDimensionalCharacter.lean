import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Group.Units.Hom

/-! An actual degree-one representation has an actual unit-valued character
homomorphism. It is constructed as the determinant homomorphism lifted to
units. Scalar endomorphisms in dimension one prove determinant equals trace,
so multiplicativity of the ordinary character is a conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.OneDimensionalCharacter

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- In actual scalar dimension one, determinant and trace agree on every endomorphism. -/
theorem det_eq_trace_of_finrank_eq_one [FiniteDimensional k V]
    (hdim : Module.finrank k V = 1) (T : Module.End k V) :
    LinearMap.det T = LinearMap.trace k V T := by
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim T
  change T = c • (1 : Module.End k V) at hc
  rw [hc]
  simp [hdim]

variable {G : Type*} [Group G] (ρ : Representation k G V)

/-- The actual determinant homomorphism, with its canonical lift to field units. -/
def characterHom : G →* kˣ := (LinearMap.det.comp ρ).toHomUnits

@[simp] theorem characterHom_val (g : G) :
    (characterHom ρ g : k) = LinearMap.det (ρ g) := rfl

variable [FiniteDimensional k V]

/-- In dimension one, the actual unit-valued homomorphism is exactly the ordinary character. -/
theorem characterHom_val_eq_character (hdim : Module.finrank k V = 1) (g : G) :
    (characterHom ρ g : k) = ρ.character g :=
  det_eq_trace_of_finrank_eq_one hdim (ρ g)

/-- If the constructed homomorphism is trivial, the actual ordinary character is constantly one. -/
theorem character_eq_one_of_characterHom_eq_one
    (hdim : Module.finrank k V = 1) (hχ : characterHom ρ = 1) (g : G) :
    ρ.character g = 1 := by
  calc
    ρ.character g = (characterHom ρ g : k) := (characterHom_val_eq_character ρ hdim g).symm
    _ = 1 := by rw [hχ]; rfl

/-- Triviality of the actual unit-valued homomorphism is exactly the constant-one character case. -/
theorem characterHom_eq_one_iff (hdim : Module.finrank k V = 1) :
    characterHom ρ = 1 ↔ ∀ g : G, ρ.character g = 1 := by
  constructor
  · exact fun hχ => character_eq_one_of_characterHom_eq_one ρ hdim hχ
  · intro h
    apply MonoidHom.ext
    intro g
    apply Units.ext
    exact (characterHom_val_eq_character ρ hdim g).trans (h g)

/-- A directly usable unit-character witness is constructed from the actual representation. -/
theorem exists_unit_character (hdim : Module.finrank k V = 1) :
    ∃ χ : G →* kˣ, ∀ g : G, (χ g : k) = ρ.character g :=
  ⟨characterHom ρ, characterHom_val_eq_character ρ hdim⟩

end Kourovka2135.OneDimensionalCharacter

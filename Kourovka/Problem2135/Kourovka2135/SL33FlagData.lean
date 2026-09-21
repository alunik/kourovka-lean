import Kourovka2135.SL33ProjectiveData
import Kourovka2135.SubactionCertificate
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.RepresentationTheory.Basic

/-! The actual action of PSL3(3) on its52 projective point-line flags.
The ambient action is the actual13-point projective action on a point and
a finite set of points. Explicit generator permutations prove that the
listed incidence flags form an invariant subset of that actual action. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SL33FlagData
open SL33ProjectiveData
open scoped Pointwise

local instance : MulAction Q (Fin 13) := MulAction.compHom (Fin 13) permutation

def ambient : Q →* Equiv.Perm (Fin 13 × Finset (Fin 13)) :=
  MulAction.toPermHom Q (Fin 13 × Finset (Fin 13))

def line : Fin 13 → Finset (Fin 13) :=
  ![{0, 1, 5, 9},
    {0, 2, 6, 10},
    {0, 3, 4, 8},
    {0, 7, 11, 12},
    {1, 2, 8, 11},
    {1, 3, 6, 7},
    {1, 4, 10, 12},
    {2, 3, 9, 12},
    {2, 4, 5, 7},
    {3, 5, 10, 11},
    {4, 6, 9, 11},
    {5, 6, 8, 12},
    {7, 8, 9, 10}]

def flag : Fin 52 → Fin 13 × Finset (Fin 13) :=
  ![(0, line 0),
    (1, line 0),
    (5, line 0),
    (9, line 0),
    (0, line 1),
    (2, line 1),
    (6, line 1),
    (10, line 1),
    (0, line 2),
    (3, line 2),
    (4, line 2),
    (8, line 2),
    (0, line 3),
    (7, line 3),
    (11, line 3),
    (12, line 3),
    (1, line 4),
    (2, line 4),
    (8, line 4),
    (11, line 4),
    (1, line 5),
    (3, line 5),
    (6, line 5),
    (7, line 5),
    (1, line 6),
    (4, line 6),
    (10, line 6),
    (12, line 6),
    (2, line 7),
    (3, line 7),
    (9, line 7),
    (12, line 7),
    (2, line 8),
    (4, line 8),
    (5, line 8),
    (7, line 8),
    (3, line 9),
    (5, line 9),
    (10, line 9),
    (11, line 9),
    (4, line 10),
    (6, line 10),
    (9, line 10),
    (11, line 10),
    (5, line 11),
    (6, line 11),
    (8, line 11),
    (12, line 11),
    (7, line 12),
    (8, line 12),
    (9, line 12),
    (10, line 12)]

theorem flag_injective : Function.Injective flag := by decide +kernel

def permA : Equiv.Perm (Fin 52) where
  toFun i := ![4, 5, 6, 7, 0, 1, 2, 3, 8, 10, 9, 11, 12, 13, 14, 15, 17, 16, 18, 19, 32, 33, 34, 35, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 40, 41, 42, 43, 36, 37, 38, 39, 45, 44, 46, 47, 48, 49, 51, 50] i
  invFun i := ![4, 5, 6, 7, 0, 1, 2, 3, 8, 10, 9, 11, 12, 13, 14, 15, 17, 16, 18, 19, 32, 33, 34, 35, 28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 40, 41, 42, 43, 36, 37, 38, 39, 45, 44, 46, 47, 48, 49, 51, 50] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permB : Equiv.Perm (Fin 52) where
  toFun i := ![9, 8, 10, 11, 29, 28, 30, 31, 21, 20, 23, 22, 36, 37, 38, 39, 4, 5, 6, 7, 0, 1, 3, 2, 12, 13, 15, 14, 17, 16, 18, 19, 32, 35, 33, 34, 24, 25, 27, 26, 48, 50, 49, 51, 40, 42, 41, 43, 44, 45, 46, 47] i
  invFun i := ![20, 21, 23, 22, 16, 17, 18, 19, 1, 0, 2, 3, 24, 25, 27, 26, 29, 28, 30, 31, 9, 8, 11, 10, 36, 37, 39, 38, 5, 4, 6, 7, 32, 34, 35, 33, 12, 13, 14, 15, 44, 46, 45, 47, 48, 49, 50, 51, 40, 42, 41, 43] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem a_flag (i : Fin 52) :
    ambient (PSL33GoodSets.q a) (flag i) = flag (permA i) := by
  change (permutation (PSL33GoodSets.q a) (flag i).1,
    (flag i).2.image (permutation (PSL33GoodSets.q a))) = _
  rw [permutation_a]
  revert i
  decide +kernel

theorem b_flag (i : Fin 52) :
    ambient (PSL33GoodSets.q b) (flag i) = flag (permB i) := by
  change (permutation (PSL33GoodSets.q b) (flag i).1,
    (flag i).2.image (permutation (PSL33GoodSets.q b))) = _
  rw [permutation_b]
  revert i
  decide +kernel

theorem generator_certificate (g : Q)
    (hg : g ∈ ({PSL33GoodSets.q a, PSL33GoodSets.q b} : Set Q)) :
    ∃ p : Equiv.Perm (Fin 52), ∀ i, ambient g (flag i) = flag (p i) := by
  rcases (show g = PSL33GoodSets.q a ∨ g = PSL33GoodSets.q b by simpa using hg) with rfl | rfl
  · exact ⟨permA, a_flag⟩
  · exact ⟨permB, b_flag⟩

/-- Genuine all-group action on the actual incidence flags. -/
def permutation : Q →* Equiv.Perm (Fin 52) :=
  SubactionCertificate.hom ambient flag flag_injective
    {PSL33GoodSets.q a, PSL33GoodSets.q b} generating_projective generator_certificate

theorem permutation_a : permutation (PSL33GoodSets.q a) = permA :=
  SubactionCertificate.hom_eq_of_spec ambient flag flag_injective _
    generating_projective generator_certificate _ permA a_flag

theorem permutation_b : permutation (PSL33GoodSets.q b) = permB :=
  SubactionCertificate.hom_eq_of_spec ambient flag flag_injective _
    generating_projective generator_certificate _ permB b_flag

/-- Column permutation representation of the actual52-flag action. -/
def representation (k : Type*) [CommRing k] : Representation k Q (Fin 52 → k) where
  toFun g := LinearMap.pi fun i => LinearMap.proj ((permutation g).symm i)
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change v ((permutation 1).symm i) = v i
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext i
    change v ((permutation (g * h)).symm i) =
      v ((permutation h).symm ((permutation g).symm i))
    rw [map_mul]
    rfl

@[simp] theorem representation_a (k : Type*) [CommRing k] (v : Fin 52 → k) (i : Fin 52) :
    representation k (PSL33GoodSets.q a) v i = v (permA.symm i) := by
  change v ((permutation (PSL33GoodSets.q a)).symm i) = _
  rw [permutation_a]

@[simp] theorem representation_b (k : Type*) [CommRing k] (v : Fin 52 → k) (i : Fin 52) :
    representation k (PSL33GoodSets.q b) v i = v (permB.symm i) := by
  change v ((permutation (PSL33GoodSets.q b)).symm i) = _
  rw [permutation_b]

end Kourovka2135.SL33FlagData

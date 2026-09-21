import Kourovka2135.SuzukiTensorHighest
import Kourovka2135.SuzukiOvoidAugmentation
import Kourovka2135.FinitePermutationOrbitMap

/-! A concrete equivalence between the full natural Frobenius tensor and
the ovoid augmentation module. The map is induced from the Borel-fixed
highest tensor. Nonvanishing follows from its actual Weyl translate;
irreducibility of augmentation and equal dimensions give bijectivity. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorAugmentation

open SuzukiGeometry
open scoped MonoidAlgebra

variable (k : Type) [Field k] [CharP k 2] (m : ℕ) (σ : K m →+* k)

local notation "ρ" => SuzukiTensorHighest.representation k m σ
local notation "A" => SuzukiOvoidAugmentation.representation k m

theorem highest_fixed (g : G m) (hg : g • infinityOvoid m = infinityOvoid m) :
    ρ g (SuzukiTensorHighest.highest k m) = SuzukiTensorHighest.highest k m :=
  SuzukiTensorHighest.stabilizer_fixes_highest k m σ
    ⟨g, MulAction.mem_stabilizer_iff.mpr hg⟩

def orbitFunction : Ovoid m → SuzukiTensorHighest.FullSpace k m :=
  FinitePermutationOrbitMap.orbitFunction ρ (infinityOvoid m)
    (SuzukiTensorHighest.highest k m) (SuzukiOvoidAugmentation.transitive m)

theorem orbitFunction_orbit (g : G m) :
    orbitFunction k m σ (g • infinityOvoid m) = ρ g (SuzukiTensorHighest.highest k m) :=
  FinitePermutationOrbitMap.orbitFunction_orbit ρ (infinityOvoid m)
    (SuzukiTensorHighest.highest k m) (SuzukiOvoidAugmentation.transitive m)
    (highest_fixed k m σ) g

theorem orbitFunction_base :
    orbitFunction k m σ (infinityOvoid m) = SuzukiTensorHighest.highest k m :=
  FinitePermutationOrbitMap.orbitFunction_base ρ (infinityOvoid m)
    (SuzukiTensorHighest.highest k m) (SuzukiOvoidAugmentation.transitive m)
    (highest_fixed k m σ)

theorem orbitFunction_equivariant (g : G m) (x : Ovoid m) :
    orbitFunction k m σ (g • x) = ρ g (orbitFunction k m σ x) :=
  FinitePermutationOrbitMap.orbitFunction_equivariant ρ (infinityOvoid m)
    (SuzukiTensorHighest.highest k m) (SuzukiOvoidAugmentation.transitive m)
    (highest_fixed k m σ) g x

theorem orbitFunction_nonconstant :
    orbitFunction k m σ (SuzukiTensorNatural.weyl m • infinityOvoid m) ≠
      orbitFunction k m σ (infinityOvoid m) := by
  rw [orbitFunction_orbit, orbitFunction_base]
  exact SuzukiTensorHighest.weyl_moves_highest k m σ

/-- The actual map from augmentation to the full tensor, with both actions retained. -/
def augmentationEquiv : Representation.Equiv A ρ := by
  let : (FinitePermutationAugmentation.action k (SuzukiGeometry.G m)
    (Ovoid m)).IsIrreducible := SuzukiOvoidAugmentation.isIrreducible k m
  exact FinitePermutationOrbitMap.augmentationEquiv ρ (orbitFunction k m σ)
    (orbitFunction_equivariant k m σ)
    ((SuzukiOvoidAugmentation.finrank_augmentation k m).trans
      (SuzukiTensorHighest.finrank_full k m).symm)
    (infinityOvoid m) (SuzukiTensorNatural.weyl m • infinityOvoid m)
    (orbitFunction_nonconstant k m σ)

set_option backward.isDefEq.respectTransparency false in
/-- Irreducibility of the genuine full tensor over every binary coefficient field
containing the finite parameter field. -/
theorem isIrreducible : Representation.IsIrreducible ρ := by
  let : (FinitePermutationAugmentation.action k (SuzukiGeometry.G m)
    (Ovoid m)).IsIrreducible := SuzukiOvoidAugmentation.isIrreducible k m
  let a := (augmentationEquiv k m σ).symm
  let f : (Representation.asModule ρ) →ₗ[k[G m]] (Representation.asModule A) :=
    Representation.IntertwiningMap.equivLinearMapAsModule ρ A a.toIntertwiningMap
  let e : (Representation.asModule ρ) ≃ₗ[k[G m]] (Representation.asModule A) :=
    LinearEquiv.ofBijective f a.toLinearEquiv.bijective
  let : IsSimpleModule k[G m] (Representation.asModule A) :=
    (Representation.irreducible_iff_isSimpleModule_asModule A).mp
      (SuzukiOvoidAugmentation.isIrreducible k m)
  let : IsSimpleModule k[G m] (Representation.asModule ρ) :=
    IsSimpleModule.congr (N := Representation.asModule A) e
  exact (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr inferInstance

end Kourovka2135.SuzukiTensorAugmentation

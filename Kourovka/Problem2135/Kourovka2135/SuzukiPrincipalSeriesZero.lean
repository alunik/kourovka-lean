import Kourovka2135.SuzukiPrincipalSeries
import Kourovka2135.StabilizerCoinduction
import Kourovka2135.SuzukiOvoidAugmentation

/-! The actual zero-character Suzuki principal series is the ovoid
permutation module. An irreducible image either maps nontrivially to the
scalar trivial representation under summation or lies in the genuine
irreducible augmentation module. There is no extra module-list premise. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiPrincipalSeriesZero

open SuzukiGeometry SuzukiPrincipalSeries SuzukiPrincipalSeriesBorel

variable (m : ℕ) {k : Type} [Field k] (σ : K m →+* k)

/-- Actual stabilizer coinduction, with the inverse orbit-map convention
dictated by right translation. -/
def permutationEquiv : (representation m σ 0).Equiv
    (FinitePermutationAugmentation.representation k (G m) (Ovoid m)) := by
  apply Representation.Equiv.symm
  change (FinitePermutationAugmentation.representation k (G m) (Ovoid m)).Equiv
    (CoinducedLinearCharacter.induced (borel m) (character m σ 0))
  have hc : character m σ 0 = (1 : borel m →* kˣ) := by
    ext b
    simp [character]
  rw [hc, borel_eq_stabilizer_infinity]
  exact StabilizerCoinduction.equiv k (G m) (Ovoid m) (infinityOvoid m)
    (SuzukiOvoidAugmentation.transitive m)

def augmentationIntertwiner :
    (FinitePermutationAugmentation.representation k (G m) (Ovoid m)).IntertwiningMap
      (Representation.trivial k (G m) k) :=
  (FinitePermutationAugmentation.augmentation k (Ovoid m)).intertwiningMap_of_isIntertwiningMap
    _ _ (FinitePermutationAugmentation.augmentation_action k (G m) (Ovoid m))

variable {V : Type} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (G m) V) [ρ.IsIrreducible]

/-- Exact scalar equivalence from an actual nonzero scalar intertwiner. -/
def scalarEquiv (l : ρ.IntertwiningMap (Representation.trivial k (G m) k)) (hl : l ≠ 0) :
    ρ.Equiv (Representation.trivial k (G m) k) := by
  have hi := (Representation.IsIrreducible.injective_or_eq_zero l).resolve_right hl
  have hl' : l.toLinearMap ≠ 0 := fun h => hl (Representation.IntertwiningMap.ext h)
  have hs := (LinearMap.surjective_or_eq_zero l.toLinearMap).resolve_right hl'
  exact l.ofBijective ⟨hi, hs⟩

variable [CharP k 2]

/-- The trivial and genuine ovoid-augmentation modules exhaust the
irreducible sources at zero character. -/
theorem scalar_or_augmentation
    (j : ρ.IntertwiningMap (representation m σ 0)) (hj : j ≠ 0) :
    Nonempty (ρ.Equiv (Representation.trivial k (G m) k)) ∨
      Nonempty (ρ.Equiv (SuzukiOvoidAugmentation.representation k m)) := by
  classical
  let e := permutationEquiv m σ
  let f := e.toIntertwiningMap.comp j
  have hf : f ≠ 0 := by
    intro he
    apply hj
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    change f v = e.toLinearEquiv 0
    rw [he, map_zero]
    rfl
  let a := (augmentationIntertwiner (k := k) m).comp f
  by_cases ha : a = 0
  · let l : V →ₗ[k] SuzukiOvoidAugmentation.Augmentation k m :=
      f.toLinearMap.codRestrict (FinitePermutationAugmentation.Space k (Ovoid m)) (by
        intro v
        have hv := congrArg (fun t : ρ.IntertwiningMap
          (Representation.trivial k (G m) k) => t v) ha
        exact hv)
    have hlact (g : G m) (v : V) :
        l (ρ g v) = SuzukiOvoidAugmentation.representation k m g (l v) := by
      apply Subtype.ext
      change f (ρ g v) =
        FinitePermutationAugmentation.representation k (G m) (Ovoid m) g (f v)
      exact Representation.IntertwiningMap.isIntertwining ρ
        (FinitePermutationAugmentation.representation k (G m) (Ovoid m)) f g v
    let j' : ρ.IntertwiningMap (SuzukiOvoidAugmentation.representation k m) :=
      l.intertwiningMap_of_isIntertwiningMap _ _ hlact
    have hj' : j' ≠ 0 := by
      intro he
      apply hf
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun t : ρ.IntertwiningMap
        (SuzukiOvoidAugmentation.representation k m) => (t v).val) he
      exact hv
    let : (SuzukiOvoidAugmentation.representation k m).IsIrreducible :=
      SuzukiOvoidAugmentation.isIrreducible k m
    exact Or.inr ⟨j'.ofBijective
      ((Representation.IsIrreducible.bijective_or_eq_zero j').resolve_right hj')⟩
  · exact Or.inl ⟨scalarEquiv m ρ a ha⟩

end Kourovka2135.SuzukiPrincipalSeriesZero

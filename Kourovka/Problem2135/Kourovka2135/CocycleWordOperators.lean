import Kourovka2135.CocycleGeneratorEvaluation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Replace the actual generator operators by checked coordinate operators
before evaluating the finite cocycle constraints. The bridge uses equality
of genuine operators; the group relations remain separate proof obligations. -/

set_option autoImplicit false
noncomputable section
universe u v w x

namespace Kourovka2135.CocycleWordOperators

variable {k : Type u} {V : Type v} {I : Type w} {J : Type x}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The same left-cocycle derivative, expressed using coordinate operators. -/
def derivative (ops : I → Module.End k V) : List I → (I → V) →ₗ[k] V
  | [] => 0
  | i :: word => (ops i).comp (derivative ops word) + LinearMap.proj i

def constraints (ops : I → Module.End k V) (words : J → List I) :
    (I → V) →ₗ[k] (J → V) := LinearMap.pi (fun j => derivative ops (words j))

/-- Verified equality on the generator operators transfers every positive-word derivative. -/
theorem derivative_eq {G : Type u} [Group G] (ρ : Representation k G V)
    (gens : I → G) (ops : I → Module.End k V)
    (hops : ∀ i, ρ (gens i) = ops i) (word : List I) :
    CocycleGeneratorEvaluation.wordDerivative ρ gens word = derivative ops word := by
  induction word with
  | nil => rfl
  | cons i word ih =>
      change (ρ (gens i)).comp _ + _ = (ops i).comp _ + _
      rw [hops i, ih]

theorem constraints_eq {G : Type u} [Group G] (ρ : Representation k G V)
    (gens : I → G) (ops : I → Module.End k V)
    (hops : ∀ i, ρ (gens i) = ops i) (words : J → List I) :
    CocycleGeneratorEvaluation.constraints ρ gens words = constraints ops words := by
  ext f j
  exact congrArg (fun D : (I → V) →ₗ[k] V => D f)
    (derivative_eq ρ gens ops hops (words j))

/-- Flatten a tuple of coordinate vectors, without choosing a basis noncomputably. -/
def flatten {n : Type*} : (I → n → k) ≃ₗ[k] (I × n → k) where
  toFun f p := f p.1 p.2
  invFun f i j := f (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Kourovka2135.CocycleWordOperators

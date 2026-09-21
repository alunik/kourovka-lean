import Kourovka2135.BinaryFieldSixteen
import Kourovka2135.RepresentationEmbeddingModel
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.CharP.Frobenius

/-! Four actual coefficient embeddings into any algebraically closed field
of characteristic two. A checked Frobenius orbit of a character value then
separates the four scalar-extended representations. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryFieldSixteenEmbedding
open BinaryFieldSixteen

variable (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]

/-- An actual embedding of the concrete finite field into the target field. -/
def baseEmbedding : K →+* L := by
  letI : Algebra (ZMod 2) L := ZMod.algebra L 2
  exact (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := L)).toRingHom

/-- Precompose the same embedding with the four source Frobenius maps. -/
def embedding (i : Fin 4) : K →+* L :=
  (baseEmbedding L).comp (iterateFrobenius K 2 i.val)

theorem embedding_apply (i : Fin 4) (x : K) :
    embedding L i x = baseEmbedding L (x ^ (2 ^ i.val)) := rfl

/-- An injective four-term orbit stays injective after the actual embedding. -/
theorem orbit_injective (x : K)
    (hx : Function.Injective (fun i : Fin 4 => x ^ (2 ^ i.val))) :
    Function.Injective (fun i : Fin 4 => embedding L i x) := by
  intro i j hij
  exact hx ((baseEmbedding L).injective hij)

theorem embedding_injective : Function.Injective (embedding L) := by
  intro i j hij
  apply orbit_injective L alpha alpha_frobenius_distinct
  exact congrArg (fun f : K →+* L => f alpha) hij

variable {G V : Type} [Group G] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Distinct character values, rather than just distinct embeddings,
certify that the four actual scalar extensions are inequivalent. -/
theorem models_pairwise_not_equiv (ρ : Representation K G V) (g : G)
    (htrace : Function.Injective (fun i : Fin 4 => (ρ.character g) ^ (2 ^ i.val))) :
    Pairwise fun i j => ¬ Nonempty
      ((RepresentationEmbeddingModel.model (embedding L i) ρ).Equiv
        (RepresentationEmbeddingModel.model (embedding L j) ρ)) := by
  intro i j hij
  apply RepresentationEmbeddingModel.not_equiv_of_character_ne
    (embedding L i) (embedding L j) ρ g
  exact fun he => hij (orbit_injective L (ρ.character g) htrace he)

end Kourovka2135.BinaryFieldSixteenEmbedding

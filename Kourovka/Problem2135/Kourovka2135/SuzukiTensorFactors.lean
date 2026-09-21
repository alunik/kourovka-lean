import Kourovka2135.SuzukiTensorAugmentation
import Kourovka2135.TensorFactorIrreducible

/-! Every partial natural Frobenius tensor is irreducible. The full tensor
is explicitly reindexed as the tensor of a chosen subset and its complement,
and irreducibility is reflected to the nonzero factors. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorFactors

open SuzukiTorusMovingRank SuzukiTensorNatural
open scoped TensorProduct PiTensorProduct MonoidAlgebra

variable (k : Type) [Field k] [CharP k 2] (m : ℕ)
variable (I : Finset (Fin (2 * m + 1)))

def complement : Finset (Fin (2 * m + 1)) := Finset.univ \ I

def indexEquiv : I ⊕ complement m I ≃ SuzukiTensorHighest.fullIndices m where
  toFun z := ⟨Sum.elim Subtype.val Subtype.val z, Finset.mem_univ _⟩
  invFun i := if h : i.val ∈ I then Sum.inl ⟨i.val, h⟩
    else Sum.inr ⟨i.val, by simp [complement, h]⟩
  left_inv z := by
    rcases z with i | i
    · simp [i.property]
    · have hi : i.val ∉ I := (Finset.mem_sdiff.mp i.property).2
      simp [hi]
  right_inv i := by
    dsimp
    split_ifs <;> rfl

def splitLinearEquiv :
    TensorSpace k m I ⊗[k] TensorSpace k m (complement m I) ≃ₗ[k]
      SuzukiTensorHighest.FullSpace k m :=
  (PiTensorProduct.tmulEquiv k (Fin 4 → k)).trans
    (PiTensorProduct.reindex k (fun _ : I ⊕ complement m I => Fin 4 → k)
      (indexEquiv m I))

omit [CharP k 2] in
theorem splitLinearEquiv_tprod (a : I → Fin 4 → k)
    (b : complement m I → Fin 4 → k) :
    splitLinearEquiv k m I
      ((PiTensorProduct.tprod k a) ⊗ₜ[k] (PiTensorProduct.tprod k b)) =
      PiTensorProduct.tprod k (fun i => Sum.elim a b ((indexEquiv m I).symm i)) := by
  simp [splitLinearEquiv]

theorem twist_reindexed (σ : K m →+* k) (g : G m)
    (a : I → Fin 4 → k) (b : complement m I → Fin 4 → k)
    (i : SuzukiTensorHighest.fullIndices m) :
    naturalTwist k m σ i.val.val g (Sum.elim a b ((indexEquiv m I).symm i)) =
      Sum.elim (fun j : I => naturalTwist k m σ j.val.val g (a j))
        (fun j : complement m I => naturalTwist k m σ j.val.val g (b j))
        ((indexEquiv m I).symm i) := by
  obtain ⟨z, rfl⟩ := (indexEquiv m I).surjective i
  rw [(indexEquiv m I).symm_apply_apply]
  cases z <;> rfl

theorem split_action_tprod (σ : K m →+* k) (g : G m)
    (a : I → Fin 4 → k) (b : complement m I → Fin 4 → k) :
    splitLinearEquiv k m I
      ((representation k m I σ g (PiTensorProduct.tprod k a)) ⊗ₜ[k]
        (representation k m (complement m I) σ g (PiTensorProduct.tprod k b))) =
      SuzukiTensorHighest.representation k m σ g
        (splitLinearEquiv k m I
          ((PiTensorProduct.tprod k a) ⊗ₜ[k] (PiTensorProduct.tprod k b))) := by
  rw [representation_tprod, representation_tprod,
    splitLinearEquiv_tprod, splitLinearEquiv_tprod]
  change _ = representation k m (SuzukiTensorHighest.fullIndices m) σ g _
  rw [representation_tprod]
  congr 1
  funext i
  exact (twist_reindexed k m I σ g a b i).symm

def splitEquiv (σ : K m →+* k) :
    ((representation k m I σ).tprod (representation k m (complement m I) σ)).Equiv
      (SuzukiTensorHighest.representation k m σ) :=
  Representation.Equiv.mk (splitLinearEquiv k m I) (by
    intro g
    apply TensorProduct.ext'
    intro x y
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c a =>
      induction y using PiTensorProduct.induction_on with
      | smul_tprod d b =>
        change splitLinearEquiv k m I
          ((representation k m I σ g (c • PiTensorProduct.tprod k a)) ⊗ₜ[k]
            (representation k m (complement m I) σ g (d • PiTensorProduct.tprod k b))) =
          SuzukiTensorHighest.representation k m σ g
            (splitLinearEquiv k m I
              ((c • PiTensorProduct.tprod k a) ⊗ₜ[k] (d • PiTensorProduct.tprod k b)))
        simp only [map_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
        rw [split_action_tprod]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz])

omit [CharP k 2] in
theorem tensor_nontrivial : Nontrivial (TensorSpace k m I) :=
  ⟨⟨highest k m I, 0, highest_ne_zero k m I⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- All partial tensors, including the trivial empty tensor and full tensor. -/
theorem isIrreducible (σ : K m →+* k) :
    Representation.IsIrreducible (representation k m I σ) := by
  let : Representation.IsIrreducible (SuzukiTensorHighest.representation k m σ) :=
    SuzukiTensorAugmentation.isIrreducible k m σ
  let := TensorFactorIrreducible.of_equiv (k := k) (G := G m)
      (V := TensorSpace k m I ⊗[k] TensorSpace k m (complement m I))
      (W := SuzukiTensorHighest.FullSpace k m)
      ((representation k m I σ).tprod (representation k m (complement m I) σ))
      (SuzukiTensorHighest.representation k m σ) (splitEquiv k m I σ)
  let : Nontrivial (TensorSpace k m I) := tensor_nontrivial k m I
  let : Nontrivial (TensorSpace k m (complement m I)) := tensor_nontrivial k m (complement m I)
  exact TensorFactorIrreducible.left (representation k m I σ)
    (representation k m (complement m I) σ)

end Kourovka2135.SuzukiTensorFactors

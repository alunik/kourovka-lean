import Kourovka2135.BinaryTensorSocle
import Kourovka2135.BinaryTensorUnipotentSpan
import Kourovka2135.BinaryTensorSLTwoWeyl
import Mathlib.RepresentationTheory.Irreducible

/-! Simplicity of the actual binary Frobenius tensor modules for SL2.

Upper-unipotent stability gives squarefree generator stability. Every
nonzero stable space therefore contains the top monomial; the genuine Weyl
matrix sends top to one, from which generator multiplication gives the
entire basis. No representation classification theorem is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorSLTwoSimplicity

open scoped IsMulCommutative

variable (k : Type*) [Field k] [CharP k 2] {f : ℕ} (I : Finset (Fin f))

omit [CharP k 2] in
theorem global_basis_top :
    BinaryTensorSubsetBasis.basis k I (BinaryTensorSubsetBasis.topIndex I) =
      BinaryTensorCoefficient.basis k I Finset.univ := by
  rw [BinaryTensorSubsetBasis.basis_apply]
  congr 1
  ext i
  simp [BinaryTensorSubsetBasis.topIndex]

variable {F : Type*} [Field F] [Fintype F] (σ : F →+* k)
variable (hcard : Fintype.card F = 2 ^ f)

omit [Fintype F] in
theorem unipotent_top (t : F) :
    BinaryTensorSLTwo.representation k σ I (SLTwo.uni t)
        (BinaryTensorCoefficient.basis k I Finset.univ) =
      BinaryTensorCoefficient.basis k I Finset.univ := by
  rw [BinaryTensorSLTwo.representation_uni, BinaryTensorCoefficient.smul_eq,
    BinaryTensorSLTwo.projection_character]
  apply Finset.prod_induction
    (fun i : I => 1 + σ t ^ 2 ^ i.val.val • BinaryTensorCoefficient.generator k I i)
    (fun a => a * BinaryTensorCoefficient.basis k I Finset.univ =
      BinaryTensorCoefficient.basis k I Finset.univ)
  · intro a b ha hb
    rw [mul_assoc, hb, ha]
  · exact one_mul _
  · intro i _
    rw [add_mul, one_mul, smul_mul_assoc, BinaryTensorSocle.generator_mul_top,
      smul_zero, add_zero]

include hcard

/-- The actual upper-unipotent fixed vectors are exactly the top monomial line. -/
theorem unipotent_fixed_iff_top (v : BinaryTensorCoefficient.Carrier k I) :
    (∀ t : F, BinaryTensorSLTwo.representation k σ I (SLTwo.uni t) v = v) ↔
      ∃ a : k, v = a • BinaryTensorCoefficient.basis k I Finset.univ := by
  constructor
  · intro hv
    apply (BinaryTensorSocle.generator_mul_eq_zero_iff k I v).mp
    exact BinaryTensorUnipotentSpan.generator_mul_eq_zero_of_unipotent_fixed
      k I σ hcard v hv
  · rintro ⟨a, rfl⟩ t
    rw [map_smul, unipotent_top]

/-- Every nonzero subspace stable under the actual SL2 action is the whole space. -/
theorem eq_top_of_stable (W : Submodule k (BinaryTensorCoefficient.Carrier k I))
    (hW : ∃ v ∈ W, v ≠ 0)
    (hstable : ∀ (g : SLTwo.SL2 F) (v : BinaryTensorCoefficient.Carrier k I),
      v ∈ W → BinaryTensorSLTwo.representation k σ I g v ∈ W) : W = ⊤ := by
  classical
  have hgen := BinaryTensorUnipotentSpan.generator_mul_mem k I σ hcard W
    (fun t v hv => hstable (SLTwo.uni t) v hv)
  have htop := BinaryTensorSocle.top_mem_of_generator_stable k I W hW hgen
  have htop' : BinaryTensorSubsetBasis.basis k I
      (BinaryTensorSubsetBasis.topIndex I) ∈ W := by
    rwa [global_basis_top]
  have hone := hstable (SLTwo.weyl F) _ htop'
  rw [BinaryTensorSLTwo.representation_weyl_top,
    BinaryTensorSubsetBasis.basis_empty] at hone
  have hb (J : Finset I) : BinaryTensorCoefficient.basis k I J ∈ W := by
    induction J using Finset.induction_on with
    | empty => simpa only [BinaryTensorCoefficient.basis_empty] using hone
    | @insert i J hi ih =>
        have h := hgen i _ ih
        rwa [BinaryTensorCoefficient.generator_mul_basis, ite_eq_right hi] at h
  apply le_antisymm le_top
  intro v _
  rw [← (BinaryTensorCoefficient.basis k I).sum_repr v]
  exact W.sum_mem (fun J _ => W.smul_mem _ (hb J))

/-- The concrete tensor coefficient representation is irreducible over every
characteristic-two field containing the finite parameter field. -/
theorem isIrreducible : (BinaryTensorSLTwo.representation k σ I).IsIrreducible := by
  let ρ := BinaryTensorSLTwo.representation k σ I
  have hbot : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    have hone : (1 : BinaryTensorCoefficient.Carrier k I) ∈
        (⊥ : Subrepresentation ρ).toSubmodule := by
      rw [h]
      trivial
    exact one_ne_zero hone
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hex : ∃ v ∈ W.toSubmodule, v ≠ 0 := by
    by_contra h
    apply hW
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    by_contra hne
    exact h ⟨v, hv, hne⟩
  apply Subrepresentation.toSubmodule_injective
  exact eq_top_of_stable k I σ hcard W.toSubmodule hex
    (fun g _ hv => W.apply_mem_toSubmodule g hv)

end Kourovka2135.BinaryTensorSLTwoSimplicity

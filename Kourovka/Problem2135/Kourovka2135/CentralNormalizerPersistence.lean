import Kourovka2135.PersistentCentralTransfer
import Kourovka2135.NormalizerCoprimeKernelLift

/-! Persistent odd commutators from a normalizer in a central extension.

The quotient value of d is persistent. Centrality therefore makes the actual
commutator [d,x⁻¹dx] persistent, even though d itself need not be a word value.
If d normalizes P and x lies in P, this commutator lies in P. A nontrivial
quotient commutator and a coprime order for P give a nonidentity coprime
persistent value. No matrix, generation, solubility, or cover-classification
premise is implicit in these generic statements.
-/

set_option autoImplicit false

namespace Kourovka2135.CentralNormalizerPersistence

universe u v
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

/-- The second commutator remains inside a subgroup normalized by d.
No commutativity of P is required. -/
theorem conjugate_commutator_mem (P : Subgroup G) (d x : G)
    (hd : d ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ P) :
    paperCommutator d (x⁻¹ * d * x) ∈ P := by
  have hmem (y : G) (hy : y ∈ P) : paperCommutator d y ∈ P := by
    apply P.mul_mem ?_ hy
    exact (Subgroup.mem_normalizer_iff''.mp hd y⁻¹).mp (P.inv_mem hy)
  have heq : paperCommutator d (x⁻¹ * d * x) =
      paperCommutator d (paperCommutator d x) := by
    unfold paperCommutator
    group
  rw [heq]
  exact hmem _ (hmem x hx)

/-- Only persistence of the quotient value is needed for the actual commutator. -/
theorem conjugate_commutator_mem_values
    (f : G →* Q) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (d x : G)
    (hd : ∀ w : OuterWord, f d ∈ w.values Q) (w : OuterWord) :
    paperCommutator d (x⁻¹ * d * x) ∈ w.values G := by
  apply OuterWord.commutator_mem_values_of_central_surjection f hf hcentral
    (B := {y : Q | ∀ v : OuterWord, y ∈ v.values Q})
    (fun v _ hy => hy v) hd ?_ w
  intro v
  simpa only [map_mul, map_inv] using v.conj_mem_values (hd v) (f x)

/-- A concrete nonidentity persistent commutator has order prime to p.
Finiteness is required only for the subgroup supplying the order bound. -/
theorem conjugate_commutator_properties
    (f : G →* Q) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center G) (P : Subgroup G) [Finite P]
    (p : ℕ) (hcop : Nat.Coprime p (Nat.card P)) (d x : G)
    (hdnorm : d ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ P)
    (hd : ∀ w : OuterWord, f d ∈ w.values Q)
    (hne : paperCommutator (f d) ((f x)⁻¹ * f d * f x) ≠ 1) :
    paperCommutator d (x⁻¹ * d * x) ∈ P ∧
      paperCommutator d (x⁻¹ * d * x) ≠ 1 ∧
      Nat.Coprime p (orderOf (paperCommutator d (x⁻¹ * d * x))) ∧
      ∀ w : OuterWord, paperCommutator d (x⁻¹ * d * x) ∈ w.values G := by
  have hz := conjugate_commutator_mem P d x hdnorm hx
  refine ⟨hz, ?_, Nat.Coprime.of_dvd_right (P.orderOf_dvd_natCard hz) hcop,
    conjugate_commutator_mem_values f hf hcentral d x hd⟩
  intro heq
  apply hne
  have hmap := congrArg f heq
  simpa only [paperCommutator, map_mul, map_inv, map_one] using hmap

section Finite

variable [Finite G] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- Across a central p-kernel, every chosen lift of a normalizing image
already normalizes the given q-subgroup, q≠p. -/
theorem mem_normalizer_of_image
    (f : G →* Q) (hker : IsPGroup p f.ker)
    (hcentral : f.ker ≤ Subgroup.center G)
    (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p)
    (d : G) (hd : f d ∈ Subgroup.normalizer (P.map f : Set Q)) :
    d ∈ Subgroup.normalizer (P : Set G) := by
  obtain ⟨n, hn, hnd⟩ :=
    NormalizerCoprimeKernelLift.exists_kernel_mul_mem_normalizer f hker P hP hne d hd
  have hnNorm : n ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.center_le_normalizer _ (hcentral hn)
  simpa only [inv_mul_cancel_left] using
    (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).inv_mem hnNorm) hnd

/-- The normalizer premise and the coprime order are both derived from the
actual central p-kernel and q-subgroup. -/
theorem conjugate_commutator_properties_of_image_normalizer
    (f : G →* Q) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (hcentral : f.ker ≤ Subgroup.center G)
    (P : Subgroup G) (hP : IsPGroup q P) (hqp : q ≠ p)
    (d x : G) (hdnorm : f d ∈ Subgroup.normalizer (P.map f : Set Q))
    (hx : x ∈ P) (hd : ∀ w : OuterWord, f d ∈ w.values Q)
    (hne : paperCommutator (f d) ((f x)⁻¹ * f d * f x) ≠ 1) :
    paperCommutator d (x⁻¹ * d * x) ∈ P ∧
      paperCommutator d (x⁻¹ * d * x) ≠ 1 ∧
      Nat.Coprime p (orderOf (paperCommutator d (x⁻¹ * d * x))) ∧
      ∀ w : OuterWord, paperCommutator d (x⁻¹ * d * x) ∈ w.values G := by
  have hnorm := mem_normalizer_of_image f hker hcentral P hP hqp d hdnorm
  have hz := conjugate_commutator_mem P d x hnorm hx
  have hcop : Nat.Coprime p (orderOf (paperCommutator d (x⁻¹ * d * x))) := by
    have hc := hP.orderOf_coprime
      ((Nat.coprime_primes (Fact.out : q.Prime) (Fact.out : p.Prime)).mpr hqp)
      (⟨paperCommutator d (x⁻¹ * d * x), hz⟩ : P)
    have hord : orderOf (⟨paperCommutator d (x⁻¹ * d * x), hz⟩ : P) =
        orderOf (paperCommutator d (x⁻¹ * d * x)) :=
      (orderOf_injective P.subtype P.subtype_injective _).symm
    rw [hord] at hc
    exact hc.symm
  refine ⟨hz, ?_, hcop, conjugate_commutator_mem_values f hf hcentral d x hd⟩
  intro heq
  apply hne
  have hmap := congrArg f heq
  simpa only [paperCommutator, map_mul, map_inv, map_one] using hmap

end Finite

end Kourovka2135.CentralNormalizerPersistence

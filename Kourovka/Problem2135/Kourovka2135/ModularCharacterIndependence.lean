import Kourovka2135.SimpleModuleTraceIndependence
import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.MonoidAlgebra.Module

/-! Independence of actual ordinary field-valued characters in arbitrary characteristic.

The coefficient field is algebraically closed, the actual representations are
finite dimensional and irreducible, and the finite family has distinct
isomorphism types. No invertibility of the group order, Maschke theorem,
Brauer character, or classification premise occurs in the independence result.
The final finite-cover helper records its character-cover premise explicitly;
the prime-part trace lemma supplies it from actual group conjugacy data.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ModularCharacterIndependence

open scoped MonoidAlgebra

variable {k G ι : Type*} [Field k] [IsAlgClosed k] [Monoid G] [Fintype ι]
variable {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable [∀ i, Module.Finite k (V i)]
variable (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
variable (hneq : Pairwise fun i j => ¬ Nonempty ((ρ i).Equiv (ρ j)))

include hneq

omit [IsAlgClosed k] [Fintype ι] [∀ i, Module.Finite k (V i)]
  [∀ i, (ρ i).IsIrreducible] in
/-- Pairwise distinct representation types remain distinct as actual
modules over the group algebra. -/
theorem asModule_pairwise_nonisomorphic :
    Pairwise fun i j => ¬ Nonempty ((ρ i).asModule ≃ₗ[k[G]] (ρ j).asModule) := by
  intro i j hij he
  obtain ⟨e⟩ := he
  let f : (ρ i).IntertwiningMap (ρ j) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ i) (ρ j)).symm e.toLinearMap
  have hf : Function.Bijective f := e.bijective
  exact hneq hij ⟨f.ofBijective hf⟩

omit hneq

omit [IsAlgClosed k] [Fintype ι] [∀ i, Module.Finite k (V i)]
  [∀ i, (ρ i).IsIrreducible] in
/-- The module trace on the actual group-algebra basis is the usual character. -/
theorem traceFunctional_single_one (i : ι) (g : G) :
    SimpleModuleTraceIndependence.traceFunctional (k := k) (R := k[G])
      (fun j => (ρ j).asModule) i (MonoidAlgebra.single g 1) = (ρ i).character g := by
  change LinearMap.trace k (V i) ((ρ i).asAlgebraHom (MonoidAlgebra.single g 1)) = _
  rw [Representation.asAlgebraHom_single_one]
  rfl

include hneq

/-- Distinct finite-dimensional simple representations have linearly
independent ordinary k-valued characters, including modular characteristic. -/
theorem linearIndependent_character :
    LinearIndependent k (fun i => (ρ i).character) := by
  have hs : Submodule.span k (Set.range (fun g : G => MonoidAlgebra.single g (1 : k))) = ⊤ := by
    have he : (fun g : G => MonoidAlgebra.single g (1 : k)) =
        (MonoidAlgebra.basis G k : G → k[G]) := by
      funext g
      exact (MonoidAlgebra.basis_apply k g).symm
    rw [he]
    exact (MonoidAlgebra.basis G k).span_eq
  have h := SimpleModuleTraceIndependence.linearIndependent_trace_on_span
    (k := k) (R := k[G]) (fun i => (ρ i).asModule)
    (asModule_pairwise_nonisomorphic ρ hneq)
    (fun g : G => MonoidAlgebra.single g (1 : k)) hs
  simpa only [traceFunctional_single_one] using h

/-- A finite list on which the characters take all their simultaneous values
bounds the number of distinct simple types. This structural helper exposes
the cover condition; it is not an assumed modular class-count theorem. -/
theorem card_le_of_character_cover
    {J : Type*} [Fintype J] (c : J → G)
    (hcover : ∀ g : G, ∃ j : J, ∀ i, (ρ i).character g = (ρ i).character (c j)) :
    Fintype.card ι ≤ Fintype.card J := by
  classical
  have hi : LinearIndependent k (fun i => fun j => (ρ i).character (c j)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    apply Fintype.linearIndependent_iff.mp (linearIndependent_character ρ hneq) a
    funext g
    obtain ⟨j, hj⟩ := hcover g
    have h := congrFun ha j
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, hj] using h
  simpa only [Module.finrank_fintype_fun_eq_card] using hi.fintype_card_le_finrank

end Kourovka2135.ModularCharacterIndependence

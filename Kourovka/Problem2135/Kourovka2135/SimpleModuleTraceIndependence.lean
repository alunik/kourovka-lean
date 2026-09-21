import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Simultaneous density and trace independence for a finite family of simple modules.

The algebra itself need not be semisimple. Only the actual finite product of
the given simple modules is semisimple. Off-diagonal endomorphism blocks vanish
by Schur, and the diagonal blocks are scalars over the algebraically closed
base field. Jacobson density then realizes every tuple of linear operators.
Rank-one operators of trace one separate the actual trace functionals, in
arbitrary characteristic, without division by module dimensions.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SimpleModuleTraceIndependence

/-- Every nonzero finite-dimensional vector space has an actual operator of
trace one, even when its dimension is zero as an element of the field. -/
theorem exists_trace_one (k V : Type*) [Field k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] [Nontrivial V] :
    ∃ T : Module.End k V, LinearMap.trace k V T = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hv
  exact ⟨f.smulRight v, by rw [LinearMap.trace_smulRight, hf]⟩

section Density

variable {k R ι : Type*} [Field k] [IsAlgClosed k] [Ring R] [Algebra k R]
variable [Fintype ι] (M : ι → Type*)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module R (M i)]
variable [∀ i, IsScalarTower k R (M i)] [∀ i, SMulCommClass R k (M i)]
variable [∀ i, IsSimpleModule R (M i)] [∀ i, Module.Finite k (M i)]
variable (hneq : Pairwise fun i j => ¬ Nonempty (M i ≃ₗ[R] M j))

/-- The actual block of an endomorphism of the finite product. -/
def block (f : Module.End R (∀ i, M i)) (i j : ι) : M j →ₗ[R] M i := by
  classical
  exact (LinearMap.proj i).comp (f.comp (LinearMap.single R M j))

include hneq

omit [Fintype ι] in
/-- Distinct simple types have no off-diagonal endomorphism blocks. -/
theorem block_eq_zero (f : Module.End R (∀ i, M i)) (i j : ι) (hij : i ≠ j) :
    block M f i j = 0 := by
  by_contra h
  exact hneq (Ne.symm hij)
    ⟨LinearEquiv.ofBijective (block M f i j) (LinearMap.bijective_of_ne_zero h)⟩

/-- A product endomorphism acts separately on its actual diagonal blocks. -/
theorem apply_eq_diagonal (f : Module.End R (∀ i, M i)) (v : ∀ i, M i) (i : ι) :
    f v i = block M f i i (v i) := by
  classical
  calc
    f v i = f (∑ j, Pi.single j (v j)) i := by rw [Finset.univ_sum_single]
    _ = ∑ j, block M f i j (v j) := by
      simp only [map_sum, Finset.sum_apply, block, LinearMap.comp_apply,
        LinearMap.proj_apply, LinearMap.single_apply]
    _ = block M f i i (v i) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [block_eq_zero M hneq f i j (Ne.symm hji), LinearMap.zero_apply]
      · simp

omit [∀ i, SMulCommClass R k (M i)] in
/-- Schur identifies each actual diagonal block as one scalar. -/
theorem exists_scalar_apply (f : Module.End R (∀ i, M i)) (i : ι) :
    ∃ c : k, ∀ v : ∀ j, M j, f v i = c • v i := by
  obtain ⟨c, hc⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).surjective (block M f i i)
  refine ⟨c, fun v => ?_⟩
  rw [apply_eq_diagonal M hneq, ← hc, Module.algebraMap_end_apply]

/-- An actual algebra element simultaneously realizes any prescribed tuple of
linear endomorphisms of pairwise nonisomorphic simple modules. -/
theorem exists_action_eq (T : ∀ i, Module.End k (M i)) :
    ∃ r : R, ∀ i (v : M i), r • v = T i v := by
  classical
  let P := ∀ i, M i
  let : Module.Finite (Module.End R P) P :=
    Module.Finite.of_restrictScalars_finite k (Module.End R P) P
  let T' : Module.End (Module.End R P) P :=
    { toFun := fun v i => T i (v i)
      map_add' := fun v w => by ext i; exact (T i).map_add _ _
      map_smul' := fun f v => by
        funext i
        change T i (f v i) = f (fun j => T j (v j)) i
        obtain ⟨c, hc⟩ := exists_scalar_apply (k := k) M hneq f i
        rw [hc, hc]
        exact (T i).map_smul c (v i) }
  obtain ⟨r, hr⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := P) T'
  refine ⟨r, fun i v => ?_⟩
  have h := congrArg (fun z : P => z i) (LinearMap.congr_fun hr (Pi.single i v))
  change r • ((Pi.single i v) i) = T i ((Pi.single i v) i) at h
  simpa only [Pi.single_eq_same] using h

omit hneq

/-- The actual trace of the action of an algebra element. -/
def traceFunctional (i : ι) : R →ₗ[k] k :=
  (LinearMap.trace k (M i)).comp (Algebra.lsmul k k (M i)).toLinearMap

omit [IsAlgClosed k] [Fintype ι] [∀ i, IsSimpleModule R (M i)]
  [∀ i, Module.Finite k (M i)] in
@[simp]
theorem traceFunctional_apply (i : ι) (r : R) :
    traceFunctional (k := k) M i r = LinearMap.trace k (M i) (Algebra.lsmul k k (M i) r) :=
  rfl

include hneq

/-- Actual algebra elements realize arbitrary trace vectors on the family. -/
theorem exists_trace_vector (c : ι → k) :
    ∃ r : R, ∀ i, traceFunctional (k := k) M i r = c i := by
  classical
  have hOne : ∀ i, ∃ T : Module.End k (M i), LinearMap.trace k (M i) T = 1 := by
    intro i
    let : Nontrivial (M i) := IsSimpleModule.nontrivial R (M i)
    exact exists_trace_one k (M i)
  choose T hT using hOne
  obtain ⟨r, hr⟩ := exists_action_eq (k := k) M hneq (fun i => c i • T i)
  refine ⟨r, fun i => ?_⟩
  have heq : Algebra.lsmul k k (M i) r = c i • T i :=
    LinearMap.ext (hr i)
  rw [traceFunctional_apply, heq, map_smul, hT, smul_eq_mul, mul_one]

/-- The actual trace functionals of the simple types are linearly independent. -/
theorem linearIndependent_traceFunctional :
    LinearIndependent k (fun i => (traceFunctional (k := k) M i : R → k)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  obtain ⟨r, hr⟩ := exists_trace_vector (k := k) M hneq (Pi.single i (1 : k))
  have h := congrFun hc r
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, hr, smul_eq_mul] at h
  simpa [Pi.single_apply] using h

/-- Restriction to any actual spanning family retains trace independence. -/
theorem linearIndependent_trace_on_span
    {Ω : Type*} (s : Ω → R) (hs : Submodule.span k (Set.range s) = ⊤) :
    LinearIndependent k (fun i => fun x => traceFunctional (k := k) M i (s x)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply Fintype.linearIndependent_iff.mp (linearIndependent_traceFunctional (k := k) M hneq) c
  let F : R →ₗ[k] k := ∑ i, c i • traceFunctional (k := k) M i
  have hker : Submodule.span k (Set.range s) ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change F (s x) = 0
    have h := congrFun hc x
    simpa only [F, LinearMap.sum_apply, LinearMap.smul_apply,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using h
  have hzero : F = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp (hs ▸ hker))
  funext r
  have h := LinearMap.congr_fun hzero r
  simpa only [F, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.zero_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using h

end Density

end Kourovka2135.SimpleModuleTraceIndependence

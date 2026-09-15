import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Module
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# A common rational flag for a nil ideal

A left ideal consisting of nilpotent elements annihilates every simple module:
if `r • m` were nonzero, simplicity would give `a • (r • m) = m`, contradicting
nilpotence of `a * r`.

Induction on a module's finite length now constructs a common strictly upper
triangular basis. In each extension by a simple quotient, the ideal maps the
whole module into the preceding submodule. Appending any complement basis to
the basis already constructed there therefore preserves strict triangularity.
Finite-dimensional rational modules have finite length over any rational
algebra acting on them, so this applies without any finite-generation
hypothesis on the algebra.

The final theorem packages the common basis as one rational invertible matrix.
It requires only left stability of the nil submodule; a two-sided ideal in
particular satisfies the hypotheses.
-/

open Module
open scoped Matrix

namespace Kourovka.P21_40

/-- Every nil left ideal annihilates every simple module. -/
theorem nilIdeal_smul_eq_zero_of_simple {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [IsSimpleModule R M] (I : Ideal R)
    (hI : ∀ r ∈ I, IsNilpotent r) {r : R} (hr : r ∈ I) (m : M) : r • m = 0 := by
  by_contra hm
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective R hm m
  change a • (r • m) = m at ha
  have hfix : (a * r) • m = m := by simpa only [mul_smul] using ha
  obtain ⟨k, hk⟩ := hI (a * r) (I.mul_mem_left a hr)
  have hpow (j : ℕ) : (a * r) ^ j • m = m := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hfix, ih]
  have hzero : m = 0 := by simpa only [hk, zero_smul] using (hpow k).symm
  exact hm (by rw [hzero, smul_zero])

/-- A nil left ideal admits a common strictly upper triangular rational basis
on any finite-length module that is finite-dimensional over `ℚ`. -/
theorem exists_strict_upper_basis_of_finiteLength {R : Type*} [Ring R] [Algebra ℚ R]
    (I : Ideal R) (hI : ∀ r ∈ I, IsNilpotent r)
    {M : Type*} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∀ [Module ℚ M] [IsScalarTower ℚ R M] [FiniteDimensional ℚ M],
      ∃ (n : ℕ) (b : Basis (Fin n) ℚ M),
        ∀ r ∈ I, ∀ i j, j ≤ i → b.repr (r • b j) i = 0 := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    intro _ _ _
    refine ⟨Module.finrank ℚ M, Module.finBasis ℚ M, ?_⟩
    intro r hr i j hij
    have hzero : r • (Module.finBasis ℚ M) j = 0 := Subsingleton.elim _ _
    simp [hzero]
  | @of_simple_quotient M _ _ N hs hN ih =>
    intro _ _ _
    let p : Submodule ℚ M := N.restrictScalars ℚ
    let : FiniteDimensional ℚ N :=
      Module.Finite.of_injective (N.subtype.restrictScalars ℚ) N.subtype_injective
    obtain ⟨m, b, hb⟩ := ih
    obtain ⟨q, hq⟩ := p.exists_isCompl
    let c := Module.finBasis ℚ q
    let e : (N × q) ≃ₗ[ℚ] M := p.prodEquivOfIsCompl q hq
    let d₀ := (b.prod c).map e
    let d := d₀.reindex finSumFinEquiv
    have hmap (r : R) (hr : r ∈ I) (x : M) : r • x ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      exact nilIdeal_smul_eq_zero_of_simple (M := M ⧸ N) I hI hr (Submodule.Quotient.mk x)
    have hfirst (x : N) : e.symm (x : M) = (x, 0) :=
      p.prodEquivOfIsCompl_symm_apply_left q hq x
    have hvec (j : Fin m) : d₀ (Sum.inl j) = (b j : M) := by
      change e ((b.prod c) (Sum.inl j)) = _
      rw [Basis.prod_apply]
      change (b j : M) + 0 = (b j : M)
      exact add_zero _
    have hcoeff (r : R) (i j : Fin m) :
        d₀.repr (r • d₀ (Sum.inl j)) (Sum.inl i) = b.repr (r • b j) i := by
      rw [hvec]
      change b.repr (e.symm (r • (b j : M))).1 i = _
      change b.repr (e.symm ((r • b j : N) : M)).1 i = _
      rw [hfirst]
    have hzero (x : M) (hx : x ∈ N) (i : Fin (Module.finrank ℚ q)) :
        d₀.repr x (Sum.inr i) = 0 := by
      change c.repr (e.symm x).2 i = 0
      rw [show e.symm x = (⟨x, hx⟩, 0) from hfirst ⟨x, hx⟩]
      simp
    refine ⟨m + Module.finrank ℚ q, d, ?_⟩
    intro r hr i j hji
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin (Module.finrank ℚ q) ≃ _).surjective i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin (Module.finrank ℚ q) ≃ _).surjective j
    change (d₀.reindex finSumFinEquiv).repr
      (r • (d₀.reindex finSumFinEquiv) (finSumFinEquiv j)) (finSumFinEquiv i) = 0
    simp only [Basis.repr_reindex_apply, Basis.reindex_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · rw [hcoeff]
      exact hb r hr i j hji
    · change m + (j : ℕ) ≤ (i : ℕ) at hji
      omega
    · exact hzero _ (hmap r hr _) i
    · exact hzero _ (hmap r hr _) i

/-- A nil left ideal acts strictly triangularly in one basis of any
finite-dimensional rational representation. -/
theorem exists_strict_upper_basis_of_nilIdeal {R M : Type*} [Ring R] [Algebra ℚ R]
    [AddCommGroup M] [Module R M] [Module ℚ M] [IsScalarTower ℚ R M]
    [FiniteDimensional ℚ M] (I : Ideal R) (hI : ∀ r ∈ I, IsNilpotent r) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ M),
      ∀ r ∈ I, ∀ i j, j ≤ i → b.repr (r • b j) i = 0 := by
  let : IsNoetherian R M := isNoetherian_of_tower ℚ inferInstance
  let : IsArtinian R M := isArtinian_of_tower ℚ inferInstance
  exact exists_strict_upper_basis_of_finiteLength I hI
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- Convert a common strictly triangular basis into a single conjugating
invertible rational matrix. -/
theorem exists_conjugating_strict_upper_of_basis {n : ℕ}
    (I : Set (Matrix (Fin n) (Fin n) ℚ)) (b : Basis (Fin n) ℚ (Fin n → ℚ))
    (hb : ∀ r ∈ I, ∀ i j, j ≤ i → b.repr (r *ᵥ b j) i = 0) :
    ∃ P : Matrix.GeneralLinearGroup (Fin n) ℚ, ∀ r ∈ I, ∀ i j : Fin n, j ≤ i →
      ((↑P⁻¹ : Matrix (Fin n) (Fin n) ℚ) * r *
        (P : Matrix (Fin n) (Fin n) ℚ)) i j = 0 := by
  let s := Pi.basisFun ℚ (Fin n)
  let P : Matrix.GeneralLinearGroup (Fin n) ℚ :=
    ⟨s.toMatrix b, b.toMatrix s, s.toMatrix_mul_toMatrix_flip b,
      b.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P, ?_⟩
  intro r hr i j hji
  change (b.toMatrix s * r * s.toMatrix b) i j = 0
  rw [basis_toMatrix_mul b s s r, linearMap_toMatrix_mul_basis_toMatrix,
    LinearMap.toMatrix_apply]
  simpa only [s, Matrix.toLin_eq_toLin', Matrix.toLin'_apply] using hb r hr i j hji

open scoped Matrix.Module in
/-- A nil submodule stable under left multiplication by its containing rational
matrix algebra is simultaneously strictly upper triangular in a rational basis.
The theorem also includes dimension zero. -/
theorem exists_conjugating_strict_upper {n : ℕ}
    (A : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ))
    (I : Submodule ℚ (Matrix (Fin n) (Fin n) ℚ)) (hIA : I ≤ A.toSubmodule)
    (hleft : ∀ r ∈ I, ∀ a ∈ A, a * r ∈ I)
    (hnil : ∀ r ∈ I, IsNilpotent r) :
    ∃ P : Matrix.GeneralLinearGroup (Fin n) ℚ, ∀ r ∈ I, ∀ i j : Fin n, j ≤ i →
      ((↑P⁻¹ : Matrix (Fin n) (Fin n) ℚ) * r *
        (P : Matrix (Fin n) (Fin n) ℚ)) i j = 0 := by
  let J : Ideal A :=
    { carrier := {r | (r : Matrix (Fin n) (Fin n) ℚ) ∈ I}
      zero_mem' := I.zero_mem
      add_mem' := fun hr hs => I.add_mem hr hs
      smul_mem' := fun a r hr => hleft r hr a a.property }
  have hJ : ∀ r ∈ J, IsNilpotent r := by
    intro r hr
    obtain ⟨k, hk⟩ := hnil r hr
    refine ⟨k, Subtype.ext ?_⟩
    exact hk
  obtain ⟨m, b, hb⟩ := exists_strict_upper_basis_of_nilIdeal (M := Fin n → ℚ) J hJ
  have hmn : m = n := by simpa using (Module.finrank_eq_card_basis b).symm
  subst m
  apply exists_conjugating_strict_upper_of_basis (I : Set _) b
  intro r hr i j hji
  exact hb ⟨r, hIA hr⟩ hr i j hji

end Kourovka.P21_40

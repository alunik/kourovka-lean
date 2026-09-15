import Kourovka.Problems.P21_40.Statement
import Kourovka.Problems.P21_40.Proof.TraceRadical
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.NoncommRing

/-!
# The trace ideal and finite-index kernel

The rational span of a matrix group is an algebra. The radical of its trace
pairing is a two-sided nil ideal. Integral bounded traces distinguish the
cosets of the associated normal subgroup.
-/

namespace Kourovka.P21_40

abbrev RationalMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

/-- The faithful matrix representation of a subgroup of the rational general linear group. -/
def matrixRepresentation {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) : G →* RationalMatrix n :=
  (Units.coeHom (RationalMatrix n)).comp G.subtype

/-- The algebra spanned by the matrices in the group. -/
def groupAlgebra {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) : Subalgebra ℚ (RationalMatrix n) :=
  Algebra.adjoin ℚ (MonoidHom.mrange (matrixRepresentation G))

theorem groupAlgebra_toSubmodule {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) :
    (groupAlgebra G).toSubmodule = Submodule.span ℚ (Set.range (matrixRepresentation G)) := by
  rw [groupAlgebra, Algebra.adjoin_eq_span, Submonoid.closure_eq]
  rfl

theorem matrix_mem_groupAlgebra {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) (g : G) :
    matrixRepresentation G g ∈ groupAlgebra G :=
  Algebra.subset_adjoin ⟨g, rfl⟩

/-- The radical of the matrix trace pairing on a rational matrix algebra. -/
def traceIdeal {n : ℕ} (A : Subalgebra ℚ (RationalMatrix n)) :
    Submodule ℚ (RationalMatrix n) where
  carrier := {r | r ∈ A ∧ ∀ b ∈ A, Matrix.trace (r * b) = 0}
  zero_mem' := ⟨A.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hxtr⟩ ⟨hy, hytr⟩
    exact ⟨A.add_mem hx hy, fun b hb => by simp [add_mul, hxtr b hb, hytr b hb]⟩
  smul_mem' := by
    rintro c x ⟨hx, hxtr⟩
    exact ⟨A.smul_mem hx c, fun b hb => by simp [hxtr b hb]⟩

theorem traceIdeal_le {n : ℕ} (A : Subalgebra ℚ (RationalMatrix n)) :
    traceIdeal A ≤ A.toSubmodule := fun _ hr => hr.1

theorem traceIdeal_mul_right {n : ℕ} {A : Subalgebra ℚ (RationalMatrix n)}
    {r a : RationalMatrix n} (hr : r ∈ traceIdeal A) (ha : a ∈ A) :
    r * a ∈ traceIdeal A :=
  ⟨A.mul_mem hr.1 ha, fun b hb => by
    rw [mul_assoc]
    exact hr.2 _ (A.mul_mem ha hb)⟩

theorem traceIdeal_mul_left {n : ℕ} {A : Subalgebra ℚ (RationalMatrix n)}
    {r a : RationalMatrix n} (hr : r ∈ traceIdeal A) (ha : a ∈ A) :
    a * r ∈ traceIdeal A :=
  ⟨A.mul_mem ha hr.1, fun b hb => by
    rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.trace_mul_comm]
    exact hr.2 _ (A.mul_mem hb ha)⟩

theorem traceIdeal_isNilpotent {n : ℕ} {A : Subalgebra ℚ (RationalMatrix n)}
    {r : RationalMatrix n} (hr : r ∈ traceIdeal A) : IsNilpotent r := by
  apply Matrix.isNilpotent_of_forall_trace_pow_eq_zero
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [pow_succ']
  exact hr.2 _ (A.pow_mem hr.1 j)

/-- The normal subgroup acting as the identity modulo the trace ideal. -/
def traceKernel {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) : Subgroup G where
  carrier := {g | matrixRepresentation G g - 1 ∈ traceIdeal (groupAlgebra G)}
  one_mem' := by simp [map_one, (traceIdeal (groupAlgebra G)).zero_mem]
  mul_mem' := by
    intro g h hg hh
    change matrixRepresentation G (g * h) - 1 ∈ traceIdeal (groupAlgebra G)
    rw [map_mul]
    have heq : matrixRepresentation G g * matrixRepresentation G h - 1 =
        (matrixRepresentation G g - 1) * matrixRepresentation G h +
          (matrixRepresentation G h - 1) := by noncomm_ring
    rw [heq]
    exact (traceIdeal (groupAlgebra G)).add_mem
      (traceIdeal_mul_right hg (matrix_mem_groupAlgebra G h)) hh
  inv_mem' := by
    intro g hg
    change matrixRepresentation G g⁻¹ - 1 ∈ traceIdeal (groupAlgebra G)
    have hmul : matrixRepresentation G g * matrixRepresentation G g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have heq : matrixRepresentation G g⁻¹ - 1 =
        -((matrixRepresentation G g - 1) * matrixRepresentation G g⁻¹) := by
      rw [sub_mul, one_mul, hmul]
      abel
    rw [heq]
    exact (traceIdeal (groupAlgebra G)).neg_mem
      (traceIdeal_mul_right hg (matrix_mem_groupAlgebra G g⁻¹))

theorem traceKernel_normal {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) : (traceKernel G).Normal := by
  constructor
  intro g hg a
  change matrixRepresentation G (a * g * a⁻¹) - 1 ∈ traceIdeal (groupAlgebra G)
  simp only [map_mul]
  have hmul : matrixRepresentation G a * matrixRepresentation G a⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have heq : matrixRepresentation G a * matrixRepresentation G g *
      matrixRepresentation G a⁻¹ - 1 =
      matrixRepresentation G a * (matrixRepresentation G g - 1) *
        matrixRepresentation G a⁻¹ := by
    rw [mul_sub, mul_one, sub_mul, hmul]
  rw [heq]
  exact traceIdeal_mul_right (traceIdeal_mul_left hg (matrix_mem_groupAlgebra G a))
    (matrix_mem_groupAlgebra G a⁻¹)

theorem inv_mul_mem_traceKernel_iff {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) (g h : G) :
    g⁻¹ * h ∈ traceKernel G ↔
      matrixRepresentation G h - matrixRepresentation G g ∈ traceIdeal (groupAlgebra G) := by
  have hg : matrixRepresentation G g * matrixRepresentation G g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hgi : matrixRepresentation G g⁻¹ * matrixRepresentation G g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  constructor
  · intro hh
    have hm := traceIdeal_mul_left hh (matrix_mem_groupAlgebra G g)
    change matrixRepresentation G g * (matrixRepresentation G (g⁻¹ * h) - 1) ∈
      traceIdeal (groupAlgebra G) at hm
    simpa only [map_mul, mul_sub, ← mul_assoc, hg, one_mul, mul_one] using hm
  · intro hh
    have hm := traceIdeal_mul_left hh (matrix_mem_groupAlgebra G g⁻¹)
    change matrixRepresentation G (g⁻¹ * h) - 1 ∈ traceIdeal (groupAlgebra G)
    simpa only [map_mul, mul_sub, hgi] using hm

theorem traceKernel_quotient_eq_iff {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)) (g h : G) :
    (g : G ⧸ traceKernel G) = h ↔
      ∀ b ∈ groupAlgebra G,
        Matrix.trace (matrixRepresentation G g * b) =
          Matrix.trace (matrixRepresentation G h * b) := by
  rw [QuotientGroup.eq, inv_mul_mem_traceKernel_iff]
  constructor
  · intro hdiff b hb
    have ht := hdiff.2 b hb
    exact (sub_eq_zero.mp (by simpa only [sub_mul, Matrix.trace_sub] using ht)).symm
  · intro ht
    refine ⟨(groupAlgebra G).sub_mem (matrix_mem_groupAlgebra G h)
      (matrix_mem_groupAlgebra G g), ?_⟩
    intro b hb
    simp only [sub_mul, Matrix.trace_sub, sub_eq_zero]
    exact (ht b hb).symm

/-- Right multiplication followed by trace, viewed as a linear functional. -/
def rightTrace {n : ℕ} (a : RationalMatrix n) : RationalMatrix n →ₗ[ℚ] ℚ where
  toFun b := Matrix.trace (a * b)
  map_add' x y := by simp [mul_add]
  map_smul' c x := by simp

/-- A finite set of possible traces bounds the index of the trace kernel. -/
theorem traceKernel_finiteIndex_of_trace_mem {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (T : Finset ℚ) (hT : ∀ g : G, Matrix.trace (matrixRepresentation G g) ∈ T) :
    (traceKernel G).FiniteIndex ∧ (traceKernel G).index ≤ T.card ^ (n ^ 2) := by
  classical
  let S : Set (RationalMatrix n) := Set.range (matrixRepresentation G)
  let d := Module.finrank ℚ (Submodule.span ℚ S)
  obtain ⟨b, hb, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ S
  have hspanA : Submodule.span ℚ (Set.range b) = (groupAlgebra G).toSubmodule := by
    exact hspan.trans (groupAlgebra_toSubmodule G).symm
  let σ : G → (Fin d → T) := fun g i =>
    ⟨Matrix.trace (matrixRepresentation G g * b i), by
      obtain ⟨h, hh⟩ := hb i
      rw [← hh, ← map_mul]
      exact hT (g * h)⟩
  have hσ : ∀ g h : G, σ g = σ h ↔ (g : G ⧸ traceKernel G) = h := by
    intro g h
    rw [traceKernel_quotient_eq_iff]
    constructor
    · intro heq
      have hle : Submodule.span ℚ (Set.range b) ≤
          (rightTrace (matrixRepresentation G g - matrixRepresentation G h)).ker := by
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        change Matrix.trace ((matrixRepresentation G g - matrixRepresentation G h) * b i) = 0
        rw [sub_mul, Matrix.trace_sub, sub_eq_zero]
        exact congrArg Subtype.val (congrFun heq i)
      intro x hx
      have hx' : x ∈ (groupAlgebra G).toSubmodule := hx
      rw [← hspanA] at hx'
      have hz := hle hx'
      change Matrix.trace ((matrixRepresentation G g - matrixRepresentation G h) * x) = 0 at hz
      simpa only [sub_mul, Matrix.trace_sub, sub_eq_zero] using hz
    · intro heq
      funext i
      apply Subtype.ext
      exact heq (b i) (Algebra.subset_adjoin (hb i))
  let f : (G ⧸ traceKernel G) → (Fin d → T) := fun q => σ q.out
  have hf : Function.Injective f := by
    intro q r hqr
    have heq := (hσ q.out r.out).mp hqr
    simpa only [Quotient.out_eq] using heq
  let : Finite (G ⧸ traceKernel G) := Finite.of_injective f hf
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  have hd : d ≤ n ^ 2 := by
    calc
      d ≤ Module.finrank ℚ (RationalMatrix n) := (Submodule.span ℚ S).finrank_le
      _ = n ^ 2 := by simp [RationalMatrix, Module.finrank_matrix, pow_two]
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨_, hT 1⟩
  calc
    (traceKernel G).index = Nat.card (G ⧸ traceKernel G) := rfl
    _ ≤ Nat.card (Fin d → T) := Nat.card_le_card_of_injective f hf
    _ = T.card ^ d := by simp [Nat.card_eq_fintype_card]
    _ ≤ T.card ^ (n ^ 2) := Nat.pow_le_pow_right hpos hd

/-- The possible integral traces in rational dimension `n`. -/
noncomputable def boundedTraceSet (n : ℕ) : Finset ℚ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun z : ℤ => (z : ℚ))

theorem boundedTraceSet_card_le (n : ℕ) : (boundedTraceSet n).card ≤ 2 * n + 1 := by
  classical
  calc
    (boundedTraceSet n).card ≤ (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := Finset.card_image_le
    _ = 2 * n + 1 := by rw [Int.card_Icc]; omega

theorem traceKernel_finiteIndex_and_index_le {n : ℕ}
    (G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ))
    (htr : ∀ g : G, ∃ z : ℤ, Matrix.trace (matrixRepresentation G g) = (z : ℚ) ∧
      -(n : ℤ) ≤ z ∧ z ≤ n) :
    (traceKernel G).FiniteIndex ∧ (traceKernel G).index ≤ (2 * n + 1) ^ (n ^ 2) := by
  classical
  obtain ⟨hfin, hbound⟩ := traceKernel_finiteIndex_of_trace_mem G (boundedTraceSet n) (by
    intro g
    obtain ⟨z, hz, hzlo, hzhi⟩ := htr g
    exact Finset.mem_image.mpr ⟨z, Finset.mem_Icc.mpr ⟨hzlo, hzhi⟩, hz.symm⟩)
  exact ⟨hfin, hbound.trans (Nat.pow_le_pow_left (boundedTraceSet_card_le n) _)⟩

end Kourovka.P21_40

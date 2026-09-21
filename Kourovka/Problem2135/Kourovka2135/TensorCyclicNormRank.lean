import Kourovka2135.CocycleTwoPowerNorms
import Kourovka2135.LinearRankCertificate
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Abel

/-! Small coefficient projections prove tensor norm rank bounds without dense
tensor matrices. The C4 argument uses the explicit inverse T+T²+T³ when T⁴=1
in characteristic two. All operator/coefficient hypotheses are explicit. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.TensorCyclicNormRank

open scoped TensorProduct
open CocycleTwoPowerNorms

variable {k V W : Type*} [Field k] [CharP k 2]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Project one tensor factor through a scalar-valued functional. -/
def row (l : W →ₗ[k] k) : V ⊗[k] W →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (TensorProduct.map LinearMap.id l)

omit [CharP k 2] in
@[simp] theorem row_tmul (l : W →ₗ[k] k) (v : V) (w : W) :
    row l (v ⊗ₜ[k] w) = l w • v := by
  simp only [row, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul]

/-- Insert a fixed vector in one tensor factor. -/
def column (w : W) : V →ₗ[k] V ⊗[k] W := (TensorProduct.mk k V W).flip w

omit [CharP k 2] in
@[simp] theorem column_apply (w : W) (v : V) : column w v = v ⊗ₜ[k] w := rfl

include k in
private theorem vector_add_self_zero (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : k) + 1) • v := by simp only [add_smul, one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

def inversePolynomial (T : Module.End k V) : Module.End k V := T + T ^ 2 + T ^ 3

/-- The inverse polynomial is an involution for every operator of order dividing four. -/
theorem inversePolynomial_sq (T : Module.End k V) (hT : T ^ 4 = 1) :
    inversePolynomial T ^ 2 = 1 := by
  have h2 : (2 : Module.End k V) = 0 := by
    rw [← one_add_one_eq_two]
    ext v
    change v + v = 0
    exact vector_add_self_zero (k := k) v
  have hs {a b : Module.End k V} (h : Commute a b) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
    rw [h.add_sq, h2, zero_mul, zero_mul, add_zero]
  have h6 : T ^ 6 = T ^ 2 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, hT, one_mul]
  have hd : T ^ 2 + T ^ 2 = 0 := by
    ext v
    exact vector_add_self_zero (k := k) _
  unfold inversePolynomial
  rw [hs ((Commute.self_pow T 3).add_left (Commute.pow_pow_self T 2 3)),
    hs (Commute.self_pow T 2), ← pow_mul, ← pow_mul]
  change T ^ 2 + T ^ 4 + T ^ 6 = 1
  rw [hT, h6, add_right_comm, hd, zero_add]

omit [CharP k 2] in
/-- Conjugate actual operators have equal range dimension. -/
theorem finrank_range_eq_of_intertwining (e : V ≃ₗ[k] W)
    (f : Module.End k V) (g : Module.End k W) (h : ∀ v, e (f v) = g (e v)) :
    Module.finrank k f.range = Module.finrank k g.range := by
  have hm : f.range.map e.toLinearMap = g.range := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
      obtain ⟨x, rfl⟩ := hv
      exact ⟨e x, (h x).symm⟩
    · rintro ⟨x, rfl⟩
      refine Submodule.mem_map.mpr ⟨f (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
      change e (f (e.symm x)) = g x
      rw [h, e.apply_symm_apply]
  have hd := (e.finrank_map_eq f.range).symm
  change Module.finrank k f.range = Module.finrank k (f.range.map e.toLinearMap) at hd
  rw [hm] at hd
  exact hd

variable [FiniteDimensional k V] [FiniteDimensional k W]

/-- One nonzero repeated coefficient in the three powers supplies a quarter-rank minor. -/
theorem finrank_le_normFour_tensor (T : Module.End k V) (A : Module.End k W)
    (hT : T ^ 4 = 1) (e : W) (l : W →ₗ[k] k) (c : k) (hc : c ≠ 0)
    (h0 : l e = 0) (h1 : l (A e) = c) (h2 : l ((A ^ 2) e) = c)
    (h3 : l ((A ^ 3) e) = c) :
    Module.finrank k V ≤ Module.finrank k
      (LinearMap.range (normFour (TensorProduct.map T A))) := by
  let S := inversePolynomial T
  have hs : S * S = 1 := by simpa only [S, pow_two] using inversePolynomial_sq T hT
  have hproj : (row l).comp ((normFour (TensorProduct.map T A)).comp (column e)) =
      c • S := by
    ext v
    simp only [LinearMap.comp_apply, column_apply, normFour, LinearMap.add_apply,
      TensorProduct.map_pow, TensorProduct.map_tmul, Module.End.one_apply,
      map_add, row_tmul, h0, h1, h2, h3, zero_smul, add_zero,
      LinearMap.smul_apply, S, inversePolynomial, smul_add]
    abel
  apply LinearRankCertificate.finrank_le_range _ (column e)
    ((c⁻¹ • S).comp (row l))
  rw [LinearMap.comp_assoc, hproj]
  ext v
  change c⁻¹ • S (c • S v) = v
  rw [map_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact congrArg (fun F : Module.End k V => F v) hs

omit [CharP k 2] in
/-- Two coordinate vectors exchanged out of the projected plane give half-rank. -/
theorem twice_finrank_le_normTwo_tensor (T : Module.End k V) (A : Module.End k W)
    (e0 e1 : W) (l0 l1 : W →ₗ[k] k)
    (h00 : l0 e0 = 1) (h01 : l0 e1 = 0) (h10 : l1 e0 = 0) (h11 : l1 e1 = 1)
    (ha00 : l0 (A e0) = 0) (ha01 : l0 (A e1) = 0)
    (ha10 : l1 (A e0) = 0) (ha11 : l1 (A e1) = 0) :
    2 * Module.finrank k V ≤ Module.finrank k
      (LinearMap.range (normTwo (TensorProduct.map T A))) := by
  let cols : V × V →ₗ[k] V ⊗[k] W := (column e0).coprod (column e1)
  let rows : V ⊗[k] W →ₗ[k] V × V := (row l0).prod (row l1)
  have h : rows.comp ((normTwo (TensorProduct.map T A)).comp cols) = LinearMap.id := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · simp [rows, cols, normTwo, LinearMap.coprod_apply, map_add,
        h00, h01, ha00, ha01]
    · simp [rows, cols, normTwo, LinearMap.coprod_apply, map_add,
        h10, h11, ha10, ha11]
  have hr := LinearRankCertificate.finrank_le_range _ cols rows h
  simpa only [Module.finrank_prod, two_mul] using hr

end Kourovka2135.TensorCyclicNormRank

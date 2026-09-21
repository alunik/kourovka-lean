import Kourovka2135.NormalQuotientRepresentation
import Kourovka2135.RelativeCongruence
import Mathlib.GroupTheory.OrderOfElement

/-! Convert kernel corrections into actual kernel conjugations. The difference
map is the actual forward conjugation difference on N/Z(N). Its surjectivity
gives the required conjugacy-class times center decomposition. Centrality in
the ambient group then removes the two central factors from the commutator.
The core does not need class two or finiteness. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.ConjugateCommutatorCorrection

open scoped IsMulCommutative

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- The actual forward difference, matching `conj_a - id` in additive notation. -/
def quotientDifference (a : G) (x : N ⧸ Subgroup.center N) :
    N ⧸ Subgroup.center N :=
  normalQuotientAut N (Subgroup.center N) a x * x⁻¹

@[simp] theorem quotientDifference_mk (a : G) (n : N) :
    quotientDifference N a (QuotientGroup.mk' (Subgroup.center N) n) =
      QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal a n * n⁻¹) := by
  simp only [quotientDifference, normalQuotientAut_apply_mk, map_mul, map_inv]

/-- The standard elementary-abelian representation difference is exactly the same map. -/
theorem surjective_quotientDifference_of_linear (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] (a : G)
    (h : Function.Surjective
      (normalQuotientRepresentation N (Subgroup.center N) p a -
        (1 : Module.End (ZMod p) (Additive (N ⧸ Subgroup.center N))))) :
    Function.Surjective (quotientDifference N a) := by
  intro q
  obtain ⟨x, hx⟩ := h (Additive.ofMul q)
  refine ⟨x.toMul, ?_⟩
  change Additive.ofMul (normalQuotientAut N (Subgroup.center N) a x.toMul) - x =
    Additive.ofMul q at hx
  have hh := congrArg (fun z : Additive (N ⧸ Subgroup.center N) => z.toMul) hx
  simpa only [toMul_sub, toMul_ofMul, div_eq_mul_inv,
    quotientDifference] using hh

/-- Surjectivity modulo the internal center gives an actual central-factor decomposition.
The conjugator is constructed from a preimage of the inverse correction. -/
theorem exists_conjugate_mul_center (a : G)
    (h : Function.Surjective (quotientDifference N a)) (u : N) :
    ∃ x : N, ∃ z : Subgroup.center N,
      a * (u : G) = (x : G)⁻¹ * a * (x : G) * ((z : N) : G) := by
  obtain ⟨q, hq⟩ := h (QuotientGroup.mk' (Subgroup.center N) u⁻¹)
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) q
  let d : N := MulAut.conjNormal a n * n⁻¹
  have hd : QuotientGroup.mk' (Subgroup.center N) d =
      QuotientGroup.mk' (Subgroup.center N) u⁻¹ := by
    simpa only [quotientDifference_mk] using hq
  have hz : d * u ∈ Subgroup.center N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (Subgroup.center N) (d * u) = 1
    rw [map_mul, hd, map_inv, inv_mul_cancel]
  refine ⟨MulAut.conjNormal a n⁻¹, ⟨d * u, hz⟩, ?_⟩
  change a * (u : G) =
    (a * (n : G)⁻¹ * a⁻¹)⁻¹ * a * (a * (n : G)⁻¹ * a⁻¹) *
      ((a * (n : G) * a⁻¹ * (n : G)⁻¹) * (u : G))
  group

/-- Multiplying both inputs by ambient-central factors does not change the commutator. -/
theorem paperCommutator_mul_center (a b z w : G)
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    paperCommutator (a * z) (b * w) = paperCommutator a b := by
  have hzc (g : G) : Commute z g := (Subgroup.mem_center_iff.mp hz g).symm
  have hwc (g : G) : Commute w g := (Subgroup.mem_center_iff.mp hw g).symm
  rw [← (hzc a).eq, ← (hwc b).eq]
  exact paperCommutator_mul_of_cross_commute a b z w (hzc b) (hzc w) (hwc a).symm

/-- Every corrected commutator is a commutator of actual N-conjugates of the original inputs. -/
theorem exists_conjugate_commutator
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (a b : G) (ha : Function.Surjective (quotientDifference N a))
    (hb : Function.Surjective (quotientDifference N b)) (u v : N) :
    ∃ x y : N,
      paperCommutator (a * (u : G)) (b * (v : G)) =
        paperCommutator ((x : G)⁻¹ * a * (x : G)) ((y : G)⁻¹ * b * (y : G)) := by
  obtain ⟨x, z, hx⟩ := exists_conjugate_mul_center N a ha u
  obtain ⟨y, w, hy⟩ := exists_conjugate_mul_center N b hb v
  refine ⟨x, y, ?_⟩
  rw [hx, hy]
  exact paperCommutator_mul_center _ _ _ _
    (hZ ⟨z, z.property, rfl⟩) (hZ ⟨w, w.property, rfl⟩)

omit [N.Normal] in
/-- The explicitly produced right conjugate preserves the input order, including infinite order. -/
theorem orderOf_conjugate (a : G) (x : N) :
    orderOf ((x : G)⁻¹ * a * (x : G)) = orderOf a := by
  simpa only [MulAut.conj_apply, inv_inv] using
    (MulAut.conj (x : G)⁻¹).orderOf_eq a

/-- Kernel conjugation also preserves the actual quotient image used for generation. -/
theorem quotient_conjugate (a : G) (x : N) :
    QuotientGroup.mk' N ((x : G)⁻¹ * a * (x : G)) = QuotientGroup.mk' N a := by
  have hx : QuotientGroup.mk' N (x : G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr x.property
  rw [map_mul, map_mul, map_inv, hx, inv_one, one_mul, mul_one]

/-- A target attained by kernel corrections is attained with the original input orders
and the same actual quotient images. -/
theorem exists_inputs_of_corrections
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (a b t : G) (ha : Function.Surjective (quotientDifference N a))
    (hb : Function.Surjective (quotientDifference N b))
    (h : ∃ u v : N, paperCommutator (a * (u : G)) (b * (v : G)) = t) :
    ∃ a' b' : G, paperCommutator a' b' = t ∧
      orderOf a' = orderOf a ∧ orderOf b' = orderOf b ∧
      QuotientGroup.mk' N a' = QuotientGroup.mk' N a ∧
      QuotientGroup.mk' N b' = QuotientGroup.mk' N b := by
  obtain ⟨u, v, huv⟩ := h
  obtain ⟨x, y, hxy⟩ := exists_conjugate_commutator N hZ a b ha hb u v
  exact ⟨(x : G)⁻¹ * a * (x : G), (y : G)⁻¹ * b * (y : G), hxy.symm.trans huv,
    orderOf_conjugate N a x, orderOf_conjugate N b y,
    quotient_conjugate N a x, quotient_conjugate N b y⟩

end Kourovka2135.ConjugateCommutatorCorrection

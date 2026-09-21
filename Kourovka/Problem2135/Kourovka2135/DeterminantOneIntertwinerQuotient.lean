import Kourovka2135.DeterminantOneIntertwinerKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual graph quotient of the determinant-one intertwiner group.

The original projection kernel is identified with the kernel over G/N by an
explicit quotient map. Its surjectivity follows by removing the actual graph
of the projected N-element from each kernel representative. No abstract
kernel identification or cover-surjectivity premise is used for that equivalence.
-/

set_option autoImplicit false
noncomputable section
universe u v w

namespace Kourovka2135.DeterminantOneIntertwinerQuotient

open DeterminantOneIntertwinerGroup

variable {k : Type v} [Field k] {G : Type u} [Group G]
variable (N : Subgroup G) [N.Normal]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k N V)
variable (hdet : ∀ n : N, LinearEquiv.det (coefficientAut ρ n) = 1)

/-- The actual quotient of the cover by the actual normal graph. -/
abbrev GraphQuotient := Carrier N ρ ⧸ graphSubgroup N ρ hdet

/-- The actual map that kills the graph and nothing else. -/
def quotientMap : Carrier N ρ →* GraphQuotient N ρ hdet :=
  QuotientGroup.mk' (graphSubgroup N ρ hdet)

/-- Every element of the graph quotient has an actual cover representative. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap N ρ hdet) :=
  QuotientGroup.mk'_surjective _

/-- The actual graph projects into the actual normal subgroup N. -/
theorem graph_le_comap : graphSubgroup N ρ hdet ≤ N.comap (projection N ρ) := by
  rintro x ⟨n, rfl⟩
  exact n.property

/-- The induced actual map from the graph quotient to G/N. -/
def quotientProjection : GraphQuotient N ρ hdet →* G ⧸ N :=
  QuotientGroup.map (graphSubgroup N ρ hdet) N (projection N ρ) (graph_le_comap N ρ hdet)

@[simp] theorem quotientProjection_mk (a : Carrier N ρ) :
    quotientProjection N ρ hdet (quotientMap N ρ hdet a) =
      QuotientGroup.mk' N (projection N ρ a) := rfl

/-- Surjectivity of the original actual projection gives surjectivity after graph quotient. -/
theorem quotientProjection_surjective (hπ : Function.Surjective (projection N ρ)) :
    Function.Surjective (quotientProjection N ρ hdet) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨a, rfl⟩ := hπ g
  exact ⟨quotientMap N ρ hdet a, rfl⟩

/-- The actual graph is killed by the actual quotient map. -/
@[simp] theorem quotientMap_graph (n : N) :
    quotientMap N ρ hdet (graph N ρ hdet n) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨n, rfl⟩

/-- Removing the projected N-element through its actual graph gives an actual kernel element. -/
def kernelFactor (a : Carrier N ρ) (ha : projection N ρ a ∈ N) : (projection N ρ).ker :=
  ⟨a * (graph N ρ hdet ⟨projection N ρ a, ha⟩)⁻¹, by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, projection_graph]
    exact mul_inv_cancel _⟩

@[simp] theorem kernelFactor_coe (a : Carrier N ρ) (ha : projection N ρ a ∈ N) :
    (kernelFactor N ρ hdet a ha : Carrier N ρ) =
      a * (graph N ρ hdet ⟨projection N ρ a, ha⟩)⁻¹ := rfl

/-- Every element projecting into N factors as actual kernel times actual graph. -/
theorem kernelFactor_mul_graph (a : Carrier N ρ) (ha : projection N ρ a ∈ N) :
    (kernelFactor N ρ hdet a ha : Carrier N ρ) *
      graph N ρ hdet ⟨projection N ρ a, ha⟩ = a := by
  rw [kernelFactor_coe, mul_assoc, inv_mul_cancel, mul_one]

/-- Removing an actual graph factor does not change the class in the graph quotient. -/
@[simp] theorem quotientMap_kernelFactor (a : Carrier N ρ) (ha : projection N ρ a ∈ N) :
    quotientMap N ρ hdet (kernelFactor N ρ hdet a ha : Carrier N ρ) =
      quotientMap N ρ hdet a := by
  rw [kernelFactor_coe, map_mul, map_inv, quotientMap_graph, inv_one, mul_one]

/-- The actual quotient map sends the original projection kernel to the new projection kernel. -/
def kernelMap : (projection N ρ).ker →* (quotientProjection N ρ hdet).ker where
  toFun a := ⟨quotientMap N ρ hdet a.val, by
    apply MonoidHom.mem_ker.mpr
    rw [quotientProjection_mk, show projection N ρ a.val = 1 from a.property, map_one]⟩
  map_one' := Subtype.ext (map_one (quotientMap N ρ hdet))
  map_mul' a b := Subtype.ext (map_mul (quotientMap N ρ hdet) a.val b.val)

@[simp] theorem kernelMap_coe (a : (projection N ρ).ker) :
    (kernelMap N ρ hdet a : GraphQuotient N ρ hdet) = quotientMap N ρ hdet a.val := rfl

/-- Disjointness of graph and original kernel gives injectivity of the actual kernel map. -/
theorem kernelMap_injective : Function.Injective (kernelMap N ρ hdet) := by
  intro a b h
  have hD : a.val / b.val ∈ graphSubgroup N ρ hdet :=
    QuotientGroup.eq_iff_div_mem.mp (congrArg Subtype.val h)
  have hK : a.val / b.val ∈ (projection N ρ).ker :=
    (projection N ρ).ker.div_mem a.property b.property
  have hone : a.val / b.val = 1 :=
    Subgroup.disjoint_def.mp (graph_disjoint_ker N ρ hdet) hD hK
  apply Subtype.ext
  exact div_eq_one.mp hone

/-- Every new-kernel class is represented by an element of the original actual kernel. -/
theorem kernelMap_surjective : Function.Surjective (kernelMap N ρ hdet) := by
  intro z
  obtain ⟨a, ha⟩ := quotientMap_surjective N ρ hdet z.val
  have haN : projection N ρ a ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change quotientProjection N ρ hdet (quotientMap N ρ hdet a) = 1
    rw [ha]
    exact z.property
  refine ⟨kernelFactor N ρ hdet a haN, ?_⟩
  apply Subtype.ext
  change quotientMap N ρ hdet (kernelFactor N ρ hdet a haN : Carrier N ρ) = z.val
  rw [quotientMap_kernelFactor, ha]

/-- The explicit equivalence of the old and new actual projection kernels. -/
def kernelEquiv : (projection N ρ).ker ≃* (quotientProjection N ρ hdet).ker :=
  MulEquiv.ofBijective (kernelMap N ρ hdet)
    ⟨kernelMap_injective N ρ hdet, kernelMap_surjective N ρ hdet⟩

@[simp] theorem kernelEquiv_apply (a : (projection N ρ).ker) :
    kernelEquiv N ρ hdet a = kernelMap N ρ hdet a := rfl

/-- The equivalence is concretely the actual quotient map on kernel elements. -/
@[simp] theorem kernelEquiv_coe (a : (projection N ρ).ker) :
    (kernelEquiv N ρ hdet a : GraphQuotient N ρ hdet) = quotientMap N ρ hdet a.val := rfl

/-- The inverse equivalence recovers the original kernel element from its actual quotient class. -/
@[simp] theorem kernelEquiv_symm_kernelMap (a : (projection N ρ).ker) :
    (kernelEquiv N ρ hdet).symm (kernelMap N ρ hdet a) = a :=
  (kernelEquiv N ρ hdet).symm_apply_apply a

/-- The new actual kernel is exactly the image of the old actual kernel under the quotient map. -/
theorem quotientKernel_eq_map : (quotientProjection N ρ hdet).ker =
    (projection N ρ).ker.map (quotientMap N ρ hdet) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, ha⟩ := kernelMap_surjective N ρ hdet ⟨z, hz⟩
    exact ⟨a.val, a.property, congrArg Subtype.val ha⟩
  · rintro z ⟨a, ha, rfl⟩
    exact (kernelMap N ρ hdet ⟨a, ha⟩).property

/-- Centrality of the actual old kernel passes to the actual new kernel. -/
theorem quotientKernel_le_center_of
    (hcentral : (projection N ρ).ker ≤ Subgroup.center (Carrier N ρ)) :
    (quotientProjection N ρ hdet).ker ≤ Subgroup.center (GraphQuotient N ρ hdet) := by
  rw [quotientKernel_eq_map]
  exact (Subgroup.map_mono hcentral).trans
    (Subgroup.map_center_le_center (quotientMap_surjective N ρ hdet))

/-- Any actual prime-power kernel property is transported by the proved kernel equivalence. -/
theorem quotientKernel_isPGroup_of (p : ℕ) (hK : IsPGroup p (projection N ρ).ker) :
    IsPGroup p (quotientProjection N ρ hdet).ker :=
  hK.of_equiv (kernelEquiv N ρ hdet)

section ScalarKernel

variable [FiniteDimensional k V] [IsAlgClosed k] [ρ.IsIrreducible]

/-- Schur's proved centrality yields actual centrality after the graph quotient. -/
theorem quotientKernel_le_center :
    (quotientProjection N ρ hdet).ker ≤ Subgroup.center (GraphQuotient N ρ hdet) :=
  quotientKernel_le_center_of N ρ hdet (DeterminantOneIntertwinerKernel.kernel_le_center N ρ)

/-- Power-of-two degree gives an actual binary kernel after the graph quotient. -/
theorem quotientKernel_isPGroup_two (a : ℕ) (hdim : Module.finrank k V = 2 ^ a) :
    IsPGroup 2 (quotientProjection N ρ hdet).ker :=
  quotientKernel_isPGroup_of N ρ hdet 2
    (DeterminantOneIntertwinerKernel.kernel_isPGroup_two N ρ a hdim)

/-- The actual new kernel is finite by its proved equivalence with the actual old kernel. -/
theorem quotientKernel_finite : Finite (quotientProjection N ρ hdet).ker := by
  let : Finite (projection N ρ).ker := DeterminantOneIntertwinerKernel.kernel_finite N ρ
  exact Finite.of_equiv (projection N ρ).ker (kernelEquiv N ρ hdet).toEquiv

/-- For finite G the actual graph quotient is finite. -/
theorem graphQuotient_finite [Finite G] : Finite (GraphQuotient N ρ hdet) := by
  let : Finite (Carrier N ρ) := DeterminantOneIntertwinerKernel.carrier_finite N ρ
  infer_instance

end ScalarKernel
end Kourovka2135.DeterminantOneIntertwinerQuotient

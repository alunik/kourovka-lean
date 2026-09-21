import Kourovka2135.DeterminantOneIntertwinerQuotient
import Kourovka2135.DeterminantOneIntertwinerSurjective
import Kourovka2135.BinaryCentralExtensionSplit
import Kourovka2135.CentralSplitRetraction
import Kourovka2135.KernelRetractionSection

/-! Extend an actual invariant irreducible representation through a binary
quotient by splitting its concrete finite determinant-one intertwiner cover.
The graph quotient constructs a retraction onto the original scalar kernel;
its complementary section preserves the entire original representation.
No Schur-multiplier or character-extension premise is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.InvariantBinaryRepresentationExtension

open DeterminantOneIntertwinerGroup DeterminantOneIntertwinerQuotient

variable {k G V : Type} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]
variable (N : Subgroup G) [N.Normal] (ρ : Representation k N V)
variable (hdet : ∀ n : N, LinearEquiv.det (coefficientAut ρ n) = 1)

/-- Splitting the actual graph quotient gives a cover section preserving
the actual graph. The kernel correction is constructed as a group retraction. -/
theorem exists_graph_preserving_section
    (hπ : Function.Surjective (projection N ρ))
    (s : (G ⧸ N) →* GraphQuotient N ρ hdet)
    (hs : (quotientProjection N ρ hdet).comp s = MonoidHom.id (G ⧸ N))
    (hc : (quotientProjection N ρ hdet).ker ≤ Subgroup.center (GraphQuotient N ρ hdet)) :
    ∃ a : G →* Carrier N ρ,
      (projection N ρ).comp a = MonoidHom.id G ∧
      a.comp N.subtype = graph N ρ hdet := by
  let π := projection N ρ
  let q := quotientMap N ρ hdet
  let e := kernelEquiv N ρ hdet
  let r := CentralSplitRetraction.retraction (quotientProjection N ρ hdet) s hs hc
  let κ : Carrier N ρ →* π.ker := e.symm.toMonoidHom.comp (r.comp q)
  have hκ : ∀ x : π.ker, κ (x : Carrier N ρ) = x := by
    intro x
    change e.symm (r (q (x : Carrier N ρ))) = x
    rw [← kernelEquiv_coe N ρ hdet x]
    rw [CentralSplitRetraction.retraction_ker]
    exact e.symm_apply_apply x
  have hκgraph (n : N) : κ (graph N ρ hdet n) = 1 := by
    change e.symm (r (q (graph N ρ hdet n))) = 1
    rw [quotientMap_graph, map_one, map_one]
  let a := KernelRetractionSection.sectionHom π κ hκ hπ
  refine ⟨a, KernelRetractionSection.projection_comp_section π κ hκ hπ, ?_⟩
  apply MonoidHom.ext
  intro n
  exact KernelRetractionSection.section_projection_of_retraction_eq_one
    π κ hκ hπ (graph N ρ hdet n) (hκgraph n)

variable [Finite G] [IsAlgClosed k] [FiniteDimensional k V] [ρ.IsIrreducible]
variable [Group.IsPerfect (G ⧸ N)]

include hdet in
/-- The original representation extends on its original coefficient space,
with determinant one, by the actual finite central binary-cover construction. -/
theorem exists_extension
    (hinvariant : ∀ g : G, Nonempty (ρ.Equiv (ρ.comp (MulAut.conjNormal g).toMonoidHom)))
    (a : ℕ) (hdim : Module.finrank k V = 2 ^ a)
    (F : Type) [Field F] [Fintype F] [CharP F 2]
    (f : ℕ) (hcard : Fintype.card F = 2 ^ f) (hf : 3 ≤ f)
    (e : SLTwo.SL2 F ≃* (G ⧸ N)) :
    ∃ ρhat : Representation k G V,
      ρhat.comp N.subtype = ρ ∧ ∀ g : G, LinearMap.det (ρhat g) = 1 := by
  let : Finite (GraphQuotient N ρ hdet) := graphQuotient_finite N ρ hdet
  have hπ := DeterminantOneIntertwinerSurjective.projection_surjective_of_equiv N ρ hinvariant
  have hc := quotientKernel_le_center N ρ hdet
  obtain ⟨s, hs⟩ := BinaryCentralExtensionSplit.exists_section
    (quotientProjection N ρ hdet) (quotientProjection_surjective N ρ hdet hπ)
    (quotientKernel_isPGroup_two N ρ hdet a hdim) hc F f hcard hf e
  obtain ⟨b, _, hb⟩ := exists_graph_preserving_section N ρ hdet hπ s hs hc
  let ρhat : Representation k G V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((operator N ρ).comp b)
  refine ⟨ρhat, ?_, ?_⟩
  · apply MonoidHom.ext
    intro n
    change (operator N ρ (b (n : G))).toLinearMap = ρ n
    have hn : b (n : G) = graph N ρ hdet n := DFunLike.congr_fun hb n
    rw [hn, operator_graph, coefficientAut_toLinearMap]
  · intro g
    change LinearMap.det (operator N ρ (b g)).toLinearMap = 1
    rw [← LinearEquiv.coe_det, operator_det, Units.val_one]

end Kourovka2135.InvariantBinaryRepresentationExtension

import Kourovka2135.SuzukiEightCodeGeometry
import Kourovka2135.SuzukiEightPairedGoodSet

/-! The actual epimorphism from the paired matrix cover to the concrete Sz(8).
The first matrix component is transported entrywise by the proved field
equivalence.  Surjectivity uses the exhaustive canonical root/torus certificates.
-/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiEightPairedProjection

open BenderSuzuki.MatrixGroups
open SuzukiEightPairedGoodSet
open SuzukiEightCodeGeometry

/-- The ambient first projection followed by the actual field isomorphism. -/
def ambientProjection : Ambient →* ActualUnitMatrix :=
  actualMap.comp (MonoidHom.fst SuzukiEightCoverCodeMatrices.UnitMatrix
    SuzukiEightCoverMatrices.UnitMatrix)

theorem ambientProjection_c : ambientProjection c = actualC := actualMap_c
theorem ambientProjection_b : ambientProjection b = actualB := actualMap_b

theorem coverGroup_le : coverGroup ≤ (SuzukiMatrixSubgroup 1).comap ambientProjection := by
  apply (Subgroup.closure_le _).2
  intro g hg
  rcases Set.mem_insert_iff.mp hg with rfl | hg
  · change ambientProjection c ∈ SuzukiMatrixSubgroup 1
    rw [ambientProjection_c]
    exact actualC_mem
  · obtain rfl := Set.mem_singleton_iff.mp hg
    change ambientProjection b ∈ SuzukiMatrixSubgroup 1
    rw [ambientProjection_b]
    exact actualB_mem

/-- The canonical epimorphism; its domain is the actual paired matrix subgroup. -/
def projection : E →* SuzukiGeometry.G 1 :=
  (ambientProjection.comp coverGroup.subtype).codRestrict (SuzukiMatrixSubgroup 1)
    (fun g => coverGroup_le g.property)

theorem projection_coe (g : E) :
    (projection g : ActualUnitMatrix) = actualMap g.val.1 := rfl

theorem projection_c : projection ⟨c, c_mem⟩ = C := by
  apply Subtype.ext
  exact ambientProjection_c

theorem projection_b : projection ⟨b, b_mem⟩ = B := by
  apply Subtype.ext
  exact ambientProjection_b

theorem projection_surjective : Function.Surjective projection := by
  let f : E →* ActualUnitMatrix := ambientProjection.comp coverGroup.subtype
  have hc : actualC ∈ f.range := ⟨⟨c, c_mem⟩, ambientProjection_c⟩
  have hb : actualB ∈ f.range := ⟨⟨b, b_mem⟩, ambientProjection_b⟩
  have hrange : SuzukiMatrixSubgroup 1 ≤ f.range := actual_subgroup_le f.range hc hb
  intro g
  obtain ⟨e, he⟩ := hrange g.property
  exact ⟨e, Subtype.ext he⟩

theorem actualMap_injective : Function.Injective actualMap := by
  intro a b h
  apply Units.ext
  funext i j
  apply SuzukiEightCodeField.actualEquiv.injective
  exact congrArg (fun g : ActualUnitMatrix =>
    (g : Matrix (Fin 4) (Fin 4) (SuzukiGeometry.K 1)) i j) h

/-- Membership in the kernel means precisely that the canonical component is 1. -/
theorem projection_eq_one_iff (g : E) : projection g = 1 ↔ g.val.1 = 1 := by
  constructor
  · intro h
    apply actualMap_injective
    calc
      actualMap g.val.1 = (projection g : ActualUnitMatrix) := rfl
      _ = 1 := congrArg Subtype.val h
      _ = actualMap 1 := (map_one actualMap).symm
  · intro h
    apply Subtype.ext
    change actualMap g.val.1 = 1
    rw [h, map_one]

theorem mem_kernel_iff (g : E) : g ∈ projection.ker ↔ g.val.1 = 1 :=
  projection_eq_one_iff g

end Kourovka2135.SuzukiEightPairedProjection

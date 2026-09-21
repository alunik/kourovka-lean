import Kourovka2135.BinarySLTwoTrivialCohomology
import Kourovka2135.GroupCohomologyFieldExtension
import Mathlib.Algebra.CharP.Algebra

/-! Descent of actual scalar-trivial H2 from the parameter field to F2.
The comparison is an actual representation equivalence after scalar extension,
followed by the checked ordinary-cohomology dimension identity.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.BinarySLTwoPrimeFieldH2

open CategoryTheory RepresentationDensityBaseChange

section ScalarExtension
variable (E L G : Type u) [Field E] [Field L] [Algebra E L] [Group G]

/-- Extending the scalar trivial representation gives the scalar trivial
representation over the larger field, via the actual tensor-unit map. -/
def trivialBaseChangeEquiv :
    Representation.Equiv (baseChange L (Representation.trivial E G E))
      (Representation.trivial L G L) where
  toLinearEquiv := TensorProduct.AlgebraTensorModule.rid E L L
  isIntertwining' g := by
    change (TensorProduct.AlgebraTensorModule.rid E L L).toLinearMap.comp
      ((LinearMap.id : E →ₗ[E] E).baseChange L) =
      LinearMap.id.comp (TensorProduct.AlgebraTensorModule.rid E L L).toLinearMap
    rw [LinearMap.baseChange_id, LinearMap.comp_id, LinearMap.id_comp]

/-- The coefficient equivalence induces actual ordinary cohomology isomorphisms. -/
def trivialBaseChangeCohomologyIso (n : ℕ) :
    groupCohomology (Rep.of (baseChange L (Representation.trivial E G E))) n ≅
      groupCohomology (Rep.of (Representation.trivial L G L)) n :=
  groupCohomology.mapIso (MulEquiv.refl G)
    (trivialBaseChangeEquiv E L G).toLinearEquiv
    (fun g => (trivialBaseChangeEquiv E L G).isIntertwining' g) n

/-- Scalar-trivial ordinary H2 has the same dimension after field extension. -/
theorem finrank_trivial_H2_fieldExtension [Finite G] :
    Module.finrank L (groupCohomology (Rep.of (Representation.trivial L G L)) 2) =
      Module.finrank E (groupCohomology (Rep.of (Representation.trivial E G E)) 2) := by
  rw [← (trivialBaseChangeCohomologyIso E L G 2).toLinearEquiv.finrank_eq]
  exact GroupCohomologyFieldExtension.finrank_H2_baseChange
    (L := L) (Representation.trivial E G E)

end ScalarExtension

variable (F : Type) [Field F] [Fintype F] [CharP F 2]
variable (f : ℕ) (hcard : Fintype.card F = 2 ^ f)

include hcard in
/-- Prime-field H2 vanishing for the actual binary SL2 group in degree f≥3. -/
theorem finrank_H2_eq_zero (hf : 3 ≤ f) :
    Module.finrank (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2))) 2) =
      0 := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rw [← finrank_trivial_H2_fieldExtension (ZMod 2) F (SLTwo.SL2 F)]
  exact BinarySLTwoTrivialCohomology.finrank_trivial_H2_eq_zero
    F (RingHom.id F) f hcard hf

include hcard in
/-- Genuine prime-field ordinary H2 vanishing, with finite-dimensionality
proved before converting the dimension-zero statement. -/
theorem subsingleton_H2 (hf : 3 ≤ f) :
    Subsingleton
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2))) 2) := by
  let : FiniteDimensional (ZMod 2)
      (groupCohomology (Rep.of (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2))) 2) :=
    GroupCohomologyFieldExtension.finiteDimensional_groupCohomology
      (Representation.trivial (ZMod 2) (SLTwo.SL2 F) (ZMod 2)) 1
  exact Module.finrank_zero_iff.mp (finrank_H2_eq_zero F f hcard hf)

end Kourovka2135.BinarySLTwoPrimeFieldH2

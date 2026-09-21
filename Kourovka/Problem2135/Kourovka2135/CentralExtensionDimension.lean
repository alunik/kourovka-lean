import Kourovka2135.CentralExtensionCocycle
import Kourovka2135.NormalSubgroupExtension
import Kourovka2135.GroupCohomologyFieldExtension
import Kourovka2135.Vendor.CFSG.ElementaryAbelian
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finite.Basic

/-! The actual dual of an elementary abelian central kernel embeds in ordinary
scalar H2 for a perfect extension. This gives the kernel dimension bound
without a multiplier or extension-classification assumption. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.CentralExtensionDimension

open AbelianExtensionCocycle CentralExtensionCocycle groupCohomology
open scoped IsMulCommutative

variable {k G Q W : Type u} [Field k] [Group G] [Group Q]
variable [AddCommGroup W] [Module k W]
variable (S : GroupExtension (Multiplicative W) G Q)
variable (hc : S.inl.range ≤ Subgroup.center G)

/-- The actual factor-set map is linear on scalar linear functionals. -/
def dualCocycle : Module.Dual k W →ₗ[k]
    cocycles₂ (Rep.of (Representation.trivial k Q k)) where
  toFun f := characterCocycle S hc f.toAddMonoidHom
  map_add' f g := by ext q; rfl
  map_smul' a f := by ext q; rfl

/-- The dual-kernel class map into ordinary H2. -/
def dualClass : Module.Dual k W →ₗ[k]
    groupCohomology (Rep.of (Representation.trivial k Q k)) 2 :=
  (H2π (Rep.of (Representation.trivial k Q k))).hom.comp (dualCocycle S hc)

/-- Perfectness forces a functional with zero actual extension class to vanish. -/
theorem eq_zero_of_dualClass_eq_zero [Group.IsPerfect G]
    (f : Module.Dual k W) (hf : dualClass S hc f = 0) : f = 0 := by
  obtain ⟨d, hd⟩ := exists_hom_of_characterClass_eq_zero (k := k) S hc f.toAddMonoidHom hf
  ext w
  have h := hom_eq_one_of_perfect d (embed S w)
  rw [hd] at h
  exact h

/-- This is an injection of actual vector spaces, not a dimension assumption. -/
theorem dualClass_injective [Group.IsPerfect G] : Function.Injective (dualClass (k := k) S hc) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro f hf
  change f = 0
  exact eq_zero_of_dualClass_eq_zero S hc f hf

include S hc in
/-- The actual central-kernel dimension is bounded by actual scalar H2. -/
theorem finrank_le_H2 [Group.IsPerfect G] [Finite Q] [FiniteDimensional k W] :
    Module.finrank k W ≤
      Module.finrank k (groupCohomology (Rep.of (Representation.trivial k Q k)) 2) := by
  let : FiniteDimensional k
      (groupCohomology (Rep.of (Representation.trivial k Q k)) 2) :=
    GroupCohomologyFieldExtension.finiteDimensional_groupCohomology
      (Representation.trivial k Q k) 1
  have h := LinearMap.finrank_le_finrank_of_injective (dualClass_injective (k := k) S hc)
  simpa only [Subspace.dual_finrank_eq] using h

/-- The normal-subgroup form uses the canonical short exact sequence. -/
theorem normal_finrank_le_H2
    {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (p : ℕ) [Fact p.Prime] (R : Subgroup G) [R.Normal] [IsElementaryAbelian p R]
    (hc : R ≤ Subgroup.center G) :
    Module.finrank (ZMod p) (Additive R) ≤
      Module.finrank (ZMod p)
        (groupCohomology (Rep.of (Representation.trivial (ZMod p) (G ⧸ R) (ZMod p))) 2) := by
  exact finrank_le_H2 (NormalSubgroupExtension.extension R)
    (by simpa only [NormalSubgroupExtension.extension_inl_range] using hc)

end Kourovka2135.CentralExtensionDimension

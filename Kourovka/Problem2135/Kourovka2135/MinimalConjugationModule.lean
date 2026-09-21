import Kourovka2135.MinimalConjugationQuotient
import Kourovka2135.NormalConjugationEmbedding
import Kourovka2135.AbelianExtensionRepresentation
import Kourovka2135.CentralAutomorphismEquivariance

/-! The actual elementary-abelian kernel in the faithful conjugation quotient.

The normal p-subgroup image embeds into the actual central automorphisms by
proved minimal-kernel action facts. Its elementary abelianity and nontriviality
are derived. The actual nested quotient extension supplies a quotient-group
representation with its compatibility equation proved by construction.

Elementary-abelian instances are explicit where they occur in module-valued
signatures. This module proves the kernel instance; the existing minimal
structure theorem proves the center-quotient instance. No semisimplicity,
module classification, or action-identification premise is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.MinimalConjugationModule

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
variable (hmin : ∀ L : Subgroup G, L.Normal → L < N → L ≤ Subgroup.center G)
variable (hnonabelian : ¬ IsMulCommutative N)
variable (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)

/-- The actual centralizer used for the faithful conjugation quotient. -/
abbrev Centralizer := Subgroup.centralizer (N : Set G)

/-- The actual normal image of R in G/C_G(N). -/
abbrev Kernel := NestedNormalExtension.kernel (Centralizer N) R

/-- Minimality proves the two honest action conditions needed for the actual embedding. -/
def kernelToCentralAut : Kernel N R →* CentralAutomorphismCoordinate.centralSubgroup N :=
  NormalConjugationEmbedding.imageToCentralAut N R
    (fun r z => NormalConjugationEmbedding.conjNormal_fixes_center N
      (minimal_noncentral_center_le N hnonabelian hmin) (r : G) z)
    (fun r n => minimal_centerQuotient_pSubgroup_action Nat.prime_two N hN hmin R hR r n)

/-- Injectivity comes from the actual faithful conjugation quotient. -/
theorem kernelToCentralAut_injective :
    Function.Injective (kernelToCentralAut N hN hmin hnonabelian R hR) :=
  NormalConjugationEmbedding.imageToCentralAut_injective N R _ _

include hN hmin hnonabelian hR in
/-- The actual kernel image is elementary abelian, rather than being assumed so. -/
theorem kernel_isElementaryAbelian : IsElementaryAbelian 2 (Kernel N R) := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  let j := kernelToCentralAut N hN hmin hnonabelian R hR
  have hj : Function.Injective j := kernelToCentralAut_injective N hN hmin hnonabelian R hR
  refine {
    toIsMulCommutative := ⟨⟨fun a b => hj (by rw [map_mul, map_mul, mul_comm])⟩⟩
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  apply hj
  rw [map_pow, map_one]
  exact CentralAutomorphismCoordinate.centralSubgroup_pow_eq_one N 2 (j a)

omit [Finite G] [R.Normal] in
include hnonabelian in
/-- Since N is nonabelian and lies in R, its conjugation image inside the kernel is nontrivial. -/
theorem kernel_nontrivial (hNR : N ≤ R) : Nontrivial (Kernel N R) := by
  apply (Subgroup.nontrivial_iff_ne_bot _).mpr
  intro hbot
  apply hnonabelian
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb : QuotientGroup.mk' (Centralizer N) (b : G) ∈ Kernel N R :=
    Subgroup.mem_map_of_mem _ (hNR b.property)
  rw [hbot] at hb
  have hbC : (b : G) ∈ Centralizer N := (QuotientGroup.eq_one_iff _).mp hb
  exact (Subgroup.mem_centralizer_iff.mp hbC) (a : G) a.property

variable [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)]

include hN hmin hnonabelian hR in
/-- The actual centralizer is contained in R by faithfulness of the minimal center quotient. -/
theorem centralizer_le : Centralizer N ≤ R := by
  let : IsElementaryAbelian 2 (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian Nat.prime_two N hN hmin
  exact minimal_centralizer_le_pSubgroup N hN hmin hnonabelian R hR

/-- The actual extension K -> G/C_G(N) -> G/R. -/
def extension : GroupExtension (Multiplicative (Additive (Kernel N R)))
    (G ⧸ Centralizer N) (G ⧸ R) :=
  NestedNormalExtension.extension (Centralizer N) R
    (centralizer_le N hN hmin hnonabelian R hR)

@[simp] theorem extension_rightHom_mk (g : G) :
    (extension N hN hmin hnonabelian R hR).rightHom
      (QuotientGroup.mk' (Centralizer N) g) = QuotientGroup.mk' R g := rfl

@[simp] theorem extension_inl (k : Kernel N R) :
    (extension N hN hmin hnonabelian R hR).inl
      (Multiplicative.ofAdd (Additive.ofMul k)) = (k : G ⧸ Centralizer N) := rfl

/-- The actual Frattini condition survives the faithful conjugation quotient. -/
theorem extension_range_le_frattini (hRΦ : R ≤ frattini G) :
    (extension N hN hmin hnonabelian R hR).inl.range ≤ frattini (G ⧸ Centralizer N) := by
  change (NestedNormalExtension.extension (Centralizer N) R
    (centralizer_le N hN hmin hnonabelian R hR)).inl.range ≤ _
  rw [NestedNormalExtension.extension_inl_range]
  exact NestedNormalExtension.kernel_le_frattini (Centralizer N) R hRΦ

variable [IsElementaryAbelian 2 (Kernel N R)]

/-- The quotient representation of the actual additive kernel, induced by actual conjugation. -/
def representation : Representation (ZMod 2) (G ⧸ R) (Additive (Kernel N R)) :=
  AbelianExtensionRepresentation.representation (extension N hN hmin hnonabelian R hR) 2

/-- The factor-set compatibility equation is derived from the actual extension. -/
theorem compatibleAction :
    AbelianExtensionCocycle.CompatibleAction (extension N hN hmin hnonabelian R hR)
      (representation N hN hmin hnonabelian R hR) :=
  AbelianExtensionRepresentation.compatibleAction (extension N hN hmin hnonabelian R hR) 2

/-- On actual ambient representatives, the quotient action is exactly kernel conjugation. -/
theorem representation_mk_inl (g : G) (k : Kernel N R) :
    (extension N hN hmin hnonabelian R hR).inl
        (Multiplicative.ofAdd
          (representation N hN hmin hnonabelian R hR (QuotientGroup.mk' R g)
            (Additive.ofMul k))) =
      QuotientGroup.mk' (Centralizer N) g * (k : G ⧸ Centralizer N) *
        (QuotientGroup.mk' (Centralizer N) g)⁻¹ := by
  exact compatibleAction N hN hmin hnonabelian R hR
    (QuotientGroup.mk' (Centralizer N) g) (Additive.ofMul k)

variable [IsElementaryAbelian 2 (N ⧸ Subgroup.center N)]

omit [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)] in
/-- The actual kernel embeds linearly into Hom(N/Z(N), Ω₂(Z(N))). -/
def linearCoordinate : Additive (Kernel N R) →ₗ[ZMod 2]
    (Additive (N ⧸ Subgroup.center N) →ₗ[ZMod 2]
      Additive (CentralAutomorphismTorsion.centerTorsion N 2)) :=
  (CentralAutomorphismTorsion.linearCoordinate N 2).comp
    ((kernelToCentralAut N hN hmin hnonabelian R hR).toAdditive.toZModLinearMap 2)

omit [Group.IsPerfect G] [IsSimpleGroup (G ⧸ R)] in
/-- The displayed linear coordinate is injective by the two actual embeddings. -/
theorem linearCoordinate_injective :
    Function.Injective (linearCoordinate N hN hmin hnonabelian R hR) := by
  apply (CentralAutomorphismTorsion.linearCoordinate_injective N 2).comp
  intro a b h
  change a.toMul = b.toMul
  exact kernelToCentralAut_injective N hN hmin hnonabelian R hR h

end Kourovka2135.MinimalConjugationModule

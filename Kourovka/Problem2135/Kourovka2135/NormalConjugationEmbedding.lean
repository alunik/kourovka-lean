import Kourovka2135.CentralAutomorphismCoordinate
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual faithful conjugation quotient and its normal-subgroup images.

Conjugation on N has kernel C_G(N). Its quotient map into MulAut N is
injective. Explicit center-fixing and central-quotient conditions place the
image of a subgroup R inside the actual central-automorphism subgroup.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.NormalConjugationEmbedding

variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

/-- The kernel of actual conjugation on a normal subgroup is its centralizer. -/
theorem conjNormal_ker :
    (MulAut.conjNormal : G →* MulAut N).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  change (MulAut.conjNormal g : MulAut N) = 1 ↔
    ∀ n ∈ N, n * g = g * n
  constructor
  · intro hg n hn
    have hfix : MulAut.conjNormal g (⟨n, hn⟩ : N) = (⟨n, hn⟩ : N) :=
      congrArg (fun a : MulAut N => a ⟨n, hn⟩) hg
    have he : g * n * g⁻¹ = n := congrArg Subtype.val hfix
    calc
      n * g = (g * n * g⁻¹) * g := congrArg (fun x : G => x * g) he.symm
      _ = g * n := by simp only [mul_assoc, inv_mul_cancel, mul_one]
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = n
    rw [← hg n n.property, mul_assoc, mul_inv_cancel, mul_one]

/-- The actual conjugation homomorphism on the quotient by C_G(N). -/
def quotientConjugation : (G ⧸ Subgroup.centralizer (N : Set G)) →* MulAut N :=
  QuotientGroup.lift (Subgroup.centralizer (N : Set G))
    (MulAut.conjNormal : G →* MulAut N) (by rw [conjNormal_ker])

@[simp] theorem quotientConjugation_mk (g : G) :
    quotientConjugation N (QuotientGroup.mk' (Subgroup.centralizer (N : Set G)) g) =
      MulAut.conjNormal g := rfl

theorem quotientConjugation_injective : Function.Injective (quotientConjugation N) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  exact (conjNormal_ker N).symm

theorem quotientConjugation_comp_mk :
    (quotientConjugation N).comp (QuotientGroup.mk' (Subgroup.centralizer (N : Set G))) =
      (MulAut.conjNormal : G →* MulAut N) := by
  ext g
  rfl

/-- The subgroup's actual image in the faithful conjugation quotient. -/
abbrev quotientImage (R : Subgroup G) : Subgroup (G ⧸ Subgroup.centralizer (N : Set G)) :=
  R.map (QuotientGroup.mk' (Subgroup.centralizer (N : Set G)))

theorem map_quotientImage (R : Subgroup G) :
    (quotientImage N R).map (quotientConjugation N) =
      R.map (MulAut.conjNormal : G →* MulAut N) := by
  rw [Subgroup.map_map, quotientConjugation_comp_mk]

/-- Restriction of the faithful conjugation embedding to the actual image of R. -/
def imageEmbedding (R : Subgroup G) : quotientImage N R →* MulAut N :=
  (quotientConjugation N).comp (quotientImage N R).subtype

theorem imageEmbedding_injective (R : Subgroup G) :
    Function.Injective (imageEmbedding N R) :=
  (quotientConjugation_injective N).comp Subtype.val_injective

theorem imageEmbedding_range (R : Subgroup G) :
    (imageEmbedding N R).range = R.map (MulAut.conjNormal : G →* MulAut N) := by
  rw [imageEmbedding, MonoidHom.range_comp, Subgroup.range_subtype, map_quotientImage]

@[simp] theorem imageEmbedding_mk (R : Subgroup G) (r : R) :
    imageEmbedding N R
        ⟨QuotientGroup.mk' (Subgroup.centralizer (N : Set G)) r,
          Subgroup.mem_map_of_mem _ r.property⟩ =
      MulAut.conjNormal (r : G) := rfl

/-- Ambient centrality supplies pointwise fixation of the internal center. -/
theorem conjNormal_fixes_center
    (hZ : (Subgroup.center N).map N.subtype ≤ Subgroup.center G)
    (g : G) (z : Subgroup.center N) :
    MulAut.conjNormal g (z : N) = z := by
  apply Subtype.ext
  change g * ((z : N) : G) * g⁻¹ = (z : N)
  have hz : ((z : N) : G) ∈ Subgroup.center G :=
    hZ (Subgroup.mem_map_of_mem N.subtype z.property)
  rw [Subgroup.mem_center_iff.mp hz g]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- The two concrete pointwise conditions give membership in the actual
central-automorphism subgroup, with no exponent or finiteness assumption. -/
theorem conjNormal_mem_centralSubgroup (g : G)
    (hZ : ∀ z : Subgroup.center N, MulAut.conjNormal g (z : N) = z)
    (hQ : ∀ n : N, QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal g n) =
      QuotientGroup.mk' (Subgroup.center N) n) :
    (MulAut.conjNormal g : MulAut N) ∈ CentralAutomorphismCoordinate.centralSubgroup N := by
  refine ⟨hZ, ?_⟩
  change characteristicQuotientAut (Subgroup.center N) (MulAut.conjNormal g) = 1
  apply MulEquiv.ext
  intro q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center N) q
  exact hQ n

variable (R : Subgroup G)
variable (hZ : ∀ r : R, ∀ z : Subgroup.center N, MulAut.conjNormal (r : G) (z : N) = z)
variable (hQ : ∀ r : R, ∀ n : N,
  QuotientGroup.mk' (Subgroup.center N) (MulAut.conjNormal (r : G) n) =
    QuotientGroup.mk' (Subgroup.center N) n)

include hZ hQ in
theorem conjugationImage_le_centralSubgroup :
    R.map (MulAut.conjNormal : G →* MulAut N) ≤
      CentralAutomorphismCoordinate.centralSubgroup N := by
  rintro a ⟨r, hr, rfl⟩
  exact conjNormal_mem_centralSubgroup N r (hZ ⟨r, hr⟩) (hQ ⟨r, hr⟩)

/-- The actual image of R in G/C_G(N) embeds into the central automorphisms. -/
def imageToCentralAut : quotientImage N R →*
    CentralAutomorphismCoordinate.centralSubgroup N where
  toFun r := ⟨imageEmbedding N R r,
    conjugationImage_le_centralSubgroup N R hZ hQ (by
      rw [← imageEmbedding_range N R]
      exact ⟨r, rfl⟩)⟩
  map_one' := Subtype.ext (map_one (imageEmbedding N R))
  map_mul' a b := Subtype.ext (map_mul (imageEmbedding N R) a b)

@[simp] theorem imageToCentralAut_coe (r : quotientImage N R) :
    (imageToCentralAut N R hZ hQ r : MulAut N) = imageEmbedding N R r := rfl

theorem imageToCentralAut_injective : Function.Injective (imageToCentralAut N R hZ hQ) := by
  intro a b hab
  apply imageEmbedding_injective N R
  exact congrArg Subtype.val hab

end Kourovka2135.NormalConjugationEmbedding

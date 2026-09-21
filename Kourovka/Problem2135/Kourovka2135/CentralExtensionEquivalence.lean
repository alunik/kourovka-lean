import Kourovka2135.CentralExtensionCocycle

/-! Equal actual factor-set classes give an actual group isomorphism between
central extensions. Both the kernel inclusion and quotient map are preserved;
no classification of extensions is assumed. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.CentralExtensionEquivalence

open AbelianExtensionCocycle groupCohomology

variable {G H Q W : Type u} [Group G] [Group H] [Group Q] [AddCommGroup W]
variable (S : GroupExtension (Multiplicative W) G Q)
variable (T : GroupExtension (Multiplicative W) H Q)

@[simp] theorem rightHom_embed_mul_section (w : W) (q : Q) :
    S.rightHom (embed S w * normalizedSection S q) = q := by
  simp only [map_mul, rightHom_embed, GroupExtension.Section.rightHom_section, one_mul]

@[simp] theorem coordinate_embed_mul_section (w : W) (q : Q) :
    coordinate S (embed S w * normalizedSection S q) = w := by
  apply embed_injective S
  rw [embed_coordinate, rightHom_embed_mul_section]
  group

/-- Actual kernel and quotient coordinates form a bijection. -/
def coordinates : G ≃ W × Q where
  toFun g := (coordinate S g, S.rightHom g)
  invFun x := embed S x.1 * normalizedSection S x.2
  left_inv := embed_coordinate_mul_section S
  right_inv x := by
    apply Prod.ext
    · exact coordinate_embed_mul_section S x.1 x.2
    · exact rightHom_embed_mul_section S x.1 x.2

/-- A quotient-dependent translation of the actual kernel coordinate. -/
def shift (b : Q → W) : W × Q ≃ W × Q where
  toFun x := (x.1 + b x.2, x.2)
  invFun x := (x.1 - b x.2, x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- The underlying coordinate bijection associated with a one-cochain. -/
def shiftedEquiv (b : Q → W) : G ≃ H :=
  ((coordinates S).trans (shift b)).trans (coordinates T).symm

@[simp] theorem shiftedEquiv_coordinate (b : Q → W) (g : G) :
    coordinate T (shiftedEquiv S T b g) = coordinate S g + b (S.rightHom g) := by
  exact coordinate_embed_mul_section T _ _

@[simp] theorem shiftedEquiv_rightHom (b : Q → W) (g : G) :
    T.rightHom (shiftedEquiv S T b g) = S.rightHom g := by
  exact rightHom_embed_mul_section T _ _

/-- A genuine factor-set coboundary difference constructs a group isomorphism. -/
def equivOfCoboundary
    (hS : S.inl.range ≤ Subgroup.center G) (hT : T.inl.range ≤ Subgroup.center H)
    (b : Q → W)
    (hb : ∀ s t, b t - b (s * t) + b s = factorSet S s t - factorSet T s t) :
    G ≃* H :=
  { shiftedEquiv S T b with
    map_mul' := by
      intro g l
      apply (coordinates T).injective
      apply Prod.ext
      · change coordinate T (shiftedEquiv S T b (g * l)) =
          coordinate T (shiftedEquiv S T b g * shiftedEquiv S T b l)
        rw [shiftedEquiv_coordinate, CentralExtensionCocycle.coordinate_mul T hT,
          shiftedEquiv_coordinate, shiftedEquiv_coordinate,
          shiftedEquiv_rightHom, shiftedEquiv_rightHom,
          CentralExtensionCocycle.coordinate_mul S hS, map_mul]
        rw [← (eq_sub_iff_add_eq.mp (hb (S.rightHom g) (S.rightHom l)))]
        abel
      · change T.rightHom (shiftedEquiv S T b (g * l)) =
          T.rightHom (shiftedEquiv S T b g * shiftedEquiv S T b l)
        simp only [shiftedEquiv_rightHom, map_mul] }

@[simp] theorem equivOfCoboundary_rightHom
    (hS : S.inl.range ≤ Subgroup.center G) (hT : T.inl.range ≤ Subgroup.center H)
    (b : Q → W)
    (hb : ∀ s t, b t - b (s * t) + b s = factorSet S s t - factorSet T s t)
    (g : G) : T.rightHom (equivOfCoboundary S T hS hT b hb g) = S.rightHom g :=
  shiftedEquiv_rightHom S T b g

@[simp] theorem equivOfCoboundary_embed
    (hS : S.inl.range ≤ Subgroup.center G) (hT : T.inl.range ≤ Subgroup.center H)
    (b : Q → W)
    (hb : ∀ s t, b t - b (s * t) + b s = factorSet S s t - factorSet T s t)
    (w : W) : equivOfCoboundary S T hS hT b hb (embed S w) = embed T w := by
  have hb1 : b 1 = 0 := by
    simpa only [one_mul, sub_self, zero_add, factorSet_one_left, sub_self] using hb 1 1
  apply (coordinates T).injective
  apply Prod.ext
  · change coordinate T (shiftedEquiv S T b (embed S w)) = coordinate T (embed T w)
    simp only [shiftedEquiv_coordinate, coordinate_embed, rightHom_embed, hb1, add_zero]
  · change T.rightHom (shiftedEquiv S T b (embed S w)) = T.rightHom (embed T w)
    simp only [shiftedEquiv_rightHom, rightHom_embed]

/-- Equality in actual ordinary H2 supplies the required cochain and isomorphism. -/
theorem exists_equiv_of_characterClass_eq
    {k : Type u} [CommRing k] [Module k W]
    (hS : S.inl.range ≤ Subgroup.center G) (hT : T.inl.range ≤ Subgroup.center H)
    (hclass : CentralExtensionCocycle.characterClass (k := k) S hS (AddMonoidHom.id W) =
      CentralExtensionCocycle.characterClass (k := k) T hT (AddMonoidHom.id W)) :
    ∃ e : G ≃* H, (∀ g, T.rightHom (e g) = S.rightHom g) ∧
      ∀ w, e (embed S w) = embed T w := by
  let cS := CentralExtensionCocycle.characterCocycle (k := k) S hS (AddMonoidHom.id W)
  let cT := CentralExtensionCocycle.characterCocycle (k := k) T hT (AddMonoidHom.id W)
  have hz : H2π (Rep.of (Representation.trivial k Q W)) (cS - cT) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hclass
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff (cS - cT)).mp hz
  have hbc (s t : Q) : b t - b (s * t) + b s = factorSet S s t - factorSet T s t := by
    exact congrFun hb (s, t)
  exact ⟨equivOfCoboundary S T hS hT b hbc,
    equivOfCoboundary_rightHom S T hS hT b hbc,
    equivOfCoboundary_embed S T hS hT b hbc⟩

end Kourovka2135.CentralExtensionEquivalence

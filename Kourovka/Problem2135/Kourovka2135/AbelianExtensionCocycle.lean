import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic.Abel

/-! Actual factor sets of abelian group extensions and their ordinary H2 classes.

The extension and its conjugation action are structural inputs. The factor-set
cocycle, coefficient map, and crossed homomorphism arising from a zero class are
constructed here from the actual kernel embedding and quotient homomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.AbelianExtensionCocycle

open CategoryTheory groupCohomology

variable {k J Q W V : Type u} [CommRing k] [Group J] [Group Q]
variable [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
variable (S : GroupExtension (Multiplicative W) J Q)

/-- The actual kernel inclusion, in additive notation on its source. -/
abbrev embed (w : W) : J := S.inl (Multiplicative.ofAdd w)

theorem embed_injective : Function.Injective (embed S) :=
  S.inl_injective

@[simp] theorem embed_zero : embed S (0 : W) = 1 := S.inl.map_one

@[simp] theorem embed_add (a b : W) : embed S (a + b) = embed S a * embed S b :=
  S.inl.map_mul _ _

@[simp] theorem embed_neg (a : W) : embed S (-a) = (embed S a)⁻¹ :=
  S.inl.map_inv _

@[simp] theorem rightHom_embed (w : W) : S.rightHom (embed S w) = 1 :=
  S.rightHom_inl _

/-- A chosen section, explicitly normalized at the identity. -/
def normalizedSection : S.Section := by
  classical
  exact {
    toFun := fun q => if q = 1 then 1 else S.surjInvRightHom q
    rightInverse_rightHom := fun q => by
      by_cases hq : q = 1
      · simp [hq]
      · simp [hq] }

@[simp] theorem normalizedSection_one : normalizedSection S 1 = 1 := by
  simp [normalizedSection]

/-- Inverse of the kernel embedding on its image. Values outside the kernel
are not used in any theorem identifying this function with an inverse. -/
def kernelValue (j : J) : W :=
  Multiplicative.toAdd (Function.invFun S.inl j)

theorem embed_kernelValue (j : J) (hj : S.rightHom j = 1) :
    embed S (kernelValue S j) = j := by
  apply Function.invFun_eq
  change j ∈ S.inl.range
  rw [S.range_inl_eq_ker_rightHom]
  exact hj

@[simp] theorem kernelValue_embed (w : W) : kernelValue S (embed S w) = w := by
  exact Function.leftInverse_invFun S.inl_injective (Multiplicative.ofAdd w)

@[simp] theorem kernelValue_one : kernelValue S 1 = 0 := by
  rw [← embed_zero S, kernelValue_embed]

/-- The left factor-set convention: σ(s)σ(t)=i(c(s,t))σ(st). -/
def factorSet (s t : Q) : W :=
  kernelValue S (normalizedSection S s * normalizedSection S t *
    (normalizedSection S (s * t))⁻¹)

theorem embed_factorSet (s t : Q) :
    embed S (factorSet S s t) = normalizedSection S s * normalizedSection S t *
      (normalizedSection S (s * t))⁻¹ := by
  apply embed_kernelValue
  simp only [map_mul, map_inv, GroupExtension.Section.rightHom_section, mul_inv_cancel]

@[simp] theorem factorSet_one_left (t : Q) : factorSet S 1 t = 0 := by
  simp [factorSet]

@[simp] theorem factorSet_one_right (s : Q) : factorSet S s 1 = 0 := by
  simp [factorSet]

/-- The actual kernel coordinate in j=i(κ(j))σ(π(j)). -/
def coordinate (j : J) : W :=
  kernelValue S (j * (normalizedSection S (S.rightHom j))⁻¹)

theorem embed_coordinate (j : J) :
    embed S (coordinate S j) = j * (normalizedSection S (S.rightHom j))⁻¹ := by
  apply embed_kernelValue
  simp only [map_mul, map_inv, GroupExtension.Section.rightHom_section, mul_inv_cancel]

theorem embed_coordinate_mul_section (j : J) :
    embed S (coordinate S j) * normalizedSection S (S.rightHom j) = j := by
  rw [embed_coordinate]
  group

@[simp] theorem coordinate_embed (w : W) : coordinate S (embed S w) = w := by
  simp [coordinate]

@[simp] theorem coordinate_one : coordinate S 1 = 0 := by
  simp [coordinate]

variable (ρW : Representation k Q W) (ρV : Representation k Q V)

/-- The given Q-action is the actual conjugation action of the extension. -/
def CompatibleAction : Prop :=
  ∀ (j : J) (w : W), embed S (ρW (S.rightHom j) w) = j * embed S w * j⁻¹

variable (hcompat : CompatibleAction S ρW)

include hcompat in
theorem embed_action_section (s : Q) (w : W) :
    embed S (ρW s w) = normalizedSection S s * embed S w *
      (normalizedSection S s)⁻¹ := by
  simpa only [GroupExtension.Section.rightHom_section] using
    hcompat (normalizedSection S s) w

include hcompat in
theorem factorSet_cocycle (s t v : Q) :
    factorSet S (s * t) v + factorSet S s t =
      ρW s (factorSet S t v) + factorSet S s (t * v) := by
  rw [add_comm (factorSet S (s * t) v) (factorSet S s t)]
  apply embed_injective S
  simp only [embed_add, embed_action_section S ρW hcompat, embed_factorSet]
  rw [mul_assoc s t v]
  group

include hcompat in
theorem coordinate_mul (j l : J) :
    coordinate S (j * l) = coordinate S j + ρW (S.rightHom j) (coordinate S l) +
      factorSet S (S.rightHom j) (S.rightHom l) := by
  apply embed_injective S
  simp only [embed_add, embed_coordinate, embed_factorSet,
    embed_action_section S ρW hcompat, map_mul]
  group

/-- Postcomposition of the actual factor set by an actual equivariant linear map. -/
def coefficientCocycle (f : ρW.IntertwiningMap ρV) : cocycles₂ (Rep.of ρV) :=
  ⟨fun q => f (factorSet S q.1 q.2), (mem_cocycles₂_iff _).mpr (by
    intro s t v
    have h := congrArg f (factorSet_cocycle S ρW hcompat s t v)
    have hf : f (ρW s (factorSet S t v)) = ρV s (f (factorSet S t v)) :=
      congrArg (fun a : W →ₗ[k] V => a (factorSet S t v)) (f.isIntertwining' s)
    simpa only [map_add, hf] using h)⟩

@[simp] theorem coefficientCocycle_apply (f : ρW.IntertwiningMap ρV) (s t : Q) :
    coefficientCocycle S ρW ρV hcompat f (s, t) = f (factorSet S s t) := rfl

/-- The coefficient factor-set map is linear on the actual intertwiner space. -/
def coefficientCocycleLinear : (ρW.IntertwiningMap ρV) →ₗ[k] cocycles₂ (Rep.of ρV) where
  toFun := coefficientCocycle S ρW ρV hcompat
  map_add' f g := by ext q; rfl
  map_smul' a f := by ext q; rfl

/-- The actual ordinary H2 class, with no extension-class comparison premise. -/
def transgression : (ρW.IntertwiningMap ρV) →ₗ[k] groupCohomology (Rep.of ρV) 2 :=
  (H2π (Rep.of ρV)).hom.comp (coefficientCocycleLinear S ρW ρV hcompat)

theorem transgression_eq_zero_iff (f : ρW.IntertwiningMap ρV) :
    transgression S ρW ρV hcompat f = 0 ↔
      ∃ b : Q → V, ∀ s t : Q,
        ρV s (b t) - b (s * t) + b s = f (factorSet S s t) := by
  change H2π (Rep.of ρV) (coefficientCocycle S ρW ρV hcompat f) = 0 ↔ _
  rw [H2π_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro s t
    exact congrFun hb (s, t)
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    funext q
    exact hb q.1 q.2

/-- Zero class produces a crossed homomorphism on the actual extension group,
whose restriction is the specified kernel homomorphism. -/
theorem exists_crossedHom_of_transgression_eq_zero
    (f : ρW.IntertwiningMap ρV)
    (hf : transgression S ρW ρV hcompat f = 0) :
    ∃ d : J → V, d 1 = 0 ∧
      (∀ j l : J, d (j * l) = d j + ρV (S.rightHom j) (d l)) ∧
      (∀ w : W, d (embed S w) = f w) := by
  obtain ⟨b, hb⟩ := (transgression_eq_zero_iff S ρW ρV hcompat f).mp hf
  have hb1 : b 1 = 0 := by
    simpa only [map_one, Module.End.one_apply, one_mul, sub_self, zero_add,
      factorSet_one_left, map_zero] using hb 1 1
  let d : J → V := fun j => f (coordinate S j) + b (S.rightHom j)
  refine ⟨d, ?_, ?_, ?_⟩
  · simp [d, hb1]
  · intro j l
    have hfj : f (ρW (S.rightHom j) (coordinate S l)) =
        ρV (S.rightHom j) (f (coordinate S l)) :=
      congrArg (fun a : W →ₗ[k] V => a (coordinate S l))
        (f.isIntertwining' (S.rightHom j))
    dsimp only [d]
    rw [coordinate_mul S ρW hcompat]
    simp only [map_add, hfj, map_mul]
    rw [← hb (S.rightHom j) (S.rightHom l)]
    abel
  · intro w
    simp [d, hb1]

end Kourovka2135.AbelianExtensionCocycle

import Kourovka2135.FiniteAdjoinCard

/-! A finite generated subgroup preserved on its generators by an ambient
automorphism inherits an actual automorphism. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.FiniteAutomorphismRestriction

variable {G : Type*} [Group G]

theorem compatible_trans {E : Type*} [Group E] (f : E → G)
    (a₁ a₂ : MulAut E) (b₁ b₂ : MulAut G)
    (h₁ : ∀ g, f (a₁ g) = b₁ (f g)) (h₂ : ∀ g, f (a₂ g) = b₂ (f g))
    (g : E) : f ((a₁.trans a₂) g) = (b₁.trans b₂) (f g) := by
  change f (a₂ (a₁ g)) = b₂ (b₁ (f g))
  rw [h₂, h₁]

theorem compatible_symm {E : Type*} [Group E] (f : E → G)
    (a : MulAut E) (b : MulAut G) (h : ∀ g, f (a g) = b (f g))
    (g : E) : f (a.symm g) = b.symm (f g) := by
  apply b.injective
  rw [← h, a.apply_symm_apply, b.apply_symm_apply]

theorem preserves_closure (S : Set G) (e : MulAut G)
    (h : ∀ g ∈ S, e g ∈ Subgroup.closure S) :
    ∀ g ∈ Subgroup.closure S, e g ∈ Subgroup.closure S := by
  have hm : (Subgroup.closure S).map e.toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨a, ha, rfl⟩
    exact h a ha
  intro g hg
  exact hm (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)

def restrict (H : Subgroup G) [Finite H] (e : MulAut G)
    (h : ∀ g ∈ H, e g ∈ H) : MulAut H := by
  let f : H →* H :=
    { toFun := fun g => ⟨e g.val, h g.val g.property⟩
      map_one' := Subtype.ext e.map_one
      map_mul' := fun x y => Subtype.ext (e.map_mul x.val y.val) }
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun g : H => g.val) hab
  exact MulEquiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩

@[simp] theorem restrict_apply (H : Subgroup G) [Finite H] (e : MulAut G)
    (h : ∀ g ∈ H, e g ∈ H) (g : H) :
    ((restrict H e h g : H) : G) = e g.val := rfl

def closure (S : Set G) [Finite (Subgroup.closure S)] (e : MulAut G)
    (h : ∀ g ∈ S, e g ∈ Subgroup.closure S) : MulAut (Subgroup.closure S) :=
  restrict (Subgroup.closure S) e (preserves_closure S e h)

@[simp] theorem closure_apply (S : Set G) [Finite (Subgroup.closure S)] (e : MulAut G)
    (h : ∀ g ∈ S, e g ∈ Subgroup.closure S) (g : Subgroup.closure S) :
    ((closure S e h g : Subgroup.closure S) : G) = e g.val := rfl

end Kourovka2135.FiniteAutomorphismRestriction

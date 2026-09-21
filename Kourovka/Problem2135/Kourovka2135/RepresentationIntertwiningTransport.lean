import Kourovka2135.GroupCohomologyScalarRestriction
import Kourovka2135.RepresentationGroupEquiv

/-! Transport actual intertwiners through coefficient restriction and
an actual group isomorphism. All maps retain their underlying functions.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace Kourovka2135.RepresentationIntertwiningTransport

section Scalars
variable (K : Type u) [Field K] {E G V W : Type u} [Field E] [Algebra K E]
variable [Group G] [AddCommGroup V] [AddCommGroup W]
variable [Module E V] [Module K V] [IsScalarTower K E V]
variable [Module E W] [Module K W] [IsScalarTower K E W]
variable {ρ : Representation E G V} {τ : Representation E G W}

/-- An actual equivariant linear map remains equivariant upon scalar restriction. -/
def restrictIntertwiner (a : ρ.IntertwiningMap τ) :
    (GroupCohomologyScalarRestriction.restrict K ρ).IntertwiningMap
      (GroupCohomologyScalarRestriction.restrict K τ) where
  toLinearMap := a.toLinearMap.restrictScalars K
  isIntertwining' g := by
    ext v
    exact congrArg (fun l : V →ₗ[E] W => l v) (a.isIntertwining' g)

@[simp] theorem restrictIntertwiner_apply (a : ρ.IntertwiningMap τ) (v : V) :
    restrictIntertwiner K a v = a v := rfl

/-- Restricting the actual coefficient equivalence changes no function or group action. -/
def restrictEquiv (a : ρ.Equiv τ) :
    (GroupCohomologyScalarRestriction.restrict K ρ).Equiv
      (GroupCohomologyScalarRestriction.restrict K τ) :=
  (restrictIntertwiner K a.toIntertwiningMap).ofBijective a.toLinearEquiv.bijective

@[simp] theorem restrictEquiv_apply (a : ρ.Equiv τ) (v : V) :
    restrictEquiv K a v = a v := rfl
end Scalars

section Groups
variable {K G H V W : Type u} [Field K] [Group G] [Group H]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable {ρ : Representation K G V} {τ : Representation K G W}

/-- Surjectivity of the actual group isomorphism descends the equivariance equation. -/
def ofComp (e : H ≃* G)
    (a : Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom)) :
    ρ.IntertwiningMap τ where
  toLinearMap := a.toLinearMap
  isIntertwining' g := by
    obtain ⟨h, rfl⟩ := e.surjective g
    exact a.isIntertwining' h

@[simp] theorem ofComp_apply (e : H ≃* G)
    (a : Representation.IntertwiningMap (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom))
    (v : V) : ofComp e a v = a v := rfl

/-- An equivalence of pulled-back actions is an equivalence of the original actions. -/
def equivOfComp (e : H ≃* G)
    (a : Representation.Equiv (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom)) :
    ρ.Equiv τ :=
  (ofComp e a.toIntertwiningMap).ofBijective a.toLinearEquiv.bijective

@[simp] theorem equivOfComp_apply (e : H ≃* G)
    (a : Representation.Equiv (ρ.comp e.toMonoidHom) (τ.comp e.toMonoidHom))
    (v : V) : equivOfComp e a v = a v := rfl
end Groups

end Kourovka2135.RepresentationIntertwiningTransport

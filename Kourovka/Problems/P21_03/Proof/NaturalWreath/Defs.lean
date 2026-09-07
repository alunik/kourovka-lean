import Mathlib.GroupTheory.SemidirectProduct

/-!
# Permutational wreath products for an arbitrary top action

This is a standalone adaptation of
`Saxl/PermWreath/Defs.lean` from the local `SaxlCounterexamples`
development.  The construction is the semidirect product

`(ι → X) ⋊ Q`,

where `Q` acts on functions by contravariant reindexing.  In contrast to
Mathlib's `RegularWreathProduct`, the action of `Q` on `ι` is arbitrary.
-/

namespace Kourovka213

variable (X Q ι : Type*) [Group X] [Group Q] [MulAction Q ι]

/-- The action of `Q` on the base group `ι → X` by contravariant
reindexing: `(q • f) i = f (q⁻¹ • i)`. -/
def reindexAut : Q →* MulAut (ι → X) where
  toFun q := MulEquiv.arrowCongr (MulAction.toPerm q) (MulEquiv.refl X)
  map_one' := by
    ext f i
    simp
  map_mul' q r := by
    ext f i
    simp [mul_smul]

@[simp]
theorem reindexAut_apply (q : Q) (f : ι → X) (i : ι) :
    reindexAut X Q ι q f i = f (q⁻¹ • i) := rfl

/-- The permutational wreath product `X wr_ι Q` attached to the specified
action of `Q` on `ι`. -/
abbrev PermWreath := (ι → X) ⋊[reindexAut X Q ι] Q

namespace PermWreath

/-- The canonical inclusion of the base group. -/
def base : (ι → X) →* PermWreath X Q ι :=
  SemidirectProduct.inl

/-- The canonical inclusion of the top group. -/
def top : Q →* PermWreath X Q ι :=
  SemidirectProduct.inr

/-- The canonical projection onto the top group. -/
def rightHom : PermWreath X Q ι →* Q :=
  SemidirectProduct.rightHom

/-- Put one element of `X` in a single base coordinate. -/
noncomputable def coordinate (i : ι) : X →* PermWreath X Q ι := by
  classical
  exact (base X Q ι).comp (MonoidHom.mulSingle (fun _ : ι ↦ X) i)

@[simp]
theorem base_left (f : ι → X) : (base X Q ι f).left = f := rfl

@[simp]
theorem base_right (f : ι → X) : (base X Q ι f).right = 1 := rfl

@[simp]
theorem top_left (q : Q) : (top X Q ι q).left = 1 := rfl

@[simp]
theorem top_right (q : Q) : (top X Q ι q).right = q := rfl

@[simp]
theorem rightHom_apply (g : PermWreath X Q ι) : rightHom X Q ι g = g.right := rfl

/-- Extensionality in the base and top coordinates. -/
theorem ext {g h : PermWreath X Q ι} (hbase : g.left = h.left)
    (htop : g.right = h.right) : g = h :=
  SemidirectProduct.ext hbase htop

/-- The base-group inclusion is injective. -/
theorem base_injective : Function.Injective (base X Q ι) :=
  SemidirectProduct.inl_injective

/-- The top-group inclusion is injective. -/
theorem top_injective : Function.Injective (top X Q ι) :=
  SemidirectProduct.inr_injective

/-- Every single-coordinate map is injective. -/
theorem coordinate_injective (i : ι) : Function.Injective (coordinate X Q ι i) := by
  intro x y hxy
  have hleft := congrArg (fun g : PermWreath X Q ι ↦ g.left i) hxy
  simpa [coordinate] using hleft

@[simp]
theorem coordinate_left_apply [DecidableEq ι]
    (i j : ι) (x : X) : (coordinate X Q ι i x).left j = if j = i then x else 1 := by
  by_cases hji : j = i
  · subst j
    simp [coordinate]
  · simp [coordinate, hji]

@[simp]
theorem coordinate_right (i : ι) (x : X) : (coordinate X Q ι i x).right = 1 := by
  simp [coordinate]

/-- Top-group conjugation transports a single base coordinate with the top
action on `ι`. -/
theorem top_conj_coordinate [DecidableEq ι] (q : Q) (i : ι) (x : X) :
    top X Q ι q * coordinate X Q ι i x * (top X Q ι q)⁻¹ =
      coordinate X Q ι (q • i) x := by
  apply ext
  · funext j
    by_cases hj : j = q • i
    · subst j
      simp [coordinate]
    · have hj' : q⁻¹ • j ≠ i := by
        intro hqi
        apply hj
        rw [← hqi]
        simp
      simp [coordinate, hj, hj']
  · simp [coordinate]

end PermWreath

end Kourovka213

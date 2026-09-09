import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Abel

/-! Affine actions on finitely many coordinate fibres. -/

namespace Kourovka.P21_99

variable (K V : Type*) [Group K] [AddCommGroup V] [DistribMulAction K V]

def affineLinearAut : K →* MulAut (Multiplicative V) :=
  (MulAutMultiplicative V).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut K V)

abbrev AffineGroup := Multiplicative V ⋊[affineLinearAut K V] K

@[simp] theorem affineLinearAut_apply (k : K) (v : Multiplicative V) :
    (affineLinearAut K V k v).toAdd = k • v.toAdd := rfl

variable (I F : Type*) [AddCommGroup F] [MulAction K I]

/-- Surjective coordinate maps for an equivariant family of quotient fibres. -/
structure FiberSystem where
  project : I → V →+ F
  project_surjective : ∀ i, Function.Surjective (project i)
  linear : K → I → F →+ F
  equivariant : ∀ k i v,
    project (k • i) (k • v) = linear k i (project i v)

namespace FiberSystem

variable {K V I F} (D : FiberSystem K V I F)

@[simp] theorem linear_one (i : I) (x : F) : D.linear 1 i x = x := by
  obtain ⟨v, rfl⟩ := D.project_surjective i x
  simpa only [one_smul] using (D.equivariant 1 i v).symm

theorem linear_mul (k h : K) (i : I) (x : F) :
    D.linear (k * h) i x = D.linear k (h • i) (D.linear h i x) := by
  obtain ⟨v, rfl⟩ := D.project_surjective i x
  rw [← D.equivariant, ← D.equivariant, ← D.equivariant]
  simp only [mul_smul]

def act (g : AffineGroup K V) (p : I × F) : I × F :=
  (g.right • p.1, D.project (g.right • p.1) g.left.toAdd +
    D.linear g.right p.1 p.2)

@[simp] theorem one_act (p : I × F) : D.act 1 p = p := by
  rcases p with ⟨i, x⟩
  simp [act]

theorem mul_act (g h : AffineGroup K V) (p : I × F) :
    D.act (g * h) p = D.act g (D.act h p) := by
  rcases p with ⟨i, x⟩
  apply Prod.ext
  · exact mul_smul _ _ _
  · change D.project ((g.right * h.right) • i)
        (g.left.toAdd + g.right • h.left.toAdd) +
        D.linear (g.right * h.right) i x =
      D.project (g.right • (h.right • i)) g.left.toAdd +
        D.linear g.right (h.right • i)
          (D.project (h.right • i) h.left.toAdd + D.linear h.right i x)
    rw [mul_smul, map_add, D.equivariant, D.linear_mul, map_add]
    exact add_assoc _ _ _

@[instance_reducible] def affineMulAction : MulAction (AffineGroup K V) (I × F) where
  smul := D.act
  one_smul := D.one_act
  mul_smul := D.mul_act

theorem pretransitive [MulAction.IsPretransitive K I] :
    letI := D.affineMulAction
    MulAction.IsPretransitive (AffineGroup K V) (I × F) := by
  let := D.affineMulAction
  constructor
  intro x y
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K x.1 y.1
  obtain ⟨v, hv⟩ := D.project_surjective y.1 (y.2 - D.linear k x.1 x.2)
  refine ⟨⟨Multiplicative.ofAdd v, k⟩, ?_⟩
  change D.act ⟨Multiplicative.ofAdd v, k⟩ x = y
  apply Prod.ext
  · exact hk
  · change D.project (k • x.1) v + D.linear k x.1 x.2 = y.2
    rw [hk, hv]
    exact sub_add_cancel _ _

theorem act_source_iff (g : AffineGroup K V) (source target : I) (b : F) :
    D.act g (source, 0) = (target, b) ↔
      g.right • source = target ∧ D.project target g.left.toAdd = b := by
  constructor
  · intro h
    have hi : g.right • source = target := congrArg Prod.fst h
    refine ⟨hi, ?_⟩
    simpa [act, hi] using congrArg Prod.snd h
  · rintro ⟨hi, hv⟩
    apply Prod.ext
    · exact hi
    · simpa [act, hi] using hv

/-- A unique fixed point on one fibre and no fixed points on the others suffice. -/
theorem unique_fixed_of_fibres (g : AffineGroup K V) (regular : I)
    (hregular : g.right • regular = regular)
    (hunique : ∃! x : F,
      D.project regular g.left.toAdd + D.linear g.right regular x = x)
    (hother : ∀ i, g.right • i = i → i ≠ regular → ∀ x : F,
      D.project i g.left.toAdd + D.linear g.right i x ≠ x) :
    ∃! p : I × F, D.act g p = p := by
  obtain ⟨x, hx, huniq⟩ := hunique
  refine ⟨(regular, x), ?_, ?_⟩
  · apply Prod.ext hregular
    simpa [act, hregular] using hx
  · rintro ⟨i, y⟩ hy
    have hi : g.right • i = i := congrArg Prod.fst hy
    have hfix : D.project i g.left.toAdd + D.linear g.right i y = y := by
      simpa [act, hi] using congrArg Prod.snd hy
    have hir : i = regular := by
      by_contra hne
      exact hother i hi hne y hfix
    subst i
    exact Prod.ext rfl (huniq y hfix)

/-- The certificate case: at most two fixed fibres, one regular and one obstructed. -/
theorem unique_fixed_of_two_fibres (g : AffineGroup K V) (regular singular : I)
    (hregular : g.right • regular = regular)
    (hfixed : ∀ i, g.right • i = i → i = regular ∨ i = singular)
    (hunique : ∃! x : F,
      D.project regular g.left.toAdd + D.linear g.right regular x = x)
    (hsingular : ∀ x : F,
      D.project singular g.left.toAdd + D.linear g.right singular x ≠ x) :
    ∃! p : I × F, D.act g p = p := by
  apply D.unique_fixed_of_fibres g regular hregular hunique
  intro i hi hne
  rcases hfixed i hi with hir | his
  · exact False.elim (hne hir)
  · subst i
    exact hsingular

end FiberSystem

section FixedFibre

variable {F : Type*} [AddCommGroup F]

theorem affine_equation_iff (T : F →+ F) (z x : F) :
    z + T x = x ↔ x - T x = z := by
  constructor
  · intro h
    exact (eq_sub_iff_add_eq.mpr h).symm
  · intro h
    exact eq_sub_iff_add_eq.mp h.symm

/-- Bijectivity of `1-T` gives exactly one affine fixed point. -/
theorem unique_affine_fixed (T : F →+ F)
    (h : Function.Bijective (fun x => x - T x)) (z : F) :
    ∃! x : F, z + T x = x := by
  obtain ⟨x, hx⟩ := h.2 z
  refine ⟨x, (affine_equation_iff T z x).mpr hx, ?_⟩
  intro y hy
  exact h.1 (((affine_equation_iff T z y).mp hy).trans hx.symm)

theorem unique_affine_fixed_of_inverse (T R : F →+ F)
    (hleft : ∀ x, R (x - T x) = x)
    (hright : ∀ x, R x - T (R x) = x) (z : F) :
    ∃! x : F, z + T x = x := by
  apply unique_affine_fixed T _ z
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

/-- A covector fixed by T and nonzero on the translation obstructs a fixed point. -/
theorem no_affine_fixed_of_covector {R : Type*} [AddCommGroup R]
    (T : F →+ F) (ell : F →+ R) (z : F)
    (hinvariant : ∀ x, ell (T x) = ell x) (hnonzero : ell z ≠ 0) :
    ∀ x, z + T x ≠ x := by
  intro x hx
  have h := congrArg ell hx
  rw [map_add, hinvariant] at h
  apply hnonzero
  exact add_right_cancel (h.trans (zero_add (ell x)).symm)

/-- Transfer a singular-fibre obstruction from the prescribed target coordinates. -/
theorem no_affine_fixed_of_covector_transport
    {V R : Type*} [AddCommGroup V] [AddCommGroup R]
    (T : F →+ F) (P Q : V →+ F) (psi phi : F →+ R) (u b : V)
    (hinvariant : ∀ x, psi (T x) = psi x)
    (htransfer : ∀ v, psi (P v) = phi (Q v))
    (hnonzero : phi (Q b) ≠ 0) (htransport : Q u = Q b) :
    ∀ x, P u + T x ≠ x := by
  apply no_affine_fixed_of_covector T psi (P u) hinvariant
  rw [htransfer, htransport]
  exact hnonzero

end FixedFibre

end Kourovka.P21_99

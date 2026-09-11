import Kourovka.Problems.P21_68.Proof.Obstruction
import Kourovka.External.TauCeti.RepresentationTheory.Induction.FiniteDimensional

/-!
# Scalar coordinates on an induced representation

We use all group elements as evaluation coordinates in the coinduced model.
This needs no choice of a coset transversal in any proof statement.
-/

open CategoryTheory

namespace Kourovka.P21_68

universe u

variable {k G : Type u} [Field k] [Group G] {I : Subgroup G} [I.FiniteIndex]

/-- The comparison between finite-dimensional induction and the function model
of coinduction. -/
noncomputable def indFDRepCoindIso (V : FDRep k I) :
    (forget₂ (FDRep k G) (Rep k G)).obj (TauCeti.indFDRep V) ≅
      Rep.coind I.subtype ((forget₂ (FDRep k I) (Rep k I)).obj V) := by
  classical
  exact (TauCeti.indFDRepForgetIso V).trans (Rep.indCoindIso _)

/-- Evaluation at `g`, after identifying induction with coinduction. -/
noncomputable def inducedCoordinate (V : FDRep k I) (g : G) :
    TauCeti.indFDRep V →ₗ[k] V where
  toFun v := ((indFDRepCoindIso V).hom.hom.toLinearMap v).val g
  map_add' x y := congrArg (fun f => f.val g)
    ((indFDRepCoindIso V).hom.hom.toLinearMap.map_add x y)
  map_smul' c x := congrArg (fun f => f.val g)
    ((indFDRepCoindIso V).hom.hom.toLinearMap.map_smul c x)

/-- Evaluation coordinates jointly detect zero. -/
theorem inducedCoordinate_detects_zero (V : FDRep k I) (v : TauCeti.indFDRep V)
    (hv : ∀ g, inducedCoordinate V g v = 0) : v = 0 := by
  have h : (indFDRepCoindIso V).hom.hom.toLinearMap v = 0 := by
    apply Subtype.ext
    funext g
    exact hv g
  have h' := congrArg ((indFDRepCoindIso V).inv.hom.toLinearMap) h
  have hid := ConcreteCategory.congr_hom (indFDRepCoindIso V).hom_inv_id v
  change (indFDRepCoindIso V).inv.hom.toLinearMap
    ((indFDRepCoindIso V).hom.hom.toLinearMap v) = v at hid
  rw [hid, map_zero] at h'
  exact h'

/-- The action in these coordinates is right translation of the argument. -/
theorem inducedCoordinate_action (V : FDRep k I) (a g : G) (v : TauCeti.indFDRep V) :
    inducedCoordinate V g ((TauCeti.indFDRep V).ρ a v) =
      inducedCoordinate V (g * a) v := by
  have h := Rep.hom_comm_apply (indFDRepCoindIso V).hom a v
  have h' := congrArg (fun f => f.val g) h
  exact h'

/-- Functions in the coinduced model satisfy left equivariance under the
inducing subgroup. -/
theorem inducedCoordinate_subgroup_mul (V : FDRep k I) (i : I) (g : G)
    (v : TauCeti.indFDRep V) :
    inducedCoordinate V (i * g) v = V.ρ i (inducedCoordinate V g v) :=
  ((indFDRepCoindIso V).hom.hom.toLinearMap v).property i g

/-- If the inducing representation has scalar normal-subgroup character
`weight`, its induced coordinates have the conjugate characters. -/
theorem inducedCoordinate_scalar (N : Subgroup G) [N.Normal] (hNI : N ≤ I)
    (V : FDRep k I) (weight : N →* kˣ)
    (hscalar : ∀ n : N, ∀ v : V,
      V.ρ ((Subgroup.inclusion hNI) n) v = (weight n : k) • v)
    (n : N) (g : G) (v : TauCeti.indFDRep V) :
    inducedCoordinate V g ((TauCeti.indFDRep V).ρ n v) =
      (weight (MulAut.conjNormal g n) : k) • inducedCoordinate V g v := by
  rw [inducedCoordinate_action]
  have hmul : g * (n : G) =
      (((Subgroup.inclusion hNI) (MulAut.conjNormal g n) : I) : G) * g := by
    simp
  rw [hmul, inducedCoordinate_subgroup_mul, hscalar]

end Kourovka.P21_68

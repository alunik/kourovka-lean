import Kourovka2135.CentralClassThreeJacobi
import Kourovka2135.SuzukiEightPairingBound
import Kourovka2135.SuzukiRootDerivedTorus
import Kourovka2135.InvariantBiadditiveCoordinates

/-! The actual central triple-commutator pairing above the Suzuki root
group over F8, transported through its proved additive coordinates. Both
the scalar invariance and the scalar Jacobi equation are derived here. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.SuzukiEightCentralPairing

open SuzukiGeometry SuzukiRootDerivedCoordinates SuzukiRootDerivedTorus
open CentralClassThreePairing CentralClassThreeJacobi
open scoped IsMulCommutative

variable {P : Type*} [Group P]

local instance : IsElementaryAbelian 2 (commutator (U 1)) := derived_isElementaryAbelian 1

abbrev derivedCoordinates : Additive (commutator (U 1)) ≃+ K 1 := derivedAddEquiv 1 (by decide)
abbrev abelianCoordinates : Additive (Abelianization (U 1)) ≃+ K 1 :=
  abelianizationAddEquiv 1 (by decide)

variable (phi : P →* U 1) (hphi : Function.Surjective phi)
variable (hcentral : phi.ker ≤ Subgroup.center P)

/-- The actual descended pairing, with its actual center as additive target. -/
def nativePairing : Additive (commutator (U 1)) →+
    (Additive (Abelianization (U 1)) →+ Additive (Subgroup.center P)) where
  toFun d := (CentralClassThreeVanishing.pairingRightHom phi hphi hcentral
    (SuzukiRootDerivedCoordinates.commutator_le_center 1) d.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    exact congrFun (map_one (pairingHom phi hphi hcentral
      (SuzukiRootDerivedCoordinates.commutator_le_center 1))) a.toMul
  map_add' d e := by
    apply AddMonoidHom.ext
    intro a
    apply Additive.toMul.injective
    exact congrFun ((pairingHom phi hphi hcentral
      (SuzukiRootDerivedCoordinates.commutator_le_center 1)).map_mul d.toMul e.toMul) a.toMul

/-- The actual form in the proved two field coordinates. -/
def scalarForm : K 1 →+ (K 1 →+ Additive (Subgroup.center P)) :=
  InvariantBiadditiveCoordinates.reindex derivedCoordinates abelianCoordinates
    (nativePairing phi hphi hcentral)

theorem scalarForm_native (d : Additive (commutator (U 1)))
    (a : Additive (Abelianization (U 1))) :
    scalarForm phi hphi hcentral (derivedCoordinates d) (abelianCoordinates a) =
      nativePairing phi hphi hcentral d a := by
  simp only [scalarForm, InvariantBiadditiveCoordinates.reindex_apply,
    AddEquiv.symm_apply_apply]

/-- Evaluating the scalar form on actual lifted inputs recovers their commutator. -/
theorem scalarForm_lift_eval (d : commutator P) (x : P) :
    ((scalarForm phi hphi hcentral
      (derivedCoordinates (Additive.ofMul (derivedMap phi hphi d)))
      (abelianCoordinates (Additive.ofMul (Abelianization.of (phi x))))).toMul : P) =
      paperCommutator (d : P) x := by
  rw [scalarForm_native]
  exact pairingHom_apply_lifts phi hphi hcentral
    (SuzukiRootDerivedCoordinates.commutator_le_center 1) d x

@[simp] theorem derivedCoordinates_zero (d : K 1) :
    derivedCoordinates (Additive.ofMul
      ⟨coord 1 0 d, zero_coord_mem_commutator 1 (by decide) d⟩) = d := by
  change (derivedEquiv 1 (by decide)
    ⟨coord 1 0 d, zero_coord_mem_commutator 1 (by decide) d⟩).toAdd = d
  rw [derivedEquiv_zero]
  rfl

@[simp] theorem abelianCoordinates_coord (a b : K 1) :
    abelianCoordinates (Additive.ofMul (Abelianization.of (coord 1 a b))) = a := by
  change (abelianizationEquiv 1 (by decide) (Abelianization.of (coord 1 a b))).toAdd = a
  rw [abelianizationEquiv_of, firstHom_coord]
  rfl

/-- The coordinate Jacobi input is derived from actual root multiplication. -/
theorem derivedCoordinates_commutator_lifts (a b : K 1) (x y : P)
    (hx : phi x = coord 1 a 0) (hy : phi y = coord 1 b 0) :
    derivedCoordinates (Additive.ofMul (derivedMap phi hphi
      ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩)) =
        a * b ^ 4 + b * a ^ 4 := by
  have he : derivedMap phi hphi
      ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩ =
        ⟨coord 1 0 (a * b ^ 4 + b * a ^ 4),
          zero_coord_mem_commutator 1 (by decide) _⟩ := by
    apply Subtype.ext
    change phi (paperCommutator x y) = coord 1 0 (a * b ^ 4 + b * a ^ 4)
    rw [map_paperCommutator, hx, hy, paperCommutator_coord,
      SuzukiTorusMovingRank.tits_apply, SuzukiTorusMovingRank.tits_apply]
    norm_num
  rw [he, derivedCoordinates_zero]

theorem scalarForm_triple_lifts (a b c : K 1) (x y z : P)
    (hx : phi x = coord 1 a 0) (hy : phi y = coord 1 b 0) (hz : phi z = coord 1 c 0) :
    ((scalarForm phi hphi hcentral (a * b ^ 4 + b * a ^ 4) c).toMul : P) =
      paperCommutator (paperCommutator x y) z := by
  have hc : abelianCoordinates (Additive.ofMul (Abelianization.of (phi z))) = c := by
    rw [hz, abelianCoordinates_coord]
  rw [← derivedCoordinates_commutator_lifts phi hphi a b x y hx hy, ← hc]
  exact scalarForm_lift_eval phi hphi hcentral
    ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩ z

/-- The actual scalar form satisfies Jacobi, with no assumed scalar equation. -/
theorem scalarForm_jacobi (a b c : K 1) :
    scalarForm phi hphi hcentral (a * b ^ 4 + b * a ^ 4) c +
      scalarForm phi hphi hcentral (b * c ^ 4 + c * b ^ 4) a +
      scalarForm phi hphi hcentral (c * a ^ 4 + a * c ^ 4) b = 0 := by
  obtain ⟨x, hx⟩ := hphi (coord 1 a 0)
  obtain ⟨y, hy⟩ := hphi (coord 1 b 0)
  obtain ⟨z, hz⟩ := hphi (coord 1 c 0)
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((scalarForm phi hphi hcentral _ _).toMul : P) *
    ((scalarForm phi hphi hcentral _ _).toMul : P) *
    ((scalarForm phi hphi hcentral _ _).toMul : P) = 1
  rw [scalarForm_triple_lifts phi hphi hcentral a b c x y z hx hy hz,
    scalarForm_triple_lifts phi hphi hcentral b c a y z x hy hz hx,
    scalarForm_triple_lifts phi hphi hcentral c a b z x y hz hx hy]
  exact paperCommutator_jacobi phi hphi hcentral
    (SuzukiRootDerivedCoordinates.commutator_le_center 1) x y z

variable (alpha : (K 1)ˣ → P ≃* P)
variable (hcompat : ∀ t x, phi (alpha t x) = rootTorusAut 1 t (phi x))
variable (hfix : ∀ t x, x ∈ phi.ker → alpha t x = x)

include hcompat hfix in
theorem nativePairing_invariant (u : (K 1)ˣ)
    (d : Additive (commutator (U 1))) (a : Additive (Abelianization (U 1))) :
    nativePairing phi hphi hcentral
      (Additive.ofMul (derivedTorusAction 1 u d.toMul))
      (Additive.ofMul (abelianizationTorusAction 1 u a.toMul)) =
        nativePairing phi hphi hcentral d a := by
  apply Additive.toMul.injective
  exact pairingHom_invariant phi hphi hcentral
    (SuzukiRootDerivedCoordinates.commutator_le_center 1) (alpha u) (rootTorusAut 1 u)
    (hcompat u) (hfix u) d.toMul a.toMul

include hcompat hfix in
/-- The weights five and one are the actual split-torus conjugation weights. -/
theorem scalarForm_invariant (u : (K 1)ˣ) (d a : K 1) :
    scalarForm phi hphi hcentral ((u : K 1) ^ 5 * d) ((u : K 1) * a) =
      scalarForm phi hphi hcentral d a := by
  have hd : derivedCoordinates.symm ((u : K 1) ^ 5 * d) =
      Additive.ofMul (derivedTorusAction 1 u (derivedCoordinates.symm d).toMul) := by
    apply derivedCoordinates.injective
    rw [derivedCoordinates.apply_symm_apply, derivedAddEquiv_torus,
      derivedCoordinates.apply_symm_apply]
    norm_num
  have ha : abelianCoordinates.symm ((u : K 1) * a) =
      Additive.ofMul (abelianizationTorusAction 1 u (abelianCoordinates.symm a).toMul) := by
    apply abelianCoordinates.injective
    rw [abelianCoordinates.apply_symm_apply, abelianizationAddEquiv_torus,
      abelianCoordinates.apply_symm_apply]
  simp only [scalarForm, InvariantBiadditiveCoordinates.reindex_apply, hd, ha]
  exact nativePairing_invariant phi hphi hcentral alpha hcompat hfix u
    (derivedCoordinates.symm d) (abelianCoordinates.symm a)

end Kourovka2135.SuzukiEightCentralPairing

import Kourovka2135.ClassTwoCommutators
import Kourovka2135.RelativeCongruence
import Mathlib.GroupTheory.Abelianization.Defs

/-! The actual class-three commutator pairing of a central extension of a
class-two group. The pairing descends to the derived subgroup and
abelianization of the quotient; its values lie in the actual central kernel.
No bound on that kernel or character pushout is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.CentralClassThreePairing

open scoped IsMulCommutative

variable {G : Type u} {Q : Type v} [Group G] [Group Q]

theorem abelianization_surjective :
    Function.Surjective (Abelianization.of : Q →* Abelianization Q) :=
  QuotientGroup.mk'_surjective (commutator Q)

theorem map_commutator_of_surjective (pi : G →* Q)
    (hpi : Function.Surjective pi) :
    (commutator G).map pi = commutator Q := by
  simp only [commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective pi hpi]

/-- The actual map on derived subgroups, with no recognition premise. -/
def derivedMap (pi : G →* Q) (hpi : Function.Surjective pi) :
    commutator G →* commutator Q where
  toFun c := ⟨pi (c : G), by
    rw [← map_commutator_of_surjective pi hpi]
    exact Subgroup.mem_map_of_mem pi c.property⟩
  map_one' := Subtype.ext (map_one pi)
  map_mul' _ _ := Subtype.ext (map_mul pi _ _)

@[simp] theorem derivedMap_coe (pi : G →* Q) (hpi : Function.Surjective pi)
    (c : commutator G) : (derivedMap pi hpi c : Q) = pi (c : G) := rfl

theorem derivedMap_surjective (pi : G →* Q) (hpi : Function.Surjective pi) :
    Function.Surjective (derivedMap pi hpi) := by
  intro d
  have hd : (d : Q) ∈ (commutator G).map pi := by
    rw [map_commutator_of_surjective pi hpi]
    exact d.property
  obtain ⟨c, hc, hcd⟩ := hd
  exact ⟨⟨c, hc⟩, Subtype.ext hcd⟩

variable (pi : G →* Q) (hpi : Function.Surjective pi)
variable (hker : pi.ker ≤ Subgroup.center G)
variable (hQ : commutator Q ≤ Subgroup.center Q)

include hpi hQ in
theorem commutator_mem_kernel (c : commutator G) (x : G) :
    paperCommutator (c : G) x ∈ pi.ker := by
  change pi (paperCommutator (c : G) x) = 1
  rw [map_paperCommutator]
  apply (paperCommutator_eq_one_iff _ _).mpr
  exact (show Commute (pi x) (pi (c : G)) from
    Subgroup.mem_center_iff.mp (hQ (derivedMap pi hpi c).property) (pi x)).symm

include pi hpi hker hQ in
theorem commutator_mem_center (c : commutator G) (x : G) :
    paperCommutator (c : G) x ∈ Subgroup.center G :=
  hker (commutator_mem_kernel pi hpi hQ c x)

/-- Fixing the derived input gives an actual homomorphism to the center. -/
def rightHom (c : commutator G) : G →* Subgroup.center G where
  toFun x := ⟨paperCommutator (c : G) x,
    commutator_mem_center pi hpi hker hQ c x⟩
  map_one' := Subtype.ext (by simp [paperCommutator])
  map_mul' x y := Subtype.ext
    (paperCommutator_mul_right_of_central (c : G) x y
      (commutator_mem_center pi hpi hker hQ c x))

/-- Centrality of the kernel permits descent of the second input to Q. -/
def rightQuotientHom (c : commutator G) : Q →* Subgroup.center G :=
  pi.liftOfSurjective hpi ⟨rightHom pi hpi hker hQ c, by
    intro x hx
    apply Subtype.ext
    change paperCommutator (c : G) x = 1
    exact (paperCommutator_eq_one_iff _ _).mpr
      (Subgroup.mem_center_iff.mp (hker hx) (c : G))⟩

theorem rightQuotientHom_apply (c : commutator G) (x : G) :
    (rightQuotientHom pi hpi hker hQ c (pi x) : G) =
      paperCommutator (c : G) x := by
  simp only [rightQuotientHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, rightHom]
  rfl

/-- Descent to the actual abelianization follows from the abelian target.
This also proves the needed independence from derived-subgroup lifts. -/
def rightAbelianizationHom (c : commutator G) :
    Abelianization Q →* Subgroup.center G :=
  Abelianization.lift (rightQuotientHom pi hpi hker hQ c)

theorem rightAbelianizationHom_apply (c : commutator G) (x : G) :
    (rightAbelianizationHom pi hpi hker hQ c
      (Abelianization.of (pi x)) : G) = paperCommutator (c : G) x :=
  rightQuotientHom_apply pi hpi hker hQ c x

def functionHom : commutator G →* (Abelianization Q → Subgroup.center G) where
  toFun c := rightAbelianizationHom pi hpi hker hQ c
  map_one' := by
    funext a
    obtain ⟨y, rfl⟩ := abelianization_surjective a
    obtain ⟨x, rfl⟩ := hpi y
    apply Subtype.ext
    change (rightAbelianizationHom pi hpi hker hQ 1
      (Abelianization.of (pi x)) : G) = 1
    rw [rightAbelianizationHom_apply]
    simp [paperCommutator]
  map_mul' c d := by
    funext a
    obtain ⟨y, rfl⟩ := abelianization_surjective a
    obtain ⟨x, rfl⟩ := hpi y
    apply Subtype.ext
    change (rightAbelianizationHom pi hpi hker hQ (c * d)
      (Abelianization.of (pi x)) : G) =
        (rightAbelianizationHom pi hpi hker hQ c
          (Abelianization.of (pi x)) : G) *
        (rightAbelianizationHom pi hpi hker hQ d
          (Abelianization.of (pi x)) : G)
    rw [rightAbelianizationHom_apply, rightAbelianizationHom_apply,
      rightAbelianizationHom_apply]
    exact paperCommutator_mul_left_of_central (c : G) (d : G) x
      (commutator_mem_center pi hpi hker hQ c x)

/-- The actual pairing on Q' times Q-ab, presented as a homomorphism in
the first input. Multiplicativity in the second input is proved below. -/
def pairingHom : commutator Q →* (Abelianization Q → Subgroup.center G) :=
  (derivedMap pi hpi).liftOfSurjective (derivedMap_surjective pi hpi)
    ⟨functionHom pi hpi hker hQ, by
      intro c hc
      change derivedMap pi hpi c = 1 at hc
      have hcKer : (c : G) ∈ pi.ker := congrArg Subtype.val hc
      funext a
      obtain ⟨y, rfl⟩ := abelianization_surjective a
      obtain ⟨x, rfl⟩ := hpi y
      apply Subtype.ext
      change (rightAbelianizationHom pi hpi hker hQ c
        (Abelianization.of (pi x)) : G) = 1
      rw [rightAbelianizationHom_apply]
      exact (paperCommutator_eq_one_iff _ _).mpr
        (show Commute x (c : G) from
          Subgroup.mem_center_iff.mp (hker hcKer) x).symm⟩

theorem pairingHom_apply_derivedMap (c : commutator G) :
    pairingHom pi hpi hker hQ (derivedMap pi hpi c) =
      rightAbelianizationHom pi hpi hker hQ c := by
  simp only [pairingHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, functionHom]
  rfl

theorem pairingHom_apply_lifts (c : commutator G) (x : G) :
    (pairingHom pi hpi hker hQ (derivedMap pi hpi c)
      (Abelianization.of (pi x)) : G) = paperCommutator (c : G) x := by
  rw [pairingHom_apply_derivedMap]
  exact rightAbelianizationHom_apply pi hpi hker hQ c x

theorem pairingHom_mul_right (d : commutator Q) (a b : Abelianization Q) :
    pairingHom pi hpi hker hQ d (a * b) =
      pairingHom pi hpi hker hQ d a * pairingHom pi hpi hker hQ d b := by
  obtain ⟨c, rfl⟩ := derivedMap_surjective pi hpi d
  rw [pairingHom_apply_derivedMap]
  exact (rightAbelianizationHom pi hpi hker hQ c).map_mul a b

theorem pairingHom_mem_kernel (d : commutator Q) (a : Abelianization Q) :
    (pairingHom pi hpi hker hQ d a : G) ∈ pi.ker := by
  obtain ⟨c, rfl⟩ := derivedMap_surjective pi hpi d
  obtain ⟨y, rfl⟩ := abelianization_surjective a
  obtain ⟨x, rfl⟩ := hpi y
  rw [pairingHom_apply_lifts]
  exact commutator_mem_kernel pi hpi hQ c x

/-- Any proof that the actual pairing vanishes proves centrality of G'. -/
theorem commutator_le_center_of_pairing_eq_one
    (hpair : ∀ (d : commutator Q) (a : Abelianization Q),
      pairingHom pi hpi hker hQ d a = 1) :
    commutator G ≤ Subgroup.center G := by
  intro c hc
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hh := congrArg (fun z : Subgroup.center G => (z : G))
    (hpair (derivedMap pi hpi ⟨c, hc⟩) (Abelianization.of (pi x)))
  rw [pairingHom_apply_lifts] at hh
  exact ((paperCommutator_eq_one_iff c x).mp hh).eq.symm

/-- If an automorphism fixes the actual kernel, the pairing is invariant
under its induced action on the two quotient factors. -/
theorem pairingHom_invariant (alpha : G ≃* G) (beta : Q ≃* Q)
    (hcompat : ∀ x, pi (alpha x) = beta (pi x))
    (hfix : ∀ x ∈ pi.ker, alpha x = x)
    (d : commutator Q) (a : Abelianization Q) :
    pairingHom pi hpi hker hQ
      (derivedMap beta.toMonoidHom beta.surjective d)
      (Abelianization.map beta.toMonoidHom a) = pairingHom pi hpi hker hQ d a := by
  obtain ⟨c, rfl⟩ := derivedMap_surjective pi hpi d
  obtain ⟨y, rfl⟩ := abelianization_surjective a
  obtain ⟨x, rfl⟩ := hpi y
  let c' : commutator G := derivedMap alpha.toMonoidHom alpha.surjective c
  have hc' : derivedMap beta.toMonoidHom beta.surjective (derivedMap pi hpi c) =
      derivedMap pi hpi c' := by
    apply Subtype.ext
    exact (hcompat (c : G)).symm
  have hx' : pi (alpha x) = beta.toMonoidHom (pi x) := hcompat x
  rw [hc', Abelianization.map_of, ← hx']
  apply Subtype.ext
  rw [pairingHom_apply_lifts, pairingHom_apply_lifts]
  change paperCommutator (alpha.toMonoidHom (c : G)) (alpha.toMonoidHom x) =
    paperCommutator (c : G) x
  rw [← map_paperCommutator alpha.toMonoidHom]
  exact hfix _ (commutator_mem_kernel pi hpi hQ c x)

end Kourovka2135.CentralClassThreePairing

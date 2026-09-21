import Kourovka2135.ClassTwoCommutators
import Kourovka2135.RelativeCongruence
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! The actual commutator pairing of a class-two group on an abelian
quotient with central kernel. Its values generate the actual derived
subgroup. No presentation or abstract tensor quotient is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v w
namespace Kourovka2135.CentralClassTwoAbelianPairing

open scoped IsMulCommutative commutatorElement

variable {G : Type u} {Q : Type v} [Group G] [CommGroup Q]
variable (psi : G →* Q) (hpsi : Function.Surjective psi)
variable (hker : psi.ker ≤ Subgroup.center G) (hD : commutator G ≤ Subgroup.center G)

include hD in
theorem commutator_isMulCommutative : IsMulCommutative (commutator G) := by
  refine ⟨⟨?_⟩⟩
  intro x y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hD y.property) x.val

def rightQuotientHom (x : G) : Q →* commutator G :=
  psi.liftOfSurjective hpsi ⟨centralCommutatorRightHom hD x, by
    intro y hy
    apply Subtype.ext
    change paperCommutator x y = 1
    exact (paperCommutator_eq_one_iff _ _).mpr
      (Subgroup.mem_center_iff.mp (hker hy) x)⟩

theorem rightQuotientHom_apply (x y : G) :
    rightQuotientHom psi hpsi hker hD x (psi y) =
      ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩ := by
  simp only [rightQuotientHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, centralCommutatorRightHom]
  rfl

def functionHom : G →* (Q → commutator G) where
  toFun x := rightQuotientHom psi hpsi hker hD x
  map_one' := by
    funext q
    obtain ⟨y, rfl⟩ := hpsi q
    apply Subtype.ext
    change (rightQuotientHom psi hpsi hker hD 1 (psi y) : G) = 1
    rw [rightQuotientHom_apply]
    simp [paperCommutator]
  map_mul' x z := by
    funext q
    obtain ⟨y, rfl⟩ := hpsi q
    apply Subtype.ext
    change (rightQuotientHom psi hpsi hker hD (x * z) (psi y) : G) =
      (rightQuotientHom psi hpsi hker hD x (psi y) : G) *
        (rightQuotientHom psi hpsi hker hD z (psi y) : G)
    rw [rightQuotientHom_apply, rightQuotientHom_apply, rightQuotientHom_apply]
    exact paperCommutator_mul_left_of_central x z y
      (hD (paperCommutator_mem_commutator x y))

def pairingHom : Q →* (Q → commutator G) :=
  psi.liftOfSurjective hpsi ⟨functionHom psi hpsi hker hD, by
    intro x hx
    funext q
    obtain ⟨y, rfl⟩ := hpsi q
    apply Subtype.ext
    change (rightQuotientHom psi hpsi hker hD x (psi y) : G) = 1
    rw [rightQuotientHom_apply]
    exact (paperCommutator_eq_one_iff _ _).mpr
      (show Commute y x from Subgroup.mem_center_iff.mp (hker hx) y).symm⟩

theorem pairingHom_apply (x : G) :
    pairingHom psi hpsi hker hD (psi x) = rightQuotientHom psi hpsi hker hD x := by
  simp only [pairingHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, functionHom]
  rfl

theorem pairingHom_apply_lifts (x y : G) :
    pairingHom psi hpsi hker hD (psi x) (psi y) =
      ⟨paperCommutator x y, paperCommutator_mem_commutator x y⟩ := by
  rw [pairingHom_apply]
  exact rightQuotientHom_apply psi hpsi hker hD x y

theorem pairingHom_mul_right (q r s : Q) :
    pairingHom psi hpsi hker hD q (r * s) =
      pairingHom psi hpsi hker hD q r * pairingHom psi hpsi hker hD q s := by
  obtain ⟨x, rfl⟩ := hpsi q
  rw [pairingHom_apply]
  exact (rightQuotientHom psi hpsi hker hD x).map_mul r s

def pairingRightHom (q : Q) : Q →* commutator G :=
  MonoidHom.mk' (pairingHom psi hpsi hker hD q)
    (pairingHom_mul_right psi hpsi hker hD q)

/-- Functoriality under actual compatible automorphisms. -/
theorem pairingHom_equivariant (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ x, psi (alpha x) = beta (psi x)) (q r : Q) :
    pairingHom psi hpsi hker hD (beta q) (beta r) =
      MulAut.characteristic (commutator G) alpha (pairingHom psi hpsi hker hD q r) := by
  obtain ⟨x, rfl⟩ := hpsi q
  obtain ⟨y, rfl⟩ := hpsi r
  rw [← hcompat, ← hcompat, pairingHom_apply_lifts, pairingHom_apply_lifts]
  apply Subtype.ext
  exact (map_paperCommutator alpha.toMonoidHom x y).symm

def pairingValues : Set (commutator G) :=
  Set.range (fun qr : Q × Q => pairingHom psi hpsi hker hD qr.1 qr.2)

/-- The actual pairing values generate the whole actual derived subgroup. -/
theorem closure_pairingValues : Subgroup.closure (pairingValues psi hpsi hker hD) = ⊤ := by
  let H : Subgroup (commutator G) := Subgroup.closure (pairingValues psi hpsi hker hD)
  have hgen : commutator G ≤ H.map (commutator G).subtype := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    have he : ⁅x, y⁆ = paperCommutator x⁻¹ y⁻¹ := by
      simp only [paperCommutator, commutatorElement_def, inv_inv]
    rw [he]
    refine Subgroup.mem_map.mpr ⟨pairingHom psi hpsi hker hD (psi x⁻¹) (psi y⁻¹), ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨(psi x⁻¹, psi y⁻¹), rfl⟩
    · exact congrArg Subtype.val (pairingHom_apply_lifts psi hpsi hker hD x⁻¹ y⁻¹)
  apply top_unique
  intro d _
  obtain ⟨e, he, hed⟩ := (Subgroup.mem_map.mp (hgen d.property))
  have heq : e = d := Subtype.ext hed
  exact heq ▸ he

theorem hom_eq_one_of_pairing {H : Type w} [Group H] (f : commutator G →* H)
    (hf : ∀ q r : Q, f (pairingHom psi hpsi hker hD q r) = 1) :
    ∀ d : commutator G, f d = 1 := by
  have hk : Subgroup.closure (pairingValues psi hpsi hker hD) ≤ f.ker := by
    rw [Subgroup.closure_le]
    rintro d ⟨⟨q, r⟩, rfl⟩
    exact hf q r
  rw [closure_pairingValues] at hk
  intro d
  exact hk (Subgroup.mem_top d)

theorem pairing_square [IsElementaryAbelian 2 Q] (q r : Q) :
    pairingHom psi hpsi hker hD q r ^ 2 = 1 := by
  change (pairingRightHom psi hpsi hker hD q r) ^ 2 = 1
  rw [← map_pow]
  have hr : r ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 Q) r
  rw [hr, map_one]

include psi hpsi hker hD in
/-- Elementary abelianity is derived from the generating pairing and the
actual quotient's exponent; it need not be an application assumption. -/
theorem derived_isElementaryAbelian [IsElementaryAbelian 2 Q] :
    IsElementaryAbelian 2 (commutator G) := by
  let : IsMulCommutative (commutator G) := commutator_isMulCommutative hD
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  exact hom_eq_one_of_pairing psi hpsi hker hD (powMonoidHom 2)
    (pairing_square psi hpsi hker hD)

section Additive
variable [IsMulCommutative (commutator G)]

def biadditive : Additive Q →+ (Additive Q →+ Additive (commutator G)) where
  toFun q := (pairingRightHom psi hpsi hker hD q.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro r
    change pairingHom psi hpsi hker hD 1 r.toMul = 1
    exact congrFun (map_one (pairingHom psi hpsi hker hD)) r.toMul
  map_add' q r := by
    apply AddMonoidHom.ext
    intro s
    change pairingHom psi hpsi hker hD (q.toMul * r.toMul) s.toMul =
      pairingHom psi hpsi hker hD q.toMul s.toMul *
        pairingHom psi hpsi hker hD r.toMul s.toMul
    exact congrFun ((pairingHom psi hpsi hker hD).map_mul q.toMul r.toMul) s.toMul

@[simp] theorem biadditive_apply (q r : Additive Q) :
    biadditive psi hpsi hker hD q r =
      Additive.ofMul (pairingHom psi hpsi hker hD q.toMul r.toMul) := rfl

theorem biadditive_equivariant (alpha : MulAut G) (beta : MulAut Q)
    (hcompat : ∀ x, psi (alpha x) = beta (psi x)) (q r : Additive Q) :
    biadditive psi hpsi hker hD (beta.toAdditive q) (beta.toAdditive r) =
      (MulAut.characteristic (commutator G) alpha).toAdditive
        (biadditive psi hpsi hker hD q r) :=
  pairingHom_equivariant psi hpsi hker hD alpha beta hcompat q.toMul r.toMul

theorem addHom_eq_zero_of_pairing {A : Type w} [AddCommGroup A]
    (f : Additive (commutator G) →+ A)
    (hf : ∀ q r : Additive Q, f (biadditive psi hpsi hker hD q r) = 0) : f = 0 := by
  apply AddMonoidHom.ext
  intro d
  exact hom_eq_one_of_pairing psi hpsi hker hD f.toMultiplicativeRight
    (fun q r => hf (Additive.ofMul q) (Additive.ofMul r)) d.toMul

end Additive
end Kourovka2135.CentralClassTwoAbelianPairing

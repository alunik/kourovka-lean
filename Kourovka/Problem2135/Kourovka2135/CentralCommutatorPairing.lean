import Kourovka2135.ClassTwoCommutators

/-! The alternating, nondegenerate commutator pairing on the center quotient. -/

set_option autoImplicit false
universe u
namespace Kourovka2135
variable {G : Type u} [Group G]
variable (hD : commutator G ≤ Subgroup.center G)

def centralCommutatorFunctionHom : G →* ((G ⧸ Subgroup.center G) → commutator G) where
  toFun x := centralCommutatorRightQuotientHom hD x
  map_one' := by
    funext y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    apply Subtype.ext
    change paperCommutator 1 b = 1
    simp [paperCommutator]
  map_mul' x z := by
    funext y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    apply Subtype.ext
    change paperCommutator (x * z) b = paperCommutator x b * paperCommutator z b
    exact paperCommutator_mul_left_of_central x z b (hD (paperCommutator_mem_commutator x b))

def centralCommutatorPairingHom :
    (G ⧸ Subgroup.center G) →* ((G ⧸ Subgroup.center G) → commutator G) :=
  QuotientGroup.lift (Subgroup.center G) (centralCommutatorFunctionHom hD) (by
    intro x hx
    funext y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
    apply Subtype.ext
    change paperCommutator x b = 1
    exact (paperCommutator_eq_one_iff _ _).mpr
      (show Commute b x from Subgroup.mem_center_iff.mp hx b).symm)

@[simp]
theorem centralCommutatorPairingHom_apply_mk (a b : G) :
    (centralCommutatorPairingHom hD (QuotientGroup.mk' (Subgroup.center G) a)
      (QuotientGroup.mk' (Subgroup.center G) b) : G) = paperCommutator a b := rfl

theorem centralCommutatorPairingHom_mul_right
    (x y z : G ⧸ Subgroup.center G) :
    centralCommutatorPairingHom hD x (y * z) =
      centralCommutatorPairingHom hD x y * centralCommutatorPairingHom hD x z := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  exact (centralCommutatorRightQuotientHom hD a).map_mul y z

theorem centralCommutatorPairingHom_self (x : G ⧸ Subgroup.center G) :
    centralCommutatorPairingHom hD x x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  apply Subtype.ext
  change paperCommutator a a = 1
  simp [paperCommutator]

theorem centralCommutatorPairingHom_swap (x y : G ⧸ Subgroup.center G) :
    centralCommutatorPairingHom hD x y = (centralCommutatorPairingHom hD y x)⁻¹ := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) y
  apply Subtype.ext
  exact (paperCommutator_inv_swap b a).symm

theorem centralCommutatorPairingHom_nondegenerate {x : G ⧸ Subgroup.center G}
    (h : ∀ y, centralCommutatorPairingHom hD x y = 1) : x = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_center_iff.mpr
  intro b
  have hab : paperCommutator a b = 1 :=
    congrArg Subtype.val (h (QuotientGroup.mk' (Subgroup.center G) b))
  exact ((paperCommutator_eq_one_iff _ _).mp hab).eq.symm

end Kourovka2135

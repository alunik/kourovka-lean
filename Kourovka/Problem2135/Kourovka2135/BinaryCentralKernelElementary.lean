import Kourovka2135.CentralPGroupTransfer
import Kourovka2135.SLTwoUnipotent

/-! Central binary kernels of finite perfect groups above actual SL2 groups
in characteristic two are elementary abelian. The proof uses transfer to the
preimage of the actual root subgroup, whose index is odd and whose elements
commute and square to one. No Frattini, simplicity, or cohomology premise is
used.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.BinaryCentralKernelElementary

open scoped IsMulCommutative

variable {F : Type v} [Field F] [CharP F 2]

/-- The actual root subgroup is elementary abelian in characteristic two. -/
theorem unip_isElementaryAbelian : IsElementaryAbelian 2 (SLTwo.Unip F) := by
  refine {
    toIsMulCommutative := ?_
    exponent_dvd_p := ?_ }
  · change IsMulCommutative (SLTwo.uniHom F).range
    infer_instance
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    obtain ⟨t, ht⟩ := x.property
    have ht2 : t ^ 2 = (1 : Multiplicative F) := by
      apply Multiplicative.toAdd.injective
      change 2 • t.toAdd = 0
      simp only [two_nsmul, CharTwo.add_self_eq_zero]
    apply Subtype.ext
    change (x : SLTwo.SL2 F) ^ 2 = 1
    rw [← ht, ← map_pow, ht2, map_one]

variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]
variable [Finite F]

/-- An actual surjection onto SL2 in characteristic two has elementary-abelian
central binary kernel. The field cardinality is arbitrary. -/
theorem isElementaryAbelian_kernel
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (hcentral : pi.ker ≤ Subgroup.center G) :
    IsElementaryAbelian 2 pi.ker := by
  let P : Subgroup G := (SLTwo.Unip F).comap pi
  have hindex : Odd P.index := by
    dsimp only [P]
    rw [(SLTwo.Unip F).index_comap_of_surjective hpi]
    exact SLTwo.odd_index_unip
  let : IsElementaryAbelian 2 (SLTwo.Unip F) := unip_isElementaryAbelian
  let f : P →* SLTwo.Unip F := {
    toFun x := ⟨pi x, x.property⟩
    map_one' := Subtype.ext (pi.map_one)
    map_mul' x y := Subtype.ext (pi.map_mul x y) }
  have hcomm : (commutator P).map P.subtype ≤ pi.ker := by
    rintro x ⟨y, hy, rfl⟩
    have hf : f y = 1 := Abelianization.commutator_subset_ker f hy
    exact congrArg Subtype.val hf
  have hpow (x : P) : (x : G) ^ 2 ∈ pi.ker := by
    have hfx : (f x) ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (SLTwo.Unip F)) (f x)
    change pi ((x : G) ^ 2) = 1
    rw [map_pow]
    exact congrArg Subtype.val hfx
  exact CentralPGroupTransfer.binary_isElementaryAbelian_of_odd_index
    pi.ker hker hcentral P hindex hcomm hpow

/-- The same conclusion with a separately named actual kernel subgroup. -/
theorem isElementaryAbelian_of_ker_eq
    (R : Subgroup G) (hR : IsPGroup 2 R) (hcentral : R ≤ Subgroup.center G)
    (pi : G →* SLTwo.SL2 F) (hpi : Function.Surjective pi) (hker : pi.ker = R) :
    IsElementaryAbelian 2 R := by
  subst R
  exact isElementaryAbelian_kernel pi hpi hR hcentral

/-- An actual quotient isomorphism supplies the required surjection. -/
theorem isElementaryAbelian_of_quotient_equiv
    (R : Subgroup G) [R.Normal] (hR : IsPGroup 2 R)
    (hcentral : R ≤ Subgroup.center G) (e : SLTwo.SL2 F ≃* G ⧸ R) :
    IsElementaryAbelian 2 R := by
  let pi : G →* SLTwo.SL2 F := e.symm.toMonoidHom.comp (QuotientGroup.mk' R)
  have hpi : Function.Surjective pi :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective R)
  have hker : pi.ker = R := by
    ext x
    change e.symm (QuotientGroup.mk' R x) = 1 ↔ x ∈ R
    rw [e.symm.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  exact isElementaryAbelian_of_ker_eq R hR hcentral pi hpi hker

end Kourovka2135.BinaryCentralKernelElementary

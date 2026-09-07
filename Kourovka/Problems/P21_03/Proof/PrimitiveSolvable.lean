import Kourovka.Problems.P21_03.Proof.Basic
import Kourovka.Problems.P21_03.Proof.AutomorphismBound
import Kourovka.Problems.P21_03.Proof.PrimitiveOrderArithmetic
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Perm.Support

/-!
# Primitive soluble permutation groups

This file isolates the elementary primitive-group input used in the asymptotic
argument.  The central point is that a nontrivial soluble group has a nontrivial
abelian normal subgroup: take the last nontrivial term of its derived series.
-/

open Subgroup

namespace Kourovka213

/-- A nontrivial soluble group contains a nontrivial abelian normal subgroup.

The subgroup constructed by the proof is the last nontrivial term of the
derived series. -/
theorem exists_nontrivial_abelian_normal_subgroup
    (G : Type*) [Group G] [Nontrivial G] [Group.IsSolvable G] :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ A.Normal ∧ IsMulCommutative A := by
  classical
  let hsolv : ∃ n : ℕ, derivedSeries G n = ⊥ := Group.IsSolvable.solvable
  let n : ℕ := Nat.find hsolv
  have hn : derivedSeries G n = ⊥ := Nat.find_spec hsolv
  have hn0 : n ≠ 0 := by
    intro h
    have htop : (⊤ : Subgroup G) = ⊥ := by
      simpa [n, h] using hn
    exact top_ne_bot htop
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hfind : Nat.find hsolv = m + 1 := by
    simpa [n, Nat.succ_eq_add_one] using hm
  refine ⟨derivedSeries G m, ?_, derivedSeries_normal G m, ?_⟩
  · intro hm_bot
    have hmin : Nat.find hsolv ≤ m := Nat.find_min' hsolv hm_bot
    rw [hfind] at hmin
    omega
  · apply Subgroup.commutator_self_eq_bot_iff.mp
    rw [hm, derivedSeries_succ] at hn
    exact hn

/-- In a faithful primitive action, every nontrivial normal subgroup is
transitive.  This is the normal-subgroup property of primitive actions,
with faithfulness used to rule out a globally trivial normal subgroup. -/
theorem normal_isPretransitive_of_ne_bot
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X]
    (A : Subgroup G) [A.Normal] (hA : A ≠ ⊥) :
    MulAction.IsPretransitive A X := by
  apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
  intro hfixed
  apply hA
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X))
  intro x
  have hx : x ∈ MulAction.fixedPoints A X := by
    rw [hfixed]
    exact Set.mem_univ x
  exact MulAction.mem_fixedPoints.mp hx ⟨a, ha⟩

/-- A faithful transitive action of an abelian group is free (and hence
regular). -/
theorem isCancelSMul_of_isPretransitive_of_isMulCommutative
    (A X : Type*) [Group A] [MulAction A X] [FaithfulSMul A X]
    [MulAction.IsPretransitive A X] [IsMulCommutative A] :
    IsCancelSMul A X := by
  rw [isCancelSMul_iff_stabilizer_eq_bot]
  intro x
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul A X))
  intro y
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq A x y
  calc
    a • b • x = (a * b) • x := by rw [mul_smul]
    _ = (b * a) • x := by rw [mul_comm']
    _ = b • a • x := by rw [mul_smul]
    _ = b • x := by rw [MulAction.mem_stabilizer_iff.mp ha]

/-- A nontrivial soluble group in a faithful primitive action has a regular
abelian normal subgroup. -/
theorem exists_regular_abelian_normal_subgroup
    (G X : Type*) [Group G] [Nontrivial G] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X] :
    ∃ A : Subgroup G, A ≠ ⊥ ∧ A.Normal ∧ IsMulCommutative A ∧
      MulAction.IsPretransitive A X ∧ IsCancelSMul A X := by
  obtain ⟨A, hA, hnormal, hab⟩ := exists_nontrivial_abelian_normal_subgroup G
  letI : A.Normal := hnormal
  have htrans : MulAction.IsPretransitive A X :=
    normal_isPretransitive_of_ne_bot G X A hA
  letI : MulAction.IsPretransitive A X := htrans
  letI : IsMulCommutative A := hab
  have hfree : IsCancelSMul A X :=
    isCancelSMul_of_isPretransitive_of_isMulCommutative A X
  exact ⟨A, hA, hnormal, hab, htrans, hfree⟩

/-- In a regular action, evaluation at any point is an equivalence. -/
noncomputable def regularOrbitEquiv
    (A X : Type*) [Group A] [MulAction A X]
    [MulAction.IsPretransitive A X] [IsCancelSMul A X] (x : X) : A ≃ X where
  toFun a := a • x
  invFun y := Classical.choose (MulAction.exists_smul_eq A x y)
  left_inv a := by
    apply IsCancelSMul.right_cancel _ _ x
    exact Classical.choose_spec (MulAction.exists_smul_eq A x (a • x))
  right_inv y := Classical.choose_spec (MulAction.exists_smul_eq A x y)

/-- If a finite group has a regular abelian normal subgroup, then a nonidentity
element fixes at most half of the points. -/
theorem two_mul_card_fixedBy_le_of_regular_abelian_normal
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    [MulAction.IsPretransitive A X] [IsCancelSMul A X]
    (g : G) (hg : g ≠ 1) :
    2 * Nat.card (MulAction.fixedBy X g) ≤ Fintype.card X := by
  classical
  by_cases hnonempty : (MulAction.fixedBy X g).Nonempty
  · obtain ⟨x, hx⟩ := hnonempty
    have hxg : g • x = x := MulAction.mem_fixedBy.mp hx
    let C : Subgroup A :=
      (Subgroup.centralizer ({g} : Set G)).comap A.subtype
    have hC : C ≠ ⊤ := by
      intro htop
      apply hg
      apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X))
      intro y
      obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A x y
      have haC : a ∈ C := by
        rw [htop]
        exact Subgroup.mem_top a
      have hcomm : (a : G) * g = g * (a : G) := by
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_comap.mp haC)
      calc
        g • (a : G) • x = (g * (a : G)) • x := by rw [mul_smul]
        _ = ((a : G) * g) • x := by rw [hcomm]
        _ = (a : G) • g • x := by rw [mul_smul]
        _ = (a : G) • x := by rw [hxg]
    let e : A ≃ X := regularOrbitEquiv A X x
    have hmem (a : A) : a ∈ C ↔ e a ∈ MulAction.fixedBy X g := by
      change a ∈ C ↔ g • (a : G) • x = (a : G) • x
      constructor
      · intro ha
        have hcomm : (a : G) * g = g * (a : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.mem_comap.mp ha)
        calc
          g • (a : G) • x = (g * (a : G)) • x := by rw [mul_smul]
          _ = ((a : G) * g) • x := by rw [hcomm]
          _ = (a : G) • g • x := by rw [mul_smul]
          _ = (a : G) • x := by rw [hxg]
      · intro ha
        have hginv : g⁻¹ • x = x := by
          calc
            g⁻¹ • x = g⁻¹ • (g • x) := by rw [hxg]
            _ = x := by simp
        let c : A :=
          ⟨g * (a : G) * g⁻¹,
            (inferInstance : A.Normal).conj_mem (a : G) a.2 g⟩
        have hca : c = a := by
          apply IsCancelSMul.right_cancel _ _ x
          change (g * (a : G) * g⁻¹) • x = (a : G) • x
          calc
            (g * (a : G) * g⁻¹) • x = g • (a : G) • (g⁻¹ • x) := by
              simp only [mul_smul]
            _ = g • (a : G) • x := by rw [hginv]
            _ = (a : G) • x := ha
        apply Subgroup.mem_comap.mpr
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have hconj : g * (a : G) * g⁻¹ = (a : G) :=
          congrArg Subtype.val hca
        calc
          (a : G) * g = (g * (a : G) * g⁻¹) * g := by rw [hconj]
          _ = g * (a : G) := by simp [mul_assoc]
    let efixed : C ≃ MulAction.fixedBy X g := e.subtypeEquiv hmem
    have hfixedC : Nat.card (MulAction.fixedBy X g) = Nat.card C :=
      (Nat.card_congr efixed).symm
    have hXA : Fintype.card X = Nat.card A := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr e).symm
    have hindex : 2 ≤ C.index := by
      have : 1 < C.index := Subgroup.one_lt_index_of_ne_top hC
      omega
    rw [hfixedC, hXA]
    calc
      2 * Nat.card C ≤ C.index * Nat.card C :=
        Nat.mul_le_mul_right (Nat.card C) hindex
      _ = Nat.card A := C.index_mul_card
  · have hempty : MulAction.fixedBy X g = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty]
    simp

/-- The fixed-point bound specialized to a finite faithful primitive soluble
action. -/
theorem primitive_solvable_two_mul_card_fixedBy_le
    (G X : Type*) [Group G] [Finite G] [Fintype X]
    [Group.IsSolvable G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X]
    (g : G) (hg : g ≠ 1) :
    2 * Nat.card (MulAction.fixedBy X g) ≤ Fintype.card X := by
  letI : Nontrivial G := nontrivial_of_ne g 1 hg
  obtain ⟨A, _hA, hnormal, hab, htrans, hfree⟩ :=
    exists_regular_abelian_normal_subgroup G X
  letI : A.Normal := hnormal
  letI : IsMulCommutative A := hab
  letI : MulAction.IsPretransitive A X := htrans
  letI : IsCancelSMul A X := hfree
  exact two_mul_card_fixedBy_le_of_regular_abelian_normal G X A g hg

/-- Fixed points of an element of a permutation subgroup are the complement
of the support of its underlying permutation. -/
theorem card_fixedBy_subgroup_eq_card_compl_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (g : G) :
    Nat.card (MulAction.fixedBy X g) = g.1.supportᶜ.card := by
  classical
  let e : MulAction.fixedBy X g ≃ {x // x ∈ g.1.supportᶜ} :=
    Equiv.subtypeEquivRight fun x => by
      simp only [MulAction.mem_fixedBy, Subgroup.smul_def,
        Equiv.Perm.smul_def, Finset.mem_compl, Equiv.Perm.mem_support,
        not_not]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact Fintype.card_coe g.1.supportᶜ

/-- Every nonidentity element of a finite primitive soluble permutation group
moves at least half of the underlying points. -/
theorem card_le_two_mul_support_of_primitive_solvable
    {X : Type*} [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) [Group.IsSolvable G]
    [MulAction.IsPreprimitive G X]
    (g : G) (hg : g ≠ 1) :
    Fintype.card X ≤ 2 * g.1.support.card := by
  have hfixed := primitive_solvable_two_mul_card_fixedBy_le G X g hg
  rw [card_fixedBy_subgroup_eq_card_compl_support G g,
    Finset.card_compl] at hfixed
  have hs : g.1.support.card ≤ Fintype.card X := g.1.support.card_le_univ
  omega

/-- Conjugation on a regular abelian normal subgroup is faithful on a point
stabilizer.  This is the structural injection used for crude order bounds on
primitive soluble groups. -/
theorem pointStabilizer_conjNormal_injective
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    [MulAction.IsPretransitive A X] [IsCancelSMul A X]
    (x : X) :
    Function.Injective
      ((MulAut.conjNormal (H := A)).comp (MulAction.stabilizer G x).subtype) := by
  intro h k hhk
  let q : G := (k : G)⁻¹ * (h : G)
  have hqmap : MulAut.conjNormal (H := A) q = 1 := by
    change MulAut.conjNormal (H := A) (h : G) =
      MulAut.conjNormal (H := A) (k : G) at hhk
    change MulAut.conjNormal (H := A) ((k : G)⁻¹ * (h : G)) = 1
    rw [map_mul, map_inv, hhk, inv_mul_cancel]
  have hqcomm (a : A) : q * (a : G) = (a : G) * q := by
    have happly : (MulAut.conjNormal (H := A) q) a = a := by
      rw [hqmap]
      rfl
    have hconj : q * (a : G) * q⁻¹ = (a : G) := by
      exact (MulAut.conjNormal_apply q a).symm.trans
        (congrArg Subtype.val happly)
    calc
      q * (a : G) = (q * (a : G) * q⁻¹) * q := by simp [mul_assoc]
      _ = (a : G) * q := by rw [hconj]
  have hqfix : q • x = x := by
    have hhfix : (h : G) • x = x := MulAction.mem_stabilizer_iff.mp h.2
    have hkfix : (k : G) • x = x := MulAction.mem_stabilizer_iff.mp k.2
    have hkinv : (k : G)⁻¹ • x = x := by
      calc
        (k : G)⁻¹ • x = (k : G)⁻¹ • ((k : G) • x) := by rw [hkfix]
        _ = x := by simp
    change ((k : G)⁻¹ * (h : G)) • x = x
    calc
      ((k : G)⁻¹ * (h : G)) • x = (k : G)⁻¹ • ((h : G) • x) := by
        rw [mul_smul]
      _ = (k : G)⁻¹ • x := by rw [hhfix]
      _ = x := hkinv
  have hqone : q = 1 := by
    apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X))
    intro y
    obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq A x y
    calc
      q • ((a : G) • x) = (q * (a : G)) • x :=
        (mul_smul q (a : G) x).symm
      _ = ((a : G) * q) • x := by rw [hqcomm]
      _ = (a : G) • (q • x) := mul_smul (a : G) q x
      _ = (a : G) • x := by rw [hqfix]
  apply Subtype.ext
  dsimp [q] at hqone
  exact (inv_mul_eq_one.mp hqone).symm

/-- Consequently, the point stabilizer has cardinality at most the automorphism
group of a regular abelian normal subgroup. -/
theorem card_pointStabilizer_le_card_mulAut
    (G X : Type*) [Group G] [Finite G] [MulAction G X] [FaithfulSMul G X]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    [MulAction.IsPretransitive A X] [IsCancelSMul A X]
    (x : X) :
    Nat.card (MulAction.stabilizer G x) ≤ Nat.card (MulAut A) :=
  Nat.card_le_card_of_injective _
    (pointStabilizer_conjNormal_injective G X A x)

/-- A group acting regularly on a finite type has the same cardinality as the
type. -/
theorem natCard_eq_card_of_regular_action
    (A X : Type*) [Group A] [Finite A] [Fintype X] [MulAction A X]
    [MulAction.IsPretransitive A X] [IsCancelSMul A X] (x : X) :
    Nat.card A = Fintype.card X := by
  calc
    Nat.card A = Nat.card X := Nat.card_congr (regularOrbitEquiv A X x)
    _ = Fintype.card X := Nat.card_eq_fintype_card

/-- A nontrivial group cannot act faithfully on a finite type with fewer than
two points. -/
theorem two_le_card_of_faithful_action
    (G X : Type*) [Group G] [Nontrivial G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X] :
    2 ≤ Fintype.card X := by
  haveI : Nontrivial X := by
    by_contra hX
    haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    have hsubG : Subsingleton G :=
      ⟨fun g h => inv_mul_eq_one.mp <|
        (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) (g⁻¹ * h)
          (fun x => Subsingleton.elim ((g⁻¹ * h) • x) x)⟩
    exact not_subsingleton_iff_nontrivial.mpr
      (inferInstance : Nontrivial G) hsubG
  exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance

/-- A primitive soluble group has the elementary subexponential order bound
`n ^ (log 2 n + 1)`.  This is enough to obtain a universal exponential bound
after a purely numerical estimate. -/
theorem natCard_le_card_pow_log_succ_of_primitive_solvable
    (G X : Type*) [Group G] [Finite G] [Nontrivial G]
    [Fintype X] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X] :
    Nat.card G ≤ Fintype.card X ^ (Nat.log 2 (Fintype.card X) + 1) := by
  letI := Fintype.ofFinite G
  letI : Nonempty X := Fintype.card_pos_iff.mp <| by
    have := two_le_card_of_faithful_action G X
    omega
  obtain ⟨A, _hA, hnormal, hab, htrans, hfree⟩ :=
    exists_regular_abelian_normal_subgroup G X
  letI : A.Normal := hnormal
  letI : IsMulCommutative A := hab
  letI : MulAction.IsPretransitive A X := htrans
  letI : IsCancelSMul A X := hfree
  let x : X := Classical.arbitrary X
  letI := Fintype.ofFinite (MulAction.stabilizer G x)
  have hAcard : Nat.card A = Fintype.card X :=
    natCard_eq_card_of_regular_action A X x
  have hstab :
      Nat.card (MulAction.stabilizer G x) ≤ Nat.card (MulAut A) :=
    card_pointStabilizer_le_card_mulAut G X A x
  have haut : Nat.card (MulAut A) ≤
      Nat.card A ^ Nat.log 2 (Nat.card A) :=
    natCard_mulAut_le_pow_log_two A
  have hGcard : Nat.card G =
      Nat.card (MulAction.stabilizer G x) * Fintype.card X := by
    calc
      Nat.card G = Nat.card (MulAction.stabilizer G x) *
          (MulAction.stabilizer G x).index :=
        (MulAction.stabilizer G x).card_mul_index.symm
      _ = Nat.card (MulAction.stabilizer G x) * Nat.card X := by
        rw [MulAction.index_stabilizer_of_transitive]
      _ = Nat.card (MulAction.stabilizer G x) * Fintype.card X :=
        congrArg (fun m : ℕ => Nat.card (MulAction.stabilizer G x) * m)
          (Nat.card_eq_fintype_card (α := X))
  rw [hGcard]
  calc
    Nat.card (MulAction.stabilizer G x) * Fintype.card X ≤
        Nat.card (MulAut A) * Fintype.card X :=
      Nat.mul_le_mul_right (Fintype.card X) hstab
    _ ≤ (Nat.card A ^ Nat.log 2 (Nat.card A)) * Fintype.card X :=
      Nat.mul_le_mul_right (Fintype.card X) haut
    _ = Fintype.card X ^ (Nat.log 2 (Fintype.card X) + 1) := by
      rw [hAcard, pow_succ]

/-- Uniform exponential form of the primitive soluble order bound.  The loss
of one in the exponent is useful when this estimate is iterated down a block
decomposition tree. -/
theorem natCard_le_256_pow_pred_of_primitive_solvable
    (G X : Type*) [Group G] [Finite G] [Nontrivial G]
    [Fintype X] [Group.IsSolvable G]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPreprimitive G X] :
    Nat.card G ≤ 256 ^ (Fintype.card X - 1) :=
  (natCard_le_card_pow_log_succ_of_primitive_solvable G X).trans
    (pow_succ_log_two_le_256_pow_pred (Fintype.card X)
      (two_le_card_of_faithful_action G X))

end Kourovka213

import Mathlib.GroupTheory.Sylow

/-! Normalizers lift across a finite p-kernel for every q-subgroup, q≠p.

The given subgroup is proved Sylow inside its product with the kernel.
Sylow conjugacy there corrects a chosen lift by a kernel element. This is
the elementary Frattini argument; no solubility, complement, or splitting
hypothesis is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.NormalizerCoprimeKernelLift

open scoped Pointwise

variable {G H : Type*} [Group G] [Group H] [Finite G]
variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- A q-subgroup is actually Sylow inside its product with a normal p-kernel. -/
def sylowInPreimage (f : G →* H) (hker : IsPGroup p f.ker)
    (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p) :
    Sylow q ↥(P ⊔ f.ker) where
  toSubgroup := P.subgroupOf (P ⊔ f.ker)
  isPGroup' := hP.comap_subtype
  is_maximal' := by
    intro D hD hPD
    apply le_antisymm ?_ hPD
    let L := P ⊔ f.ker
    let E : Subgroup G := D.map L.subtype
    have hE : IsPGroup q E := hD.map L.subtype
    have hPE : P ≤ E := by
      intro a ha
      exact ⟨⟨a, (show P ≤ P ⊔ f.ker from le_sup_left) ha⟩, hPD ha, rfl⟩
    have hdisjoint : Disjoint E f.ker :=
      IsPGroup.disjoint_of_ne q p hne E f.ker hE hker
    intro x hx
    have hxL : (x : G) ∈ P ⊔ f.ker := x.property
    obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp hxL
    have hxa : f (x : G) = f a := by
      rw [← han, map_mul, show f n = 1 from hn, mul_one]
    have hdiffE : (x : G) * a⁻¹ ∈ E :=
      E.mul_mem ⟨x, hx, rfl⟩ (E.inv_mem (hPE ha))
    have hdiffker : (x : G) * a⁻¹ ∈ f.ker := by
      change f ((x : G) * a⁻¹) = 1
      rw [map_mul, map_inv, hxa, mul_inv_cancel]
    have hxa' : (x : G) = a := mul_inv_eq_one.mp
      (Subgroup.disjoint_def.mp hdisjoint hdiffE hdiffker)
    change (x : G) ∈ P
    exact hxa'.symm ▸ ha

omit [Finite G] in
@[simp] theorem sylowInPreimage_map (f : G →* H) (hker : IsPGroup p f.ker)
    (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p) :
    ((sylowInPreimage f hker P hP hne : Sylow q ↥(P ⊔ f.ker)) :
      Subgroup ↥(P ⊔ f.ker)).map (P ⊔ f.ker).subtype = P := by
  change (P.subgroupOf (P ⊔ f.ker)).map (P ⊔ f.ker).subtype = P
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_left]

/-- Correct a chosen normalizing image lift by an actual kernel element.
Surjectivity of f is not needed for this chosen-lift statement. -/
theorem exists_kernel_mul_mem_normalizer (f : G →* H) (hker : IsPGroup p f.ker)
    (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p)
    (z : G) (hz : f z ∈ (Subgroup.normalizer (P.map f : Set H))) :
    ∃ n ∈ f.ker, n * z ∈ (Subgroup.normalizer (P : Set G)) := by
  let L : Subgroup G := P ⊔ f.ker
  let S : Sylow q L := sylowInPreimage f hker P hP hne
  have hSmap : (S : Subgroup L).map L.subtype = P :=
    sylowInPreimage_map f hker P hP hne
  have hzL : z ∈ (Subgroup.normalizer (L : Set G)) := by
    change z ∈ (Subgroup.normalizer ((P ⊔ f.ker : Subgroup G) : Set G))
    rw [← Subgroup.comap_map_eq]
    exact (P.map f).le_normalizer_comap f hz
  have hconjL : L.map (MulAut.conj z).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hzL
  let α : L ≃* L := ((MulAut.conj z).subgroupMap L).trans
    (MulEquiv.subgroupCongr hconjL)
  let T : Sylow q L := S.mapSurjective (f := α.toMonoidHom) α.surjective
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq L T S
  have htSub : (S : Subgroup L) =
      ((S : Subgroup L).map α.toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    exact congrArg (fun Q : Sylow q L => (Q : Subgroup L)) ht.symm
  have hcomp : (L.subtype.comp (MulAut.conj t).toMonoidHom).comp α.toMonoidHom =
      (MulAut.conj ((t : G) * z)).toMonoidHom.comp L.subtype := by
    ext a
    change (t : G) * (z * (a : G) * z⁻¹) * (t : G)⁻¹ =
      ((t : G) * z) * (a : G) * ((t : G) * z)⁻¹
    group
  have htG := congrArg (fun K : Subgroup L => K.map L.subtype) htSub
  rw [Subgroup.map_map, Subgroup.map_map, hcomp, ← Subgroup.map_map, hSmap] at htG
  have htz : (t : G) * z ∈ (Subgroup.normalizer (P : Set G)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr htG.symm
  obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp t.property
  refine ⟨n, hn, ?_⟩
  have h := (Subgroup.normalizer (P : Set G)).mul_mem
    ((Subgroup.normalizer (P : Set G)).inv_mem (P.le_normalizer ha)) htz
  rw [← han] at h
  simpa only [mul_assoc, inv_mul_cancel_left] using h

/-- Every element normalizing the image has a lift normalizing the given subgroup. -/
theorem exists_lift_normalizer (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p)
    (y : H) (hy : y ∈ (Subgroup.normalizer (P.map f : Set H))) :
    ∃ z ∈ (Subgroup.normalizer (P : Set G)), f z = y := by
  obtain ⟨z, rfl⟩ := hf y
  obtain ⟨n, hn, hnz⟩ := exists_kernel_mul_mem_normalizer f hker P hP hne z hy
  exact ⟨n * z, hnz, by rw [map_mul, show f n = 1 from hn, one_mul]⟩

/-- The normalizer maps onto the full normalizer of the image. -/
theorem map_normalizer_eq (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p) :
    (Subgroup.normalizer (P : Set G)).map f = (Subgroup.normalizer (P.map f : Set H)) := by
  apply le_antisymm (P.le_normalizer_map f)
  intro y hy
  obtain ⟨z, hz, hzy⟩ := exists_lift_normalizer f hf hker P hP hne y hy
  exact ⟨z, hz, hzy⟩

/-- The actual restricted normalizer homomorphism. -/
def normalizerMap (f : G →* H) (P : Subgroup G) :
    (Subgroup.normalizer (P : Set G)) →* (Subgroup.normalizer (P.map f : Set H)) :=
  (f.comp (Subgroup.normalizer (P : Set G)).subtype).codRestrict (Subgroup.normalizer (P.map f : Set H))
    (fun x => P.le_normalizer_map f ⟨x, x.property, rfl⟩)

theorem normalizerMap_surjective (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (P : Subgroup G) (hP : IsPGroup q P) (hne : q ≠ p) :
    Function.Surjective (normalizerMap f P) := by
  intro y
  obtain ⟨z, hz, hzy⟩ := exists_lift_normalizer f hf hker P hP hne y y.property
  exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

/-- In particular, prime-order subgroups have the normalizer-lifting property. -/
theorem exists_lift_normalizer_of_card_eq_prime (f : G →* H)
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    (P : Subgroup G) (hcard : Nat.card P = q) (hne : q ≠ p)
    (y : H) (hy : y ∈ (Subgroup.normalizer (P.map f : Set H))) :
    ∃ z ∈ (Subgroup.normalizer (P : Set G)), f z = y :=
  exists_lift_normalizer f hf hker P
    (IsPGroup.of_card (hcard.trans (pow_one q).symm)) hne y hy

/-- A lift of an inverting image can be chosen to invert the actual element.
The restriction of f to its q-cyclic subgroup is injective because its
intersection with the p-kernel is trivial. -/
theorem exists_lift_inverting (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (u : G) (hu : IsPGroup q (Subgroup.zpowers u))
    (hne : q ≠ p) (a : H) (ha : a⁻¹ * f u * a = (f u)⁻¹) :
    ∃ z : G, f z = a ∧ z⁻¹ * u * z = u⁻¹ := by
  let P := Subgroup.zpowers u
  have haInv : a⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers (f u) : Set H) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (a⁻¹ * f u * (a⁻¹)⁻¹) = Subgroup.zpowers (f u)
    rw [inv_inv, ha, Subgroup.zpowers_inv]
  have haNorm : a ∈ Subgroup.normalizer (P.map f : Set H) := by
    change a ∈ Subgroup.normalizer ((Subgroup.zpowers u).map f : Set H)
    rw [MonoidHom.map_zpowers]
    simpa only [inv_inv] using
      (Subgroup.normalizer (Subgroup.zpowers (f u) : Set H)).inv_mem haInv
  obtain ⟨z, hz, hza⟩ := exists_lift_normalizer f hf hker P hu hne a haNorm
  refine ⟨z, hza, ?_⟩
  have hconj : z⁻¹ * u * z ∈ P :=
    (Subgroup.mem_normalizer_iff''.mp hz u).mp (Subgroup.mem_zpowers u)
  have hdisjoint : Disjoint P f.ker :=
    IsPGroup.disjoint_of_ne q p hne P f.ker hu hker
  have hdP : (z⁻¹ * u * z) * u ∈ P := P.mul_mem hconj (Subgroup.mem_zpowers u)
  have hdker : (z⁻¹ * u * z) * u ∈ f.ker := by
    change f ((z⁻¹ * u * z) * u) = 1
    simp only [map_mul, map_inv, hza, ha, inv_mul_cancel]
  exact mul_eq_one_iff_eq_inv.mp (Subgroup.disjoint_def.mp hdisjoint hdP hdker)

/-- Prime-order form of the actual inversion-lifting theorem. -/
theorem exists_lift_inverting_of_orderOf (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) (u : G) (hu : orderOf u = q) (hne : q ≠ p)
    (a : H) (ha : a⁻¹ * f u * a = (f u)⁻¹) :
    ∃ z : G, f z = a ∧ z⁻¹ * u * z = u⁻¹ :=
  exists_lift_inverting f hf hker u
    (IsPGroup.of_card ((Nat.card_zpowers u).trans (hu.trans (pow_one q).symm))) hne a ha

/-- The order-three, binary-kernel form used by reflector induction. -/
theorem exists_lift_inverting_order_three (f : G →* H) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (u : G) (hu : orderOf u = 3)
    (a : H) (ha : a⁻¹ * f u * a = (f u)⁻¹) :
    ∃ z : G, f z = a ∧ z⁻¹ * u * z = u⁻¹ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact exists_lift_inverting_of_orderOf f hf hker u hu (by decide) a ha

end Kourovka2135.NormalizerCoprimeKernelLift

import Kourovka2135.PerfectSupplement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup

/-! A group-theoretic comparison of actual perfect central double covers.

The only conditional input is the explicitly quantified bound on the kernel
of every finite perfect central binary cover of the fixed quotient. The
comparison itself is constructed from the actual fiber product, a perfect
supplement, and its two actual projections. No cohomology or abstract cover
existence assumption replaces that construction.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.CentralDoubleCoverUniqueness
open scoped IsMulCommutative

variable {Q E₁ E₂ : Type u} [Group Q] [Group E₁] [Group E₂]

/-- The structural bound to be discharged for the particular quotient group. -/
def KernelBound (Q : Type u) [Group Q] : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* Q),
    Function.Surjective π → π.ker ≤ Subgroup.center E →
      IsPGroup 2 π.ker → Nat.card π.ker ≤ 2

/-- A central supplement to a subgroup of a perfect group adds nothing. -/
theorem eq_top_of_sup_central
    {E : Type u} [Group E] [Group.IsPerfect E]
    (H K : Subgroup E) (hs : H ⊔ K = ⊤) (hc : K ≤ Subgroup.center E) : H = ⊤ := by
  let : H.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← hs]
    exact sup_le H.le_normalizer (hc.trans (Subgroup.center_le_normalizer _))
  have hcomm : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext
    (Subgroup.mem_center_iff.mp (hc b.property) a)⟩⟩
  have hle : commutator E ≤ H :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hs hcomm
  rw [Group.IsPerfect.commutator_eq_top] at hle
  exact top_le_iff.mp hle

/-- A subgroup surjecting modulo a central kernel fills a perfect group. -/
theorem surjective_of_comp_surjective
    {P E : Type u} [Group P] [Group E] [Group.IsPerfect E]
    (f : P →* E) (π : E →* Q) (hc : π.ker ≤ Subgroup.center E)
    (hf : Function.Surjective (π.comp f)) : Function.Surjective f := by
  have hm : f.range.map π = ⊤ := by
    rw [MonoidHom.map_range, MonoidHom.range_eq_top]
    exact hf
  have hs : f.range ⊔ π.ker = ⊤ := by
    have h := congrArg (Subgroup.comap π) hm
    simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using h
  exact MonoidHom.range_eq_top.mp (eq_top_of_sup_central f.range π.ker hs hc)

/-- The cardinal formula written with the actual target of a surjection. -/
theorem card_eq_card_base_mul_card_ker
    {E : Type u} [Group E] (π : E →* Q) (hπ : Function.Surjective π) :
    Nat.card E = Nat.card Q * Nat.card π.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv]

/-- The actual fiber-product subgroup of the two covering groups. -/
def pullback (π₁ : E₁ →* Q) (π₂ : E₂ →* Q) : Subgroup (E₁ × E₂) :=
  (π₁.comp (MonoidHom.fst E₁ E₂)).eqLocus (π₂.comp (MonoidHom.snd E₁ E₂))

def left (π₁ : E₁ →* Q) (π₂ : E₂ →* Q) : pullback π₁ π₂ →* E₁ :=
  (MonoidHom.fst E₁ E₂).comp (pullback π₁ π₂).subtype

def right (π₁ : E₁ →* Q) (π₂ : E₂ →* Q) : pullback π₁ π₂ →* E₂ :=
  (MonoidHom.snd E₁ E₂).comp (pullback π₁ π₂).subtype

def base (π₁ : E₁ →* Q) (π₂ : E₂ →* Q) : pullback π₁ π₂ →* Q :=
  π₁.comp (left π₁ π₂)

theorem left_surjective (π₁ : E₁ →* Q) (π₂ : E₂ →* Q)
    (hπ₂ : Function.Surjective π₂) : Function.Surjective (left π₁ π₂) := by
  intro x
  obtain ⟨y, hy⟩ := hπ₂ (π₁ x)
  exact ⟨⟨(x, y), hy.symm⟩, rfl⟩

theorem base_surjective (π₁ : E₁ →* Q) (π₂ : E₂ →* Q)
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) :
    Function.Surjective (base π₁ π₂) :=
  hπ₁.comp (left_surjective π₁ π₂ hπ₂)

theorem base_kernel_central (π₁ : E₁ →* Q) (π₂ : E₂ →* Q)
    (hc₁ : π₁.ker ≤ Subgroup.center E₁) (hc₂ : π₂.ker ≤ Subgroup.center E₂) :
    (base π₁ π₂).ker ≤ Subgroup.center (pullback π₁ π₂) := by
  intro x hx
  have hx₁ : π₁ x.val.1 = 1 := hx
  have hx₂ : π₂ x.val.2 = 1 := x.property.symm.trans hx₁
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · exact Subgroup.mem_center_iff.mp (hc₁ hx₁) y.val.1
  · exact Subgroup.mem_center_iff.mp (hc₂ hx₂) y.val.2

theorem base_kernel_sq (π₁ : E₁ →* Q) (π₂ : E₂ →* Q)
    (hcard₁ : Nat.card π₁.ker = 2) (hcard₂ : Nat.card π₂.ker = 2)
    (x : pullback π₁ π₂) (hx : base π₁ π₂ x = 1) : x ^ 2 = 1 := by
  have hx₁ : π₁ x.val.1 = 1 := hx
  have hx₂ : π₂ x.val.2 = 1 := x.property.symm.trans hx₁
  apply Subtype.ext
  apply Prod.ext
  · have h : (⟨x.val.1, hx₁⟩ : π₁.ker) ^ 2 = 1 := by
      simpa only [hcard₁] using (pow_card_eq_one' (x := (⟨x.val.1, hx₁⟩ : π₁.ker)))
    exact congrArg Subtype.val h
  · have h : (⟨x.val.2, hx₂⟩ : π₂.ker) ^ 2 = 1 := by
      simpa only [hcard₂] using (pow_card_eq_one' (x := (⟨x.val.2, hx₂⟩ : π₂.ker)))
    exact congrArg Subtype.val h

/-- Any two actual finite perfect central double covers are equivalent over
Q once the general central binary kernel bound for Q has been established. -/
theorem exists_equiv_over
    [Finite E₁] [Finite E₂] [Group.IsPerfect E₁] [Group.IsPerfect E₂]
    (hbound : KernelBound Q) (π₁ : E₁ →* Q) (π₂ : E₂ →* Q)
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂)
    (hc₁ : π₁.ker ≤ Subgroup.center E₁) (hc₂ : π₂.ker ≤ Subgroup.center E₂)
    (hcard₁ : Nat.card π₁.ker = 2) (hcard₂ : Nat.card π₂.ker = 2) :
    ∃ e : E₁ ≃* E₂, ∀ x, π₂ (e x) = π₁ x := by
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hπ₁
  obtain ⟨P, _, hP, hperfect⟩ := exists_perfect_subgroup_map_top
    (base π₁ π₂) ⊤ (Subgroup.map_top_of_surjective _
      (base_surjective π₁ π₂ hπ₁ hπ₂))
  let : Group.IsPerfect P := hperfect
  let f : P →* Q := (base π₁ π₂).comp P.subtype
  let f₁ : P →* E₁ := (left π₁ π₂).comp P.subtype
  let f₂ : P →* E₂ := (right π₁ π₂).comp P.subtype
  have hf : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    change ((base π₁ π₂).comp P.subtype).range = ⊤
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hP
  have hf₂base : π₂.comp f₂ = f := by
    ext x
    exact x.val.property.symm
  have hsurj₁ : Function.Surjective f₁ :=
    surjective_of_comp_surjective f₁ π₁ hc₁ hf
  have hsurj₂ : Function.Surjective f₂ :=
    surjective_of_comp_surjective f₂ π₂ hc₂ (by rw [hf₂base]; exact hf)
  have hc : f.ker ≤ Subgroup.center P := by
    intro x hx
    have hx' : x.val ∈ (base π₁ π₂).ker := hx
    have hz := base_kernel_central π₁ π₂ hc₁ hc₂ hx'
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz y.val)
  have hp : IsPGroup 2 f.ker := by
    apply isPGroup_iff_pow_pow_eq_one.mpr
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val ^ 2 = 1
    exact base_kernel_sq π₁ π₂ hcard₁ hcard₂ x.val.val x.property
  have hb : Nat.card f.ker ≤ 2 := hbound P f hf hc hp
  have hsize₁ : Nat.card P ≤ Nat.card E₁ := calc
    Nat.card P = Nat.card Q * Nat.card f.ker := card_eq_card_base_mul_card_ker f hf
    _ ≤ Nat.card Q * 2 := Nat.mul_le_mul_left _ hb
    _ = Nat.card E₁ := by rw [card_eq_card_base_mul_card_ker π₁ hπ₁, hcard₁]
  have hsize₂ : Nat.card P ≤ Nat.card E₂ := calc
    Nat.card P = Nat.card Q * Nat.card f.ker := card_eq_card_base_mul_card_ker f hf
    _ ≤ Nat.card Q * 2 := Nat.mul_le_mul_left _ hb
    _ = Nat.card E₂ := by rw [card_eq_card_base_mul_card_ker π₂ hπ₂, hcard₂]
  let e₁ : P ≃* E₁ := MulEquiv.ofBijective f₁ (hsurj₁.bijective_of_nat_card_le hsize₁)
  let e₂ : P ≃* E₂ := MulEquiv.ofBijective f₂ (hsurj₂.bijective_of_nat_card_le hsize₂)
  refine ⟨e₁.symm.trans e₂, ?_⟩
  intro x
  change π₂ (f₂ (e₁.symm x)) = π₁ x
  calc
    π₂ (f₂ (e₁.symm x)) = π₁ (f₁ (e₁.symm x)) := (e₁.symm x).val.property.symm
    _ = π₁ x := congrArg π₁ (e₁.apply_symm_apply x)

end Kourovka2135.CentralDoubleCoverUniqueness

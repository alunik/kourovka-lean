import Kourovka2135.CentralDoubleCoverUniqueness

/-! An actual central p-cover attaining a proved uniform kernel bound
surjects onto every finite perfect central p-cover of the same quotient.
The proof uses a perfect supplement in the actual fiber product. It does
not assume existence or universality of a Schur covering group.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.CentralMaximalCover

open CentralDoubleCoverUniqueness

variable {Q E F : Type u} [Group Q] [Group E] [Group F]

/-- The uniform bound is an explicit input to this generic comparison. -/
def KernelBound (p n : ℕ) (Q : Type u) [Group Q] : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] [Group.IsPerfect D] (π : D →* Q),
    Function.Surjective π → π.ker ≤ Subgroup.center D →
      IsPGroup p π.ker → Nat.card π.ker ≤ n

theorem pullback_kernel_isPGroup (p : ℕ) (π : E →* Q) (τ : F →* Q)
    (hpπ : IsPGroup p π.ker) (hpτ : IsPGroup p τ.ker) :
    IsPGroup p (base π τ).ker := by
  intro x
  have hx₁ : π x.val.val.1 = 1 := x.property
  have hx₂ : τ x.val.val.2 = 1 := x.val.property.symm.trans hx₁
  obtain ⟨a, ha⟩ := hpπ (⟨x.val.val.1, hx₁⟩ : π.ker)
  obtain ⟨b, hb⟩ := hpτ (⟨x.val.val.2, hx₂⟩ : τ.ker)
  refine ⟨a + b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change x.val.val.1 ^ (p ^ (a + b)) = 1
    rw [pow_add, pow_mul, show x.val.val.1 ^ (p ^ a) = 1 from
      congrArg Subtype.val ha, one_pow]
  · change x.val.val.2 ^ (p ^ (a + b)) = 1
    rw [Nat.add_comm a b, pow_add, pow_mul,
      show x.val.val.2 ^ (p ^ b) = 1 from congrArg Subtype.val hb, one_pow]

/-- A reference cover whose kernel attains the uniform bound dominates
every other finite perfect central p-cover, over the actual quotient. -/
theorem exists_surjective_over
    [Finite E] [Finite F] [Group.IsPerfect E] [Group.IsPerfect F]
    (p n : ℕ) (hbound : KernelBound p n Q)
    (π : E →* Q) (τ : F →* Q)
    (hπ : Function.Surjective π) (hτ : Function.Surjective τ)
    (hcπ : π.ker ≤ Subgroup.center E) (hcτ : τ.ker ≤ Subgroup.center F)
    (hpπ : IsPGroup p π.ker) (hpτ : IsPGroup p τ.ker)
    (hcard : Nat.card τ.ker = n) :
    ∃ f : F →* E, Function.Surjective f ∧ π.comp f = τ := by
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hπ
  obtain ⟨P, _, hP, hperfect⟩ := exists_perfect_subgroup_map_top
    (base π τ) ⊤ (Subgroup.map_top_of_surjective _ (base_surjective π τ hπ hτ))
  let : Group.IsPerfect P := hperfect
  let b : P →* Q := (base π τ).comp P.subtype
  let l : P →* E := (left π τ).comp P.subtype
  let r : P →* F := (right π τ).comp P.subtype
  have hb : Function.Surjective b := by
    rw [← MonoidHom.range_eq_top]
    change ((base π τ).comp P.subtype).range = ⊤
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hP
  have hrbase : τ.comp r = b := by
    ext x
    exact x.val.property.symm
  have hl : Function.Surjective l := surjective_of_comp_surjective l π hcπ hb
  have hr : Function.Surjective r :=
    surjective_of_comp_surjective r τ hcτ (by rw [hrbase]; exact hb)
  have hc : b.ker ≤ Subgroup.center P := by
    intro x hx
    have hx' : x.val ∈ (base π τ).ker := hx
    have hz := base_kernel_central π τ hcπ hcτ hx'
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz y.val)
  let k : b.ker →* (base π τ).ker :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (base π τ).ker => z.val) h
  have hp : IsPGroup p b.ker := (pullback_kernel_isPGroup p π τ hpπ hpτ).of_injective k hk
  have hbcard : Nat.card b.ker ≤ n := hbound P b hb hc hp
  have hsize : Nat.card P ≤ Nat.card F := calc
    Nat.card P = Nat.card Q * Nat.card b.ker := card_eq_card_base_mul_card_ker b hb
    _ ≤ Nat.card Q * n := Nat.mul_le_mul_left _ hbcard
    _ = Nat.card F := by rw [card_eq_card_base_mul_card_ker τ hτ, hcard]
  let e : P ≃* F := MulEquiv.ofBijective r (hr.bijective_of_nat_card_le hsize)
  refine ⟨l.comp e.symm.toMonoidHom, hl.comp e.symm.surjective, ?_⟩
  ext x
  change π (l (e.symm x)) = τ x
  calc
    π (l (e.symm x)) = τ (r (e.symm x)) := (e.symm x).val.property
    _ = τ x := congrArg τ (e.apply_symm_apply x)

end Kourovka2135.CentralMaximalCover

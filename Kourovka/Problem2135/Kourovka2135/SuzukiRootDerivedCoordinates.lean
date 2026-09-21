import Kourovka2135.SuzukiRootCoordinates
import Kourovka2135.ClassTwoCommutators
import Kourovka2135.Vendor.CFSG.ElementaryAbelian
import Mathlib.GroupTheory.Abelianization.Defs

/-! Exact derived and abelianization coordinates of the full actual Suzuki
root group. Fullness is proved by expressing every central coordinate as a
scaled commutator; it is not an assumed identification. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiRootDerivedCoordinates

open BenderSuzuki.MatrixGroups SuzukiGeometry
open scoped Matrix MatrixGroups IsMulCommutative

abbrev U (m : ℕ) := root m

def coord (m : ℕ) (a b : K m) : U m :=
  ⟨⟨SuzukiRootGL m a b, Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩,
    Subgroup.subset_closure ⟨a, b, rfl⟩⟩

theorem coord_injective (m : ℕ) {a b c d : K m}
    (h : coord m a b = coord m c d) : a = c ∧ b = d :=
  suzukiRootGL_injective m a b c d (congrArg (fun x : U m => x.val.val) h)

theorem exists_coord (m : ℕ) (x : U m) : ∃ a b : K m, coord m a b = x := by
  obtain ⟨a, b, h⟩ := (suzukiRootGL_mem_closure_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    x.val.val).mp x.property
  exact ⟨a, b, Subtype.ext (Subtype.ext h.symm)⟩

@[simp] theorem coord_zero_zero (m : ℕ) : coord m 0 0 = 1 :=
  Subtype.ext (Subtype.ext (suzukiRootGL_zero_zero m))

theorem coord_mul (m : ℕ) (a b c d : K m) :
    coord m a b * coord m c d = coord m (a + c) (b + d + a * tits m c) :=
  Subtype.ext (Subtype.ext (suzukiRootGL_mul m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m) a b c d))

theorem coord_inv (m : ℕ) (a b : K m) :
    (coord m a b)⁻¹ = coord m a (b + a * tits m a) :=
  Subtype.ext (Subtype.ext (suzukiRootGL_inv m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m) a b))

def first (m : ℕ) (x : U m) : K m :=
  (x.val.val : Matrix (Fin 4) (Fin 4) (K m)) 0 1

def second (m : ℕ) (x : U m) : K m :=
  (x.val.val : Matrix (Fin 4) (Fin 4) (K m)) 0 2

@[simp] theorem first_coord (m : ℕ) (a b : K m) : first m (coord m a b) = a := by
  simp [first, coord, SuzukiRootGL, SuzukiRootMatrix]

@[simp] theorem second_coord (m : ℕ) (a b : K m) : second m (coord m a b) = b := by
  simp [second, coord, SuzukiRootGL, SuzukiRootMatrix]

@[simp] theorem coord_first_second (m : ℕ) (x : U m) :
    coord m (first m x) (second m x) = x := by
  obtain ⟨a, b, rfl⟩ := exists_coord m x
  simp

def firstHom (m : ℕ) : U m →* Multiplicative (K m) where
  toFun x := Multiplicative.ofAdd (first m x)
  map_one' := by change first m 1 = 0; simp [first]
  map_mul' x y := by
    obtain ⟨a, b, rfl⟩ := exists_coord m x
    obtain ⟨c, d, rfl⟩ := exists_coord m y
    simp [coord_mul]

@[simp] theorem firstHom_coord (m : ℕ) (a b : K m) :
    firstHom m (coord m a b) = Multiplicative.ofAdd a := by
  simp [firstHom]

theorem firstHom_surjective (m : ℕ) : Function.Surjective (firstHom m) := by
  intro a
  exact ⟨coord m a.toAdd 0, firstHom_coord m _ _⟩

def zeroHom (m : ℕ) : Multiplicative (K m) →* U m where
  toFun b := coord m 0 b.toAdd
  map_one' := coord_zero_zero m
  map_mul' b d := by simp [coord_mul]

theorem zeroHom_injective (m : ℕ) : Function.Injective (zeroHom m) := by
  intro b d h
  exact Multiplicative.toAdd.injective (coord_injective m h).2

def Z (m : ℕ) : Subgroup (U m) := (zeroHom m).range

theorem mem_Z_iff (m : ℕ) (x : U m) : x ∈ Z m ↔ ∃ b : K m, coord m 0 b = x := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b.toAdd, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨Multiplicative.ofAdd b, hb⟩

theorem firstHom_ker (m : ℕ) : (firstHom m).ker = Z m := by
  ext x
  obtain ⟨a, b, rfl⟩ := exists_coord m x
  constructor
  · intro h
    have ha : a = 0 := by simpa using congrArg Multiplicative.toAdd h
    exact (mem_Z_iff m _).mpr ⟨b, by rw [ha]⟩
  · rintro ⟨d, hd⟩
    have ha := (coord_injective m hd).1
    simp [MonoidHom.mem_ker, ha.symm]

theorem Z_le_center (m : ℕ) : Z m ≤ Subgroup.center (U m) := by
  intro x hx
  obtain ⟨b, rfl⟩ := (mem_Z_iff m x).mp hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨a, d, rfl⟩ := exists_coord m y
  change coord m a d * coord m 0 b = coord m 0 b * coord m a d
  simp [coord_mul, add_comm]

theorem paperCommutator_coord (m : ℕ) (a b c d : K m) :
    paperCommutator (coord m a b) (coord m c d) =
      coord m 0 (a * tits m c + c * tits m a) := by
  rw [paperCommutator, coord_inv, coord_inv, coord_mul, coord_mul, coord_mul]
  congr 1
  · calc
      a + c + a + c = (a + a) + (c + c) := by abel
      _ = 0 := by simp only [CharTwo.add_self_eq_zero]
  · have htwo : (2 : K m) = 0 := CharP.cast_eq_zero _ 2
    have hthree : (3 : K m) = 1 := by
      calc
        (3 : K m) = 2 + 1 := by norm_num
        _ = 1 := by rw [htwo, zero_add]
    ring_nf
    simp [htwo, hthree]

theorem commutator_le_Z (m : ℕ) : commutator (U m) ≤ Z m := by
  rw [← firstHom_ker]
  exact Abelianization.commutator_subset_ker (firstHom m)

theorem commutator_le_center (m : ℕ) : commutator (U m) ≤ Subgroup.center (U m) :=
  (commutator_le_Z m).trans (Z_le_center m)

def normHom (m : ℕ) : (K m)ˣ →* (K m)ˣ where
  toFun u := u * Units.map (tits m).toMonoidHom u
  map_one' := by simp
  map_mul' u v := by simp only [map_mul]; ac_rfl

@[simp] theorem normHom_coe (m : ℕ) (u : (K m)ˣ) :
    (normHom m u : K m) = (u : K m) * tits m (u : K m) := rfl

theorem normHom_injective (m : ℕ) : Function.Injective (normHom m) := by
  apply (normHom m).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro u hu
  apply Subgroup.mem_bot.mpr
  apply (binaryGaloisField_tits_norm_eq_one_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) u).mp
  exact congrArg (fun u : (K m)ˣ => (u : K m)) hu

theorem normHom_surjective (m : ℕ) : Function.Surjective (normHom m) :=
  Finite.surjective_of_injective (normHom_injective m)

theorem exists_nonfixed (m : ℕ) (hm : 0 < m) : ∃ c : K m, tits m c + c ≠ 0 := by
  have hex : ∃ c : K m, c ≠ 0 ∧ c ≠ 1 := by
    by_contra! h
    let f : Fin 2 → K m := fun i => if i = 0 then 0 else 1
    have hf : Function.Surjective f := by
      intro c
      by_cases hc : c = 0
      · exact ⟨0, by simp [f, hc]⟩
      · exact ⟨1, by simp [f, h c hc]⟩
    have hb : Nat.card (K m) ≤ 2 := by
      simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf
    rw [SuzukiTorusMovingRank.card_field] at hb
    have hp : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp
    omega
  obtain ⟨c, hc0, hc1⟩ := hex
  refine ⟨c, ?_⟩
  intro hc
  have hfix : tits m c = c := by
    have hh := congrArg (fun x : K m => x + c) hc
    simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hh
  have hsq : c ^ 2 = c := by
    rw [← SuzukiTorusMovingRank.tits_sq m, hfix, hfix]
  exact hc1 (mul_left_cancel₀ hc0 (by simpa only [pow_two, mul_one] using hsq))

/-- Every central coordinate is a single actual root commutator. -/
theorem zero_coord_mem_commutator (m : ℕ) (hm : 0 < m) (b : K m) :
    coord m 0 b ∈ commutator (U m) := by
  by_cases hb : b = 0
  · simp [hb]
  obtain ⟨c, hc⟩ := exists_nonfixed m hm
  let v : (K m)ˣ := Units.mk0 (b / (tits m c + c)) (div_ne_zero hb hc)
  obtain ⟨u, hu⟩ := normHom_surjective m v
  have hn : (u : K m) * tits m (u : K m) = b / (tits m c + c) :=
    congrArg (fun v : (K m)ˣ => (v : K m)) hu
  have he : paperCommutator (coord m (u : K m) 0) (coord m ((u : K m) * c) 0) =
      coord m 0 b := by
    rw [paperCommutator_coord]
    congr 1
    calc
      (u : K m) * tits m ((u : K m) * c) + (u : K m) * c * tits m (u : K m) =
          ((u : K m) * tits m (u : K m)) * (tits m c + c) := by rw [map_mul]; ring
      _ = b := by rw [hn]; exact div_mul_cancel₀ b hc
  rw [← he]
  exact paperCommutator_mem_commutator _ _

theorem commutator_eq_Z (m : ℕ) (hm : 0 < m) : commutator (U m) = Z m := by
  apply le_antisymm (commutator_le_Z m)
  intro x hx
  obtain ⟨b, rfl⟩ := (mem_Z_iff m x).mp hx
  exact zero_coord_mem_commutator m hm b

theorem commutator_eq_firstHom_ker (m : ℕ) (hm : 0 < m) :
    commutator (U m) = (firstHom m).ker := by
  rw [firstHom_ker, commutator_eq_Z m hm]

def derivedEquiv (m : ℕ) (hm : 0 < m) : commutator (U m) ≃* Multiplicative (K m) :=
  (MulEquiv.subgroupCongr (commutator_eq_Z m hm)).trans
    (MonoidHom.ofInjective (zeroHom_injective m)).symm

@[simp] theorem derivedEquiv_zero (m : ℕ) (hm : 0 < m) (b : K m) :
    derivedEquiv m hm ⟨coord m 0 b, zero_coord_mem_commutator m hm b⟩ =
      Multiplicative.ofAdd b := by
  exact (derivedEquiv m hm).apply_symm_apply (Multiplicative.ofAdd b)

def abelianizationEquiv (m : ℕ) (hm : 0 < m) :
    Abelianization (U m) ≃* Multiplicative (K m) :=
  (QuotientGroup.quotientMulEquivOfEq (commutator_eq_firstHom_ker m hm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (firstHom m) (firstHom_surjective m))

@[simp] theorem abelianizationEquiv_of (m : ℕ) (hm : 0 < m) (x : U m) :
    abelianizationEquiv m hm (Abelianization.of x) = firstHom m x := rfl

theorem derived_square (m : ℕ) (d : commutator (U m)) : d ^ 2 = 1 := by
  obtain ⟨b, hb⟩ := (mem_Z_iff m d.val).mp (commutator_le_Z m d.property)
  apply Subtype.ext
  change d.val ^ 2 = 1
  rw [← hb, pow_two, coord_mul]
  simp [CharTwo.add_self_eq_zero]

theorem derived_isElementaryAbelian (m : ℕ) : IsElementaryAbelian 2 (commutator (U m)) where
  toIsMulCommutative := by
    refine ⟨⟨?_⟩⟩
    intro x y
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (commutator_le_center m y.property) x.val)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (derived_square m)

theorem abelianization_square (m : ℕ) (hm : 0 < m) (a : Abelianization (U m)) : a ^ 2 = 1 := by
  apply (abelianizationEquiv m hm).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  change 2 • (abelianizationEquiv m hm a).toAdd = 0
  simp only [two_nsmul, CharTwo.add_self_eq_zero]

theorem abelianization_isElementaryAbelian (m : ℕ) (hm : 0 < m) :
    IsElementaryAbelian 2 (Abelianization (U m)) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (abelianization_square m hm)

end Kourovka2135.SuzukiRootDerivedCoordinates

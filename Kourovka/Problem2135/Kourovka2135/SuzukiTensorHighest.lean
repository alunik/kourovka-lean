import Kourovka2135.SuzukiTensorNatural
import Kourovka2135.SuzukiNaturalBorelFiltration

/-! The full natural Frobenius tensor has a genuine Borel-fixed highest
vector and dimension q². The actual Weyl element moves that vector. These
are the concrete inputs for the map from ovoid permutation augmentation;
no irreducibility or tensor-classification premise is assumed here. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.SuzukiTensorHighest

open SuzukiTorusMovingRank BenderSuzuki.MatrixGroups
open scoped Matrix MatrixGroups

/-- All Frobenius indices, including the unique index when m = 0. -/
def fullIndices (m : ℕ) : Finset (Fin (2 * m + 1)) := Finset.univ

theorem fullIndices_nonempty (m : ℕ) : (fullIndices m).Nonempty :=
  ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

variable (k : Type u) [Field k] [CharP k 2] (m : ℕ)

abbrev FullSpace := SuzukiTensorNatural.TensorSpace k m (fullIndices m)

abbrev representation (σ : K m →+* k) :=
  SuzukiTensorNatural.representation k m (fullIndices m) σ

abbrev highest : FullSpace k m := SuzukiTensorNatural.highest k m (fullIndices m)
abbrev lowest : FullSpace k m := SuzukiTensorNatural.lowest k m (fullIndices m)

omit [CharP k 2] in
theorem finrank_full : Module.finrank k (FullSpace k m) = (SuzukiGeometry.q m) ^ 2 := by
  rw [SuzukiTensorNatural.finrank_tensor]
  simp only [fullIndices, Finset.card_univ, Fintype.card_fin]
  change 4 ^ (2 * m + 1) = (2 ^ (2 * m + 1)) ^ 2
  rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_mul]
  congr 1
  omega

omit [CharP k 2] in
theorem highest_ne_zero : highest k m ≠ 0 :=
  SuzukiTensorNatural.highest_ne_zero k m (fullIndices m)

omit [CharP k 2] in
theorem highest_ne_lowest : highest k m ≠ lowest k m :=
  SuzukiTensorNatural.highest_ne_lowest k m (fullIndices m) (fullIndices_nonempty m)

/-- The binary exponents sum to the order of the finite-field unit group. -/
theorem sum_binary_powers (n : ℕ) : (∑ i : Fin n, 2 ^ i.val) = 2 ^ n - 1 := by
  have h : (∑ i : Fin n, 2 ^ i.val) + 1 = 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [pow_succ]
        omega
  omega

omit [CharP k 2] in
/-- The actual product of all highest torus weights is one. -/
theorem full_torus_weight (σ : K m →+* k) (u : (K m)ˣ) :
    (∏ i : fullIndices m,
      (σ ((u : K m) ^ (1 + 2 ^ m))) ^ (2 ^ i.val.val)) = 1 := by
  change (∏ i : (Finset.univ : Finset (Fin (2 * m + 1))),
    (σ ((u : K m) ^ (1 + 2 ^ m))) ^ (2 ^ i.val.val)) = 1
  rw [Finset.prod_coe_sort (Finset.univ : Finset (Fin (2 * m + 1)))
    (fun i : Fin (2 * m + 1) => (σ ((u : K m) ^ (1 + 2 ^ m))) ^ (2 ^ i.val)),
    Finset.prod_pow_eq_pow_sum, sum_binary_powers]
  have hp : ((u : K m) ^ (1 + 2 ^ m)) ^ (2 ^ (2 * m + 1) - 1) = 1 := by
    let : Fintype (K m) := Fintype.ofFinite _
    have he := FiniteField.pow_card_sub_one_eq_one
      ((u : K m) ^ (1 + 2 ^ m)) (pow_ne_zero _ u.ne_zero)
    simpa only [← Nat.card_eq_fintype_card, card_field] using he
  simpa only [map_pow, map_one] using congrArg σ hp

theorem torus_fixes_highest (σ : K m →+* k) (u : (K m)ˣ) :
    representation k m σ (torusHom m u) (highest k m) = highest k m := by
  rw [SuzukiTensorNatural.representation_torus_highest, full_torus_weight, one_smul]

theorem root_fixes_highest (σ : K m →+* k) (a b : K m) :
    representation k m σ (SuzukiTensorNatural.rootElement m a b) (highest k m) =
      highest k m :=
  SuzukiTensorNatural.representation_root_highest k m (fullIndices m) σ a b

/-- Every actual Borel element fixes the full highest tensor. -/
theorem borel_fixes_highest (σ : K m →+* k) (g : SuzukiGeometry.borel m) :
    representation k m σ (g : G m) (highest k m) = highest k m := by
  obtain ⟨a, b, u, hg⟩ := SuzukiNaturalBorelFiltration.exists_root_torus m g
  have he : (g : G m) = SuzukiTensorNatural.rootElement m a b * torusHom m u :=
    Subtype.ext hg
  rw [he, map_mul]
  change representation k m σ (SuzukiTensorNatural.rootElement m a b)
    (representation k m σ (torusHom m u) (highest k m)) = highest k m
  rw [torus_fixes_highest, root_fixes_highest]

/-- The same fixed-vector statement in the actual point-stabilizer type. -/
theorem stabilizer_fixes_highest (σ : K m →+* k)
    (g : MulAction.stabilizer (G m) (SuzukiGeometry.infinityOvoid m)) :
    representation k m σ (g : G m) (highest k m) = highest k m := by
  have hg : (g : G m) ∈ SuzukiGeometry.borel m := by
    rw [SuzukiGeometry.borel_eq_stabilizer_infinity]
    exact g.property
  exact borel_fixes_highest k m σ ⟨g, hg⟩

theorem weyl_highest (σ : K m →+* k) :
    representation k m σ (SuzukiTensorNatural.weyl m) (highest k m) = lowest k m :=
  SuzukiTensorNatural.representation_weyl_highest k m (fullIndices m) σ

/-- The induced permutation map will be nonconstant, including in the smallest field. -/
theorem weyl_moves_highest (σ : K m →+* k) :
    representation k m σ (SuzukiTensorNatural.weyl m) (highest k m) ≠ highest k m := by
  rw [weyl_highest]
  exact (highest_ne_lowest k m).symm

end Kourovka2135.SuzukiTensorHighest

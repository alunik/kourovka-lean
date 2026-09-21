import Kourovka2135.SuzukiBruhat
import Kourovka2135.BinarySplitSylow
import Kourovka2135.FocalLift

/-! Actual cyclic Sylow subgroups at split primes of the concrete Suzuki
matrix group. The proved cardinality gives a prime-to-r torus index; actual
Sylow conjugacy places every r-element inside that torus. No recognition,
conjugacy classification, or good-set premise is used. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiSplitSylow

open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open SuzukiGeometry
open SuzukiTorusMovingRank (torusHom torusHom_injective orderOf_torus)

/-- Prime-power elements conjugate into any subgroup of prime-to-p index. -/
theorem exists_conj_mem_of_not_dvd_index
    {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    (H : Subgroup A) (hindex : ¬ p ∣ H.index) {x : A}
    (hx : ∃ n : ℕ, orderOf x = p ^ n) :
    ∃ g : A, g * x * g⁻¹ ∈ H := by
  let Q : Sylow p H := Sylow.nonempty.some
  let T : Subgroup A := (Q : Subgroup H).map H.subtype
  have hT : IsPGroup p T := Q.isPGroup'.map H.subtype
  have hTi : ¬ p ∣ T.index := by
    dsimp only [T]
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul Q.not_dvd_index hindex
  obtain ⟨g, hg⟩ := FocalLift.exists_conj_mem_sylow (hT.toSylow hTi) hx
  refine ⟨g, ?_⟩
  change g * x * g⁻¹ ∈ T at hg
  obtain ⟨z, _, hz⟩ := hg
  exact hz ▸ z.property

/-- The actual torus parameter homomorphism restricted to its concrete subgroup. -/
def parameterHom (m : ℕ) : (K m)ˣ →* torus m :=
  (torusHom m).codRestrict (torus m) (fun u => by
    change SuzukiTorusGL m u ∈ torusGL m
    exact Subgroup.subset_closure ⟨u, rfl⟩)

theorem parameterHom_bijective (m : ℕ) : Function.Bijective (parameterHom m) := by
  constructor
  · intro x y hxy
    apply torusHom_injective m
    exact congrArg (fun z : torus m => (z : G m)) hxy
  · intro t
    have ht : ((t : G m) : GL (Fin 4) (K m)) ∈ torusGL m := t.property
    obtain ⟨u, hu⟩ := (suzukiTorusGL_mem_closure_iff m _).mp ht
    refine ⟨u, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hu.symm

def parameterEquiv (m : ℕ) : (K m)ˣ ≃* torus m :=
  MulEquiv.ofBijective (parameterHom m) (parameterHom_bijective m)

@[simp] theorem parameterEquiv_coe (m : ℕ) (u : (K m)ˣ) :
    ((parameterEquiv m u : torus m) : G m) = torusHom m u := rfl

theorem torus_isCyclic (m : ℕ) : IsCyclic (torus m) :=
  isCyclic_of_surjective (parameterEquiv m).toMonoidHom (parameterEquiv m).surjective

theorem index_torus (m : ℕ) : (torus m).index = (q m) ^ 2 * ((q m) ^ 2 + 1) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt (one_lt_q m))
  calc
    (q m - 1) * (torus m).index = Nat.card (G m) := by
      rw [← card_torus]
      exact (torus m).card_mul_index
    _ = (q m - 1) * ((q m) ^ 2 * ((q m) ^ 2 + 1)) := by rw [card_group]; ring

theorem odd_q_sub_one (m : ℕ) : Odd (q m - 1) := by
  have hq := one_lt_q m
  have he := Nat.even_iff.mp (even_q m)
  exact Nat.odd_iff.mpr (by omega)

variable {r : ℕ} [Fact r.Prime]

omit [Fact r.Prime] in
theorem split_prime_odd (m : ℕ) (hr : r ∣ q m - 1) : Odd r :=
  (odd_q_sub_one m).of_dvd_nat hr

theorem not_dvd_index_torus (m : ℕ) (hr : r ∣ q m - 1) :
    ¬ r ∣ (torus m).index := by
  have hq := one_lt_q m
  have hp : r.Prime := Fact.out
  have hrq : ¬ r ∣ q m := by
    intro hd
    have h1 := Nat.dvd_sub hd hr
    have heq : q m - (q m - 1) = 1 := by omega
    rw [heq] at h1
    exact hp.not_dvd_one h1
  have hfactor : (q m) ^ 2 - 1 = (q m - 1) * (q m + 1) := by
    have hsub : q m - 1 + 1 = q m := Nat.sub_add_cancel (by omega)
    have hsq : 1 ≤ (q m) ^ 2 := by nlinarith
    have hsqsub := Nat.sub_add_cancel hsq
    nlinarith
  have hrsq : r ∣ (q m) ^ 2 - 1 := by
    rw [hfactor]
    exact dvd_mul_of_dvd_left hr (q m + 1)
  have hrqp : ¬ r ∣ (q m) ^ 2 + 1 := by
    intro hd
    have h2 := Nat.dvd_sub hd hrsq
    have heq : (q m) ^ 2 + 1 - ((q m) ^ 2 - 1) = 2 := by
      have hs : 1 ≤ (q m) ^ 2 := by nlinarith
      omega
    rw [heq] at h2
    have hrone : r = 1 :=
      Nat.eq_one_of_dvd_coprimes (split_prime_odd m hr).coprime_two_right (dvd_refl r) h2
    exact hp.ne_one hrone
  rw [index_torus]
  exact hp.not_dvd_mul (fun h => hrq (hp.dvd_of_dvd_pow h)) hrqp

theorem sylow_isCyclic (m : ℕ) (hr : r ∣ q m - 1) (P : Sylow r (G m)) :
    IsCyclic P := by
  let : IsCyclic (torus m) := torus_isCyclic m
  exact BinarySplitSylow.isCyclic_sylow_of_cyclic_index (torus m)
    (not_dvd_index_torus m hr) P

theorem pSubgroup_isCyclic (m : ℕ) (hr : r ∣ q m - 1)
    (S : Subgroup (G m)) (hS : IsPGroup r S) : IsCyclic S := by
  let : IsCyclic (torus m) := torus_isCyclic m
  exact BinarySplitSylow.isCyclic_pSubgroup_of_cyclic_index (torus m)
    (not_dvd_index_torus m hr) S hS

theorem subgroup_sylow_isCyclic (m : ℕ) (hr : r ∣ q m - 1)
    (H : Subgroup (G m)) (P : Sylow r H) : IsCyclic P := by
  let : IsCyclic ((P : Subgroup H).map H.subtype) :=
    pSubgroup_isCyclic m hr ((P : Subgroup H).map H.subtype)
      (P.isPGroup'.map H.subtype)
  apply isCyclic_of_injective (H.subtype.subgroupMap (P : Subgroup H))
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : ((P : Subgroup H).map H.subtype) => (z : G m)) h

/-- Actual conjugacy to a split-torus parameter of the same prime order. -/
theorem exists_isConj_torus_of_order_prime (m : ℕ) (hr : r ∣ q m - 1)
    (x : G m) (hx : orderOf x = r) :
    ∃ u : (K m)ˣ, orderOf u = r ∧ IsConj (torusHom m u) x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index (torus m)
    (not_dvd_index_torus m hr) (x := x) ⟨1, by simpa using hx⟩
  obtain ⟨u, hu⟩ := (parameterEquiv m).surjective ⟨g * x * g⁻¹, hg⟩
  have he : torusHom m u = g * x * g⁻¹ :=
    congrArg (fun z : torus m => (z : G m)) hu
  refine ⟨u, ?_, (isConj_iff.mpr ⟨g, he.symm⟩).symm⟩
  calc
    orderOf u = orderOf (torusHom m u) := (orderOf_torus m u).symm
    _ = orderOf (g * x * g⁻¹) := congrArg orderOf he
    _ = orderOf x := (MulAut.conj g).orderOf_eq x
    _ = r := hx

end Kourovka2135.SuzukiSplitSylow

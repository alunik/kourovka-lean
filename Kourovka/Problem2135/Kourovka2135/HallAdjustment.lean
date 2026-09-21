import Kourovka2135.Hall
import Kourovka2135.GeneratingSets

/-!
# Hall adjustment of a coprime-order element

If two p′-elements commute modulo a normal p-subgroup of a finite soluble
group, one can conjugate the second by that subgroup so that they commute.
The normal p-subgroup is not assumed commutative.
-/

set_option autoImplicit false
universe u

namespace Kourovka2135.Hall

variable {G : Type u} [Group G]

private theorem commute_quotient_on_sup_zpowers
    (P : Subgroup G) [P.Normal] (x a z : G)
    (hzx : Commute (QuotientGroup.mk' P z) (QuotientGroup.mk' P x))
    (hza : Commute (QuotientGroup.mk' P z) (QuotientGroup.mk' P a))
    {y : G} (hy : y ∈ (P ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers a) :
    Commute (QuotientGroup.mk' P z) (QuotientGroup.mk' P y) := by
  let q := QuotientGroup.mk' P
  let C : Subgroup G := (Subgroup.centralizer ({q z} : Set (G ⧸ P))).comap q
  have hPC : P ≤ C := by
    intro t ht
    change q t ∈ Subgroup.centralizer ({q z} : Set (G ⧸ P))
    have hqt : q t = 1 := (QuotientGroup.eq_one_iff (N := P) t).mpr ht
    rw [hqt]
    exact Subgroup.one_mem _
  have hxC : Subgroup.zpowers x ≤ C := by
    apply Subgroup.zpowers_le.mpr
    change q x ∈ Subgroup.centralizer ({q z} : Set (G ⧸ P))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzx.symm.eq
  have haC : Subgroup.zpowers a ≤ C := by
    apply Subgroup.zpowers_le.mpr
    change q a ∈ Subgroup.centralizer ({q z} : Set (G ⧸ P))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hza.symm.eq
  have hyC := (sup_le (sup_le hPC hxC) haC) hy
  change q y ∈ Subgroup.centralizer ({q z} : Set (G ⧸ P)) at hyC
  change q z * q y = q y * q z
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm

private theorem zpowers_isPiSubgroup_prime_ne {p : ℕ} {x : G}
    (hx : ¬ p ∣ orderOf x) :
    IsPiSubgroup {q : Nat.Primes | q.val ≠ p} (Subgroup.zpowers x) := by
  intro q hq
  change q.val ≠ p
  intro heq
  apply hx
  rw [← heq]
  simpa only [Nat.card_zpowers] using hq

/-- A p′-element commuting with another modulo a normal p-subgroup has a
conjugate by that subgroup which commutes with the other element. -/
theorem exists_conj_commute_of_commutator_mem_pSubgroup
    [Finite G] {p : ℕ} (hp : p.Prime) (hsolv : Group.IsSolvable G)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P) {x a : G}
    (hxp : ¬ p ∣ orderOf x) (hap : ¬ p ∣ orderOf a)
    (hxa : paperCommutator x a ∈ P) :
    ∃ u ∈ P, Commute x (u⁻¹ * a * u) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Group.IsSolvable G := hsolv
  let L : Subgroup G := (P ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers a
  have hPL : P ≤ L := le_sup_left.trans le_sup_left
  have hxL : x ∈ L :=
    (show P ⊔ Subgroup.zpowers x ≤ L from le_sup_left)
      ((show Subgroup.zpowers x ≤ P ⊔ Subgroup.zpowers x from le_sup_right)
        (Subgroup.mem_zpowers x))
  have haL : a ∈ L :=
    (show Subgroup.zpowers a ≤ L from le_sup_right) (Subgroup.mem_zpowers a)
  let xL : L := ⟨x, hxL⟩
  let aL : L := ⟨a, haL⟩
  let P₀ : Subgroup L := P.subgroupOf L
  let π : Set Nat.Primes := {q | q.val ≠ p}
  let q : G →* G ⧸ P := QuotientGroup.mk' P
  have hqxqa : Commute (q x) (q a) := by
    apply (paperCommutator_eq_one_iff _ _).mp
    have hzero : q (paperCommutator x a) = 1 :=
      (QuotientGroup.eq_one_iff (N := P) _).mpr hxa
    simpa only [paperCommutator, map_mul, map_inv] using hzero
  have hxcentral (z : L) : Commute (q x) (q (z : G)) :=
    commute_quotient_on_sup_zpowers P x a x (Commute.refl _) hqxqa z.property
  have hacentral (z : L) : Commute (q a) (q (z : G)) :=
    commute_quotient_on_sup_zpowers P x a a hqxqa.symm (Commute.refl _) z.property
  have hxpi : IsPiSubgroup π (Subgroup.zpowers xL) :=
    zpowers_isPiSubgroup_prime_ne (by simpa only [xL, Subgroup.orderOf_mk] using hxp)
  have hapi : IsPiSubgroup π (Subgroup.zpowers aL) :=
    zpowers_isPiSubgroup_prime_ne (by simpa only [aL, Subgroup.orderOf_mk] using hap)
  obtain ⟨H, hH, hxHle⟩ := exists_hall_containing (G := L)
    (by infer_instance) π (Subgroup.zpowers xL) hxpi
  have hxH : xL ∈ H := hxHle (Subgroup.mem_zpowers xL)
  have hHnot : ¬ p ∣ Nat.card H := by
    intro hd
    have hmem := hH.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hd
    exact hmem rfl
  have hinter (z : L) (hzH : z ∈ H) (hzP : (z : G) ∈ P) : z = 1 := by
    by_contra hne
    have hneP : (⟨(z : G), hzP⟩ : P) ≠ 1 := by
      intro heq
      apply hne
      apply Subtype.ext
      exact congrArg (fun v : P => (v : G)) heq
    have hdiv : p ∣ orderOf (z : G) := by
      simpa only [Subgroup.orderOf_mk] using hP.dvd_orderOf hneP
    have hdivL : p ∣ orderOf z := by
      simpa only [Subgroup.orderOf_coe] using hdiv
    exact hHnot (hdivL.trans (H.orderOf_dvd_natCard hzH))
  have hxcomm (z : L) (hz : z ∈ H) : Commute xL z := by
    apply (paperCommutator_eq_one_iff _ _).mp
    have hcH : paperCommutator xL z ∈ H := by
      exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hxH) (H.inv_mem hz)) hxH) hz
    have hcP : ((paperCommutator xL z : L) : G) ∈ P := by
      apply (QuotientGroup.eq_one_iff (N := P) _).mp
      change q (paperCommutator x (z : G)) = 1
      have hc := (paperCommutator_eq_one_iff _ _).mpr (hxcentral z)
      simpa only [paperCommutator, map_mul, map_inv] using hc
    exact hinter _ hcH hcP
  obtain ⟨g, hg⟩ := exists_le_conjugate_hall (G := L)
    (by infer_instance) (Subgroup.zpowers aL) H hapi hH
  obtain ⟨b, hb, hba⟩ := hg (Subgroup.mem_zpowers aL)
  have hconjQ : q (g : G) * q (b : G) * (q (g : G))⁻¹ = q a := by
    have heq := congrArg (fun z : L => q (z : G)) hba
    change q ((g * b * g⁻¹ : L) : G) = q a at heq
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using heq
  have hqb : q (b : G) = q a := by
    calc
      q (b : G) = (q (g : G))⁻¹ *
          (q (g : G) * q (b : G) * (q (g : G))⁻¹) * q (g : G) := by group
      _ = (q (g : G))⁻¹ * q a * q (g : G) := by rw [hconjQ]
      _ = q a := by
        rw [(hacentral g).symm.inv_left.eq]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hadiff : aL * b⁻¹ ∈ P₀ := by
    change a * (b : G)⁻¹ ∈ P
    apply (QuotientGroup.eq_one_iff (N := P) _).mp
    change q (a * (b : G)⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]
  have haPH : aL ∈ P₀ ⊔ H := by
    have hd : aL * b⁻¹ ∈ P₀ ⊔ H := (show P₀ ≤ P₀ ⊔ H from le_sup_left) hadiff
    have hb' : b ∈ P₀ ⊔ H := (show H ≤ P₀ ⊔ H from le_sup_right) hb
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (P₀ ⊔ H).mul_mem hd hb'
  have hPH : P₀ ⊔ H = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [← MonoidHom.range_eq_map, L.range_subtype]
    apply le_antisymm (Subgroup.map_subtype_le _) ?_
    change (P ⊔ Subgroup.zpowers x) ⊔ Subgroup.zpowers a ≤ _
    apply sup_le (sup_le ?_ ?_) ?_
    · intro z hz
      exact ⟨⟨z, hPL hz⟩, (show P₀ ≤ P₀ ⊔ H from le_sup_left) hz, rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨xL, (show H ≤ P₀ ⊔ H from le_sup_right) hxH, rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨aL, haPH, rfl⟩
  obtain ⟨u, hu, hua⟩ := exists_le_conjugate_hall_by_normal_subgroup (G := L)
    (by infer_instance) (Subgroup.zpowers aL) H P₀ hapi hH hPH
  have hau : u⁻¹ * aL * u ∈ H := by
    obtain ⟨c, hc, heq⟩ := hua (Subgroup.mem_zpowers aL)
    rw [← heq]
    simpa [MulAut.conj_apply, mul_assoc] using hc
  refine ⟨(u : G), hu, ?_⟩
  exact (hxcomm _ hau).map L.subtype

end Kourovka2135.Hall

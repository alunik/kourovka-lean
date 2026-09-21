import Kourovka2135.RelativeVerbal
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! Central stem kernels above a dihedral generating pair have size at most two.

Only the actual inversion relation is used. In a central extension, the
derived subgroup lies in a cyclic subgroup on which the second lift acts
by inversion. Its central elements consequently have square one. The
argument assumes neither a Schur multiplier nor a cohomology computation.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.DihedralCentralStem

variable {E Q : Type*} [Group E] [Group Q]

private theorem closure_lifts_kernel (π : E →* Q) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤) :
    Subgroup.closure (({a, b} : Set E) ∪ π.ker) = ⊤ := by
  let H := Subgroup.closure (({a, b} : Set E) ∪ π.ker)
  have hker : π.ker ≤ H := fun _ h => Subgroup.subset_closure (Or.inr h)
  have ha : a ∈ H := Subgroup.subset_closure (Or.inl (by simp))
  have hb : b ∈ H := Subgroup.subset_closure (Or.inl (by simp))
  have hm : H.map π = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    apply (Subgroup.closure_le _).2
    intro q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq
    · exact Subgroup.mem_map_of_mem π ha
    · have : q = π b := Set.mem_singleton_iff.mp hq
      subst q
      exact Subgroup.mem_map_of_mem π hb
  apply top_le_iff.mp
  intro e _
  obtain ⟨h, hh, he⟩ := (show π e ∈ H.map π by rw [hm]; trivial)
  have hk : e * h⁻¹ ∈ π.ker := by simp [MonoidHom.mem_ker, he]
  simpa using H.mul_mem (hker hk) hh

/-- The actual derived subgroup lies in a cyclic subgroup inverted by b.
No order or square relation on the quotient generators is required. -/
theorem exists_inverted_cyclic_container (π : E →* Q)
    (hcentral : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤)
    (hconj : π b * π a * (π b)⁻¹ = (π a)⁻¹) :
    ∃ d : E, commutator E ≤ Subgroup.zpowers d ∧ b * d * b⁻¹ = d⁻¹ := by
  let z := a * (b * a * b⁻¹)
  have hzker : z ∈ π.ker := by
    simp only [z, MonoidHom.mem_ker, map_mul, map_inv, hconj, mul_inv_cancel]
  have hz := hcentral hzker
  have haz : Commute a z := Subgroup.mem_center_iff.mp hz a
  have hbz : Commute b z := Subgroup.mem_center_iff.mp hz b
  let θ : E ≃* E := MulAut.conj b
  have haθ : θ a = a⁻¹ * z := by dsimp [θ, z]; group
  have hzθ : θ z = z := by
    change b * z * b⁻¹ = z
    rw [hbz.eq, mul_inv_cancel_right]
  have hθ2 : θ (θ a) = a := by
    rw [haθ, map_mul, map_inv, hzθ, haθ, mul_inv_rev, inv_inv]
    rw [← haz.inv_right.eq, mul_assoc, inv_mul_cancel, mul_one]
  let d := θ a * a⁻¹
  have had : Commute a d := by
    dsimp only [d]
    rw [haθ]
    exact ((Commute.refl a).inv_right.mul_right haz).mul_right
      (Commute.refl a).inv_right
  have hbd : b * d * b⁻¹ = d⁻¹ := by
    change θ d = d⁻¹
    dsimp only [d]
    rw [map_mul, map_inv, hθ2, mul_inv_rev, inv_inv]
  let D := Subgroup.zpowers d
  have haD : a ∈ Subgroup.normalizer (D : Set E) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * d * a⁻¹) = Subgroup.zpowers d
    rw [had.eq, mul_inv_cancel_right]
  have hbD : b ∈ Subgroup.normalizer (D : Set E) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (b * d * b⁻¹) = Subgroup.zpowers d
    rw [hbd, Subgroup.zpowers_inv]
  have hRD : π.ker ≤ Subgroup.normalizer (D : Set E) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (r * d * r⁻¹) = Subgroup.zpowers d
    rw [← Subgroup.mem_center_iff.mp (hcentral hr) d, mul_inv_cancel_right]
  have hDnormal : D.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← closure_lifts_kernel π a b hgen]
    apply (Subgroup.closure_le _).2
    intro r hr
    rcases hr with hr | hr
    · rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact haD
      · exact Set.mem_singleton_iff.mp hr ▸ hbD
    · exact hRD hr
  let : D.Normal := hDnormal
  have habD : paperCommutator a b ∈ D := by
    have hf : Commute ((QuotientGroup.mk' D) b) ((QuotientGroup.mk' D) a) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      change (QuotientGroup.mk' D) d = 1
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers d)
    apply (QuotientGroup.eq_one_iff _).mp
    change paperCommutator ((QuotientGroup.mk' D) a) ((QuotientGroup.mk' D) b) = 1
    exact (paperCommutator_eq_one_iff _ _).mpr hf.symm
  have hbaD : paperCommutator b a ∈ D := by
    have : paperCommutator b a = (paperCommutator a b)⁻¹ := by
      simp only [paperCommutator]; group
    rw [this]
    exact D.inv_mem habD
  refine ⟨d, ?_, hbd⟩
  have h := commutator_closure_le_of_paperCommutators
    (({a, b} : Set E) ∪ π.ker) (({a, b} : Set E) ∪ π.ker) D ?_
  · simpa only [closure_lifts_kernel π a b hgen, commutator_def] using h
  intro s hs t ht
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simp [paperCommutator]
    · exact habD
    · exact hbaD
    · simp [paperCommutator]
  · have hc : Commute s t := Subgroup.mem_center_iff.mp (hcentral ht) s
    rw [(paperCommutator_eq_one_iff _ _).mpr hc]
    exact D.one_mem
  · have hc : Commute s t := (Subgroup.mem_center_iff.mp (hcentral hs) t).symm
    rw [(paperCommutator_eq_one_iff _ _).mpr hc]
    exact D.one_mem
  · have hc : Commute s t := Subgroup.mem_center_iff.mp (hcentral ht) s
    rw [(paperCommutator_eq_one_iff _ _).mpr hc]
    exact D.one_mem

/-- Any central element in the derived subgroup has square one. -/
theorem pow_two_eq_one_of_mem_ker_inf_commutator (π : E →* Q)
    (hcentral : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤)
    (hconj : π b * π a * (π b)⁻¹ = (π a)⁻¹)
    (r : E) (hr : r ∈ π.ker ⊓ commutator E) : r ^ 2 = 1 := by
  obtain ⟨d, hD, hbd⟩ := exists_inverted_cyclic_container π hcentral a b hgen hconj
  obtain ⟨n, hn⟩ := hD hr.2
  have hinv : b * r * b⁻¹ = r⁻¹ := by
    rw [← hn]
    change (MulAut.conj b) (d ^ n) = (d ^ n)⁻¹
    rw [map_zpow]
    change (b * d * b⁻¹) ^ n = (d ^ n)⁻¹
    rw [hbd, inv_zpow]
  have hfix : b * r * b⁻¹ = r := by
    rw [Subgroup.mem_center_iff.mp (hcentral hr.1) b, mul_inv_cancel_right]
  simpa only [pow_two] using eq_inv_iff_mul_eq_one.mp (hfix.symm.trans hinv)

/-- The part of the kernel in the derived subgroup is itself cyclic. -/
theorem ker_inf_commutator_isCyclic (π : E →* Q)
    (hcentral : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤)
    (hconj : π b * π a * (π b)⁻¹ = (π a)⁻¹) :
    IsCyclic (π.ker ⊓ commutator E : Subgroup E) := by
  obtain ⟨d, hD, _⟩ := exists_inverted_cyclic_container π hcentral a b hgen hconj
  exact Subgroup.isCyclic_of_le (inf_le_right.trans hD)

/-- A finite central extension has at most two kernel elements in its
derived subgroup. -/
theorem card_ker_inf_commutator_le_two [Finite E] (π : E →* Q)
    (hcentral : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤)
    (hconj : π b * π a * (π b)⁻¹ = (π a)⁻¹) :
    Nat.card (π.ker ⊓ commutator E : Subgroup E) ≤ 2 := by
  classical
  let R := π.ker ⊓ commutator E
  let : Fintype R := Fintype.ofFinite _
  let : IsCyclic R := ker_inf_commutator_isCyclic π hcentral a b hgen hconj
  have hs (r : R) : r ^ 2 = 1 := Subtype.ext
    (pow_two_eq_one_of_mem_ker_inf_commutator π hcentral a b hgen hconj r r.property)
  have he := IsCyclic.card_pow_eq_one_le (α := R) (n := 2) (by decide)
  simpa only [hs, Finset.filter_true, Finset.card_univ, Nat.card_eq_fintype_card] using he

/-- In particular, every finite central stem extension of the actual
dihedral generating relations has kernel of cardinality at most two. -/
theorem card_ker_le_two [Finite E] (π : E →* Q)
    (hcentral : π.ker ≤ Subgroup.center E) (a b : E)
    (hgen : Subgroup.closure ({π a, π b} : Set Q) = ⊤)
    (hconj : π b * π a * (π b)⁻¹ = (π a)⁻¹)
    (hstem : π.ker ≤ commutator E) : Nat.card π.ker ≤ 2 := by
  simpa only [inf_eq_left.mpr hstem] using
    card_ker_inf_commutator_le_two π hcentral a b hgen hconj

end Kourovka2135.DihedralCentralStem

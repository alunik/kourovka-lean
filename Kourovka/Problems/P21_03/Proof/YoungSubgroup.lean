import Kourovka.Problems.P21_03.Proof.YoungConfiguration

/-!
# Young subgroups and the simplicity criterion
-/

open scoped Pointwise

namespace Kourovka213

/-- The direct product of the full symmetric groups on the fibers of `P.block`. -/
def youngSubgroup (P : BoundedPartition n) : Subgroup (Sym n) where
  carrier := {sigma | ∀ x, P.block (sigma x) = P.block x}
  one_mem' := by simp
  mul_mem' {sigma tau} hs ht x := by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hs (tau x), ht x]
  inv_mem' {sigma} hs x := by
    have h := hs (sigma⁻¹ x)
    simpa using h.symm

@[simp]
theorem mem_youngSubgroup {P : BoundedPartition n} {sigma : Sym n} :
    sigma ∈ youngSubgroup P ↔ ∀ x, P.block (sigma x) = P.block x := Iff.rfl

theorem mem_conjugate_iff {G : Type*} [Group G] (K : Subgroup G) (x g : G) :
    g ∈ (MulAut.conj x⁻¹ • K) ↔ x * g * x⁻¹ ∈ K := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, MulAut.conj_apply]

/-- The intersection of two Young subgroups in relative position `sigma` is trivial exactly
when every left-block/right-block cell has size at most one. -/
theorem disjoint_youngSubgroup_conjugate_iff_isSimple
    (P Q : BoundedPartition n) (sigma : Sym n) :
    Disjoint (youngSubgroup P) (conjugate (youngSubgroup Q) sigma) ↔ IsSimple P Q sigma := by
  classical
  constructor
  · intro hdisj
    rw [Subgroup.disjoint_def] at hdisj
    intro a b hab hP
    intro hQ
    let tau : Sym n := Equiv.swap a b
    have htauP : tau ∈ youngSubgroup P := by
      intro x
      by_cases hxa : x = a
      · subst x
        simp [tau, hP]
      · by_cases hxb : x = b
        · subst x
          simp [tau, hP.symm]
        · simp [tau, Equiv.swap_apply_def, hxa, hxb]
    have htauQ : tau ∈ conjugate (youngSubgroup Q) sigma := by
      rw [conjugate, mem_conjugate_iff]
      intro y
      simp only [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_inv,
        Equiv.symm_apply_apply]
      by_cases hya : sigma.symm y = a
      · have hy : y = sigma a := by
          calc
            y = sigma (sigma.symm y) := (sigma.apply_symm_apply y).symm
            _ = sigma a := congrArg sigma hya
        rw [hya, hy]
        change Q.block (sigma ((Equiv.swap a b) a)) = Q.block (sigma a)
        rw [Equiv.swap_apply_left]
        exact hQ.symm
      · by_cases hyb : sigma.symm y = b
        · have hy : y = sigma b := by
            calc
              y = sigma (sigma.symm y) := (sigma.apply_symm_apply y).symm
              _ = sigma b := congrArg sigma hyb
          rw [hyb, hy]
          change Q.block (sigma ((Equiv.swap a b) b)) = Q.block (sigma b)
          rw [Equiv.swap_apply_right]
          exact hQ
        · simp [tau, Equiv.swap_apply_def, hya, hyb]
    have htau_one := hdisj htauP htauQ
    exact hab (Equiv.swap_eq_one_iff.mp htau_one)
  · intro hs
    rw [Subgroup.disjoint_def]
    intro g hgP hgQ
    apply Equiv.ext
    intro a
    change g a = a
    by_contra hga
    have hP := (mem_youngSubgroup.mp hgP) a
    have hgQ' : sigma * g * sigma⁻¹ ∈ youngSubgroup Q := by
      exact (mem_conjugate_iff (youngSubgroup Q) sigma g).mp (by simpa [conjugate] using hgQ)
    have hQ := (mem_youngSubgroup.mp hgQ') (sigma a)
    have hQ' : Q.block (sigma (g a)) = Q.block (sigma a) := by simpa using hQ
    exact (hs (Ne.symm hga) hP.symm) hQ'.symm

end Kourovka213

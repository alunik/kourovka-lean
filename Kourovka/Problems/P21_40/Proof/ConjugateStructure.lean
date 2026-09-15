import Kourovka.Problems.P21_40.Proof.Unipotent

/-!
# Structural consequences of a rational unitriangular change of basis

The subgroup itself is isomorphic to its conjugate image, so the unitriangular
nilpotency bound and torsion-freeness transfer without changing the subgroup.
-/

namespace Kourovka.P21_40

/-- A subgroup conjugate into the upper-unitriangular matrices is torsion-free
and nilpotent of class at most the matrix dimension minus one. -/
theorem nilpotent_torsionFree_of_conjugate_upperUnitriangular
    {n : ℕ} {G : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ)}
    {K : Subgroup G} (P : Matrix.GeneralLinearGroup (Fin n) ℚ)
    (hP : ∀ g : G, g ∈ K → IsUpperUnitriangular
      ((P⁻¹ * (g : Matrix.GeneralLinearGroup (Fin n) ℚ) * P :
        Matrix.GeneralLinearGroup (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ)) :
    Group.IsNilpotent K ∧ Group.nilpotencyClass K ≤ n - 1 ∧
      (∀ g : K, IsOfFinOrder g → g = 1) := by
  let f : K →* Matrix.GeneralLinearGroup (Fin n) ℚ :=
    { toFun := fun g => P⁻¹ * (g.1 : Matrix.GeneralLinearGroup (Fin n) ℚ) * P
      map_one' := by simp
      map_mul' := by intro x y; simp [mul_assoc] }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact mul_left_cancel (mul_right_cancel hxy)
  let S := f.range
  have hS : ∀ g : S,
      ((g : Matrix.GeneralLinearGroup (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ).IsUpperTriangular ∧
      ∀ i, ((g : Matrix.GeneralLinearGroup (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) i i = 1 := by
    rintro ⟨g, x, rfl⟩
    have hx := hP x.1 x.2
    exact ⟨fun i j hij => hx.2 i j hij, hx.1⟩
  let e : K ≃* S := MonoidHom.ofInjective hf
  let : Group.IsNilpotent S := Unipotent.isNilpotent S hS
  refine ⟨Group.nilpotent_of_mulEquiv e.symm, ?_, ?_⟩
  · exact (Group.nilpotencyClass_le_of_surjective e.symm.toMonoidHom e.symm.surjective).trans
      (Unipotent.nilpotencyClass_le S hS)
  · intro g hg
    apply e.injective
    rw [map_one]
    exact eq_one_of_isOfFinOrder_of_unipotent S
      (Unipotent.isNilpotent_sub_one S hS) (e g) (e.toMonoidHom.isOfFinOrder hg)

end Kourovka.P21_40

import Kourovka.Problems.P21_99.Proof.Action
import Kourovka.Problems.P21_99.Proof.DataModel
import Kourovka.Problems.P21_99.Proof.DataCovarianceChecks
import Kourovka.Problems.P21_99.Proof.DataFixedChecks

/-! The concrete affine action and its unique-fixed-point transporter. -/

namespace Kourovka.P21_99

abbrev Point := Fin 6 × Data.Vec 14
abbrev ActingGroup := AffineGroup Data.K (Data.Vec 18)

noncomputable def quotientFibres :
    FiberSystem Data.K (Data.Vec 18) (Fin 6) (Data.Vec 14) where
  project i := (Data.linear (Data.projectionRows i)).toAddMonoidHom
  project_surjective i x := by
    refine ⟨Data.linear (Data.sectionRows i) x, ?_⟩
    exact congrArg (fun f : Data.Vec 14 →ₗ[Data.Scalar] Data.Vec 14 => f x)
      (Data.comp_id_of_entries _ _ (Data.section_checked i))
  linear k i := (Data.quotientLinear (Data.index k) i).toAddMonoidHom
  equivariant k i v := by
    change Data.linear (Data.projectionRows (k • i)) (k • v) =
      Data.quotientLinear (Data.index k) i (Data.linear (Data.projectionRows i) v)
    rw [Data.smul_block, Data.smul_vector]
    have h :
        (Data.linear (Data.projectionRows (Data.blockMap (Data.index k) i))).comp
            (Data.linear (Data.matrixRows (Data.index k))) =
          (Data.quotientLinear (Data.index k) i).comp
            (Data.linear (Data.projectionRows i)) := by
      apply Data.ext_entries
      exact Data.covarianceChecks (Data.index k) i
    exact congrArg (fun f : Data.Vec 18 →ₗ[Data.Scalar] Data.Vec 14 => f v) h

noncomputable instance affineAction : MulAction ActingGroup Point :=
  quotientFibres.affineMulAction

instance affinePretransitive : MulAction.IsPretransitive ActingGroup Point :=
  quotientFibres.pretransitive

def source : Point := (0, 0)
def target : Point := (2, Data.linear (Data.projectionRows 2) Data.translation)

theorem source_ne_target : source ≠ target := by
  intro h
  have hblock : (0 : Fin 6) = 2 := congrArg Prod.fst h
  exact (by decide : (0 : Fin 6) ≠ 2) hblock

private theorem identityEntry_basis {n : ℕ} (i j : Fin n) :
    Data.identityEntry i j = Data.basisVector j i := by
  by_cases hi : i = j
  · subst i
    simp [Data.identityEntry, Data.basisVector]
  · simp [Data.identityEntry, Data.basisVector, hi]

/-- Every element in this particular point transporter fixes exactly one point. -/
theorem transporter_unique (g : ActingGroup) (hg : g • source = target) :
    ∃! p : Point, g • p = p := by
  have htransport := (quotientFibres.act_source_iff g 0 2
    (Data.linear (Data.projectionRows 2) Data.translation)).mp hg
  have hblock : Data.blockMap (Data.index g.right) 0 = 2 := by
    rw [← Data.smul_block]
    exact htransport.1
  let t : Fin 64 := Data.targetSlot (Data.index g.right)
  have hindex : Data.targetIndex t = Data.index g.right :=
    Data.target_coverage_checked _ hblock
  obtain ⟨_, _, hfixed, hleft, hright, hpsi, htransfer, hnonzero⟩ :=
    Data.fixedChecks t
  have hregular : g.right • Data.regularBlock t = Data.regularBlock t := by
    rw [Data.smul_block, ← hindex]
    exact (hfixed _).mpr (Or.inl rfl)
  have hfixed' : ∀ i, g.right • i = i →
      i = Data.regularBlock t ∨ i = Data.singularBlock t := by
    intro i hi
    apply (hfixed i).mp
    rw [Data.smul_block, ← hindex] at hi
    exact hi
  change ∃! p : Point, quotientFibres.act g p = p
  apply quotientFibres.unique_fixed_of_two_fibres g
    (Data.regularBlock t) (Data.singularBlock t) hregular hfixed'
  · change ∃! x : Data.Vec 14,
      Data.linear (Data.projectionRows (Data.regularBlock t)) g.left.toAdd +
        Data.quotientLinear (Data.index g.right) (Data.regularBlock t) x = x
    rw [← hindex]
    let T := Data.quotientLinear (Data.targetIndex t) (Data.regularBlock t)
    let R := Data.linear (Data.regularInverseRows t)
    have hleft' : R.comp (LinearMap.id - T) = LinearMap.id := by
      apply Data.ext_entries
      intro i j
      exact (hleft i j).trans (identityEntry_basis i j)
    have hright' : (LinearMap.id - T).comp R = LinearMap.id := by
      apply Data.ext_entries
      intro i j
      exact (hright i j).trans (identityEntry_basis i j)
    apply unique_affine_fixed_of_inverse T.toAddMonoidHom R.toAddMonoidHom
    · intro x
      exact congrArg (fun f : Data.Vec 14 →ₗ[Data.Scalar] Data.Vec 14 => f x) hleft'
    · intro x
      exact congrArg (fun f : Data.Vec 14 →ₗ[Data.Scalar] Data.Vec 14 => f x) hright'
  · change ∀ x : Data.Vec 14,
      Data.linear (Data.projectionRows (Data.singularBlock t)) g.left.toAdd +
        Data.quotientLinear (Data.index g.right) (Data.singularBlock t) x ≠ x
    rw [← hindex]
    let T := Data.quotientLinear (Data.targetIndex t) (Data.singularBlock t)
    let P := Data.linear (Data.projectionRows (Data.singularBlock t))
    let Q := Data.linear (Data.projectionRows 2)
    let psi := Data.rowLinear (Data.singularFunctional t)
    let phi := Data.rowLinear (Data.targetFunctional t)
    have hpsi' : psi.comp T = psi := Data.ext_basis _ _ hpsi
    have htransfer' : psi.comp P = phi.comp Q := Data.ext_basis _ _ htransfer
    apply no_affine_fixed_of_covector_transport T.toAddMonoidHom
      P.toAddMonoidHom Q.toAddMonoidHom psi.toAddMonoidHom phi.toAddMonoidHom
      g.left.toAdd Data.translation
    · intro x
      exact congrArg (fun f : Data.Vec 14 →ₗ[Data.Scalar] Data.Scalar => f x) hpsi'
    · intro v
      exact congrArg (fun f : Data.Vec 18 →ₗ[Data.Scalar] Data.Scalar => f v) htransfer'
    · exact hnonzero
    · exact htransport.2

end Kourovka.P21_99

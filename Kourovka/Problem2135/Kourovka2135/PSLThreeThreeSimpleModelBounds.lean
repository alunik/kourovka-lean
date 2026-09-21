import Kourovka2135.PSLThreeThreeSimpleModels
import Kourovka2135.PSL33ModuleTwelveCohomology
import Kourovka2135.PSL33ModuleTwentySixCohomology
import Kourovka2135.PSL33ModuleSixteenCohomology
import Kourovka2135.PSLThreeThreePerfect
import Kourovka2135.PSLThreeThreeMovingRank
import Kourovka2135.PSLThreeThreeClosedModuleBound

/-! The explicit models discharge the actual closed-field cohomology bound.
Completeness, cohomology transport and moving-rank transport are all applied
to the same representations, without a separate modular classification input. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeSimpleModelBounds
open PSL33GoodSets PSLThreeThreeSimpleModels RepresentationCohomologyAlternative

variable (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]

theorem model_alternative (i : Index) (g : Q) (hg : orderOf g = 13) :
    Alternative (representation L i) g := by
  cases i with
  | trivial =>
      exact Or.inl PerfectTrivialCohomology.finrank_H1_eq_zero
  | twelve =>
      right
      constructor
      · exact (RepresentationEmbeddingModel.finrank_cohomology (primeEmbedding L)
          PSL33ModuleTwelve.representation 0).trans_le
            PSL33ModuleTwelveCohomology.finrank_H1_le_one
      · have he := (RepresentationEmbeddingModel.finrank_moving (primeEmbedding L)
          PSL33ModuleTwelve.representation g).trans
            (PSLThreeThreeMovingRank.finrank_moving_eq_of_order_thirteen
              PSL33ModuleTwelve.representation g PSL33ModuleTwelveCohomology.singer hg
              PSL33ModuleTwelveCohomology.singer_order)
        exact (by decide : 4 ≤ 12).trans
          (PSL33ModuleTwelveCohomology.moving_rank.trans_eq he.symm)
  | twentySix =>
      right
      constructor
      · exact (RepresentationEmbeddingModel.finrank_cohomology (primeEmbedding L)
          PSL33ModuleTwentySix.representation 0).trans_le
            PSL33ModuleTwentySixCohomology.finrank_H1_le_one
      · have he := (RepresentationEmbeddingModel.finrank_moving (primeEmbedding L)
          PSL33ModuleTwentySix.representation g).trans
            (PSLThreeThreeMovingRank.finrank_moving_eq_of_order_thirteen
              PSL33ModuleTwentySix.representation g PSL33ModuleTwentySixCohomology.singer hg
              PSL33ModuleTwentySixCohomology.singer_order)
        exact (by decide : 4 ≤ 24).trans
          (PSL33ModuleTwentySixCohomology.moving_rank.trans_eq he.symm)
  | sixteen i =>
      left
      exact (RepresentationEmbeddingModel.finrank_cohomology
        (BinaryFieldSixteenEmbedding.embedding L i) PSL33ModuleSixteen.representation 0).trans
          PSL33ModuleSixteenCohomology.finrank_H1_eq_zero

/-- The seven proved models cover every actual finite-dimensional simple
module and satisfy the two alternatives needed by the correction argument. -/
theorem closed_module_bound : PSLThreeThreeClosedModuleBound.ClosedModuleBound := by
  intro L _ _ _ V _ _ _ ρ _ g hg
  obtain ⟨i, ⟨e⟩⟩ := PSLThreeThreeSimpleModels.exists_equiv L ρ
  exact (alternative_iff (representation L i) ρ e g).mp (model_alternative L i g hg)

/-- The prime-field family input is now a conclusion, with no extra
representation-theoretic or cohomological assumption. -/
theorem binary_module_bound : PSLThreeThreeFrattiniLifting.BinaryModuleBound :=
  PSLThreeThreeClosedModuleBound.binaryModuleBound_of_closed closed_module_bound

end Kourovka2135.PSLThreeThreeSimpleModelBounds

import Kourovka2135.PSL33ModuleTwelveDensity
import Kourovka2135.PSL33ModuleTwentySixDensity
import Kourovka2135.PSL33ModuleSixteenDensity
import Kourovka2135.PSL33ModuleSixteenCharacter
import Kourovka2135.PerfectTrivialCohomology
import Kourovka2135.ModularSimpleListComplete
import Kourovka2135.PSLThreeThreeOddConjugacy

/-! The seven actual simple models over an algebraically closed field of
characteristic two. Their construction, simplicity and distinctness are
separate from completeness, which follows from the proved odd-class bound. -/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.PSLThreeThreeSimpleModels
open PSL33GoodSets
open RepresentationEmbeddingModel

inductive Index where
  | trivial
  | twelve
  | twentySix
  | sixteen (i : Fin 4)
  deriving DecidableEq, Fintype

theorem card_index : Fintype.card Index = 7 := by decide

def dimension : Index → ℕ
  | .trivial => 1
  | .twelve => 12
  | .twentySix => 26
  | .sixteen _ => 16

variable (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]

local instance primeAlgebra : Algebra (ZMod 2) L := ZMod.algebra L 2

abbrev primeEmbedding : ZMod 2 →+* L := algebraMap (ZMod 2) L

abbrev Space : Index → Type
  | .trivial => L
  | .twelve => Carrier (V := PSL33ModuleTwelve.V) (primeEmbedding L)
  | .twentySix => Carrier (V := PSL33ModuleTwentySix.V) (primeEmbedding L)
  | .sixteen i => Carrier (V := PSL33ModuleSixteen.V)
      (BinaryFieldSixteenEmbedding.embedding L i)

instance spaceAddCommGroup (i : Index) : AddCommGroup (Space L i) := by
  cases i with
  | trivial => exact inferInstanceAs (AddCommGroup L)
  | twelve => exact inferInstanceAs (AddCommGroup
      (Carrier (V := PSL33ModuleTwelve.V) (primeEmbedding L)))
  | twentySix => exact inferInstanceAs (AddCommGroup
      (Carrier (V := PSL33ModuleTwentySix.V) (primeEmbedding L)))
  | sixteen i => exact inferInstanceAs (AddCommGroup
      (Carrier (V := PSL33ModuleSixteen.V) (BinaryFieldSixteenEmbedding.embedding L i)))

instance spaceModule (i : Index) : Module L (Space L i) := by
  cases i with
  | trivial => exact inferInstanceAs (Module L L)
  | twelve => exact inferInstanceAs (Module L
      (Carrier (V := PSL33ModuleTwelve.V) (primeEmbedding L)))
  | twentySix => exact inferInstanceAs (Module L
      (Carrier (V := PSL33ModuleTwentySix.V) (primeEmbedding L)))
  | sixteen i => exact inferInstanceAs (Module L
      (Carrier (V := PSL33ModuleSixteen.V) (BinaryFieldSixteenEmbedding.embedding L i)))

instance spaceFiniteDimensional (i : Index) : FiniteDimensional L (Space L i) := by
  cases i with
  | trivial => exact inferInstanceAs (FiniteDimensional L L)
  | twelve => exact inferInstanceAs (FiniteDimensional L
      (Carrier (V := PSL33ModuleTwelve.V) (primeEmbedding L)))
  | twentySix => exact inferInstanceAs (FiniteDimensional L
      (Carrier (V := PSL33ModuleTwentySix.V) (primeEmbedding L)))
  | sixteen i => exact inferInstanceAs (FiniteDimensional L
      (Carrier (V := PSL33ModuleSixteen.V) (BinaryFieldSixteenEmbedding.embedding L i)))

def representation : (i : Index) → Representation L Q (Space L i)
  | .trivial => Representation.trivial L Q L
  | .twelve => model (primeEmbedding L) PSL33ModuleTwelve.representation
  | .twentySix => model (primeEmbedding L) PSL33ModuleTwentySix.representation
  | .sixteen i => model (BinaryFieldSixteenEmbedding.embedding L i)
      PSL33ModuleSixteen.representation

instance representation_isIrreducible (i : Index) : (representation L i).IsIrreducible := by
  cases i with
  | trivial => exact PerfectTrivialCohomology.trivial_isIrreducible
  | twelve =>
      exact RepresentationEmbeddingModel.isIrreducible (primeEmbedding L)
        PSL33ModuleTwelve.representation PSL33ModuleTwelveDensity.asAlgebraHom_surjective
  | twentySix =>
      exact RepresentationEmbeddingModel.isIrreducible (primeEmbedding L)
        PSL33ModuleTwentySix.representation PSL33ModuleTwentySixDensity.asAlgebraHom_surjective
  | sixteen i =>
      exact RepresentationEmbeddingModel.isIrreducible
        (BinaryFieldSixteenEmbedding.embedding L i) PSL33ModuleSixteen.representation
        PSL33ModuleSixteenDensity.asAlgebraHom_surjective

theorem finrank_space (i : Index) : Module.finrank L (Space L i) = dimension i := by
  cases i with
  | trivial => exact Module.finrank_self L
  | twelve =>
      exact (finrank_carrier (V := PSL33ModuleTwelve.V) (primeEmbedding L)).trans
        PSL33ModuleTwelve.finrank_eq_twelve
  | twentySix =>
      exact (finrank_carrier (V := PSL33ModuleTwentySix.V) (primeEmbedding L)).trans
        PSL33ModuleTwentySix.finrank_eq_twentySix
  | sixteen i =>
      exact (finrank_carrier (V := PSL33ModuleSixteen.V)
        (BinaryFieldSixteenEmbedding.embedding L i)).trans PSL33ModuleSixteen.finrank_eq_sixteen

/-- Natural-number dimensions separate the three small types; an actual
ordinary character value separates the four sixteen-dimensional types. -/
theorem pairwise_not_equiv : Pairwise fun i j =>
    ¬ Nonempty ((representation L i).Equiv (representation L j)) := by
  intro i j hij he
  have hd : dimension i = dimension j := by
    obtain ⟨e⟩ := he
    exact (finrank_space L i).symm.trans (e.toLinearEquiv.finrank_eq.trans (finrank_space L j))
  cases i <;> cases j <;> simp only [dimension] at hd
  all_goals try omega
  all_goals try exact hij rfl
  rename_i i j
  exact PSL33ModuleSixteenCharacter.models_pairwise_not_equiv L
    (fun h => hij (congrArg Index.sixteen h)) he

/-- No further simple types can exist, since these seven attain the
independently checked odd-conjugacy upper bound. -/
theorem exists_equiv {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L Q V) [ρ.IsIrreducible] :
    ∃ i : Index, Nonempty ((representation L i).Equiv ρ) := by
  apply ModularSimpleListComplete.exists_equiv_of_card_eq
    (representation L) ρ (pairwise_not_equiv L) _
    PSLThreeThreeOddConjugacy.representatives
    PSLThreeThreeOddConjugacy.projective_odd_conjugacy_cover
  · rw [card_index, Fintype.card_fin]
  · rw [PSLThreeThreeSemidihedralData.projective_card]
    decide

end Kourovka2135.PSLThreeThreeSimpleModels

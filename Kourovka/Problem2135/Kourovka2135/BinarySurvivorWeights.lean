import Kourovka2135.BinarySurvivorDegree
import Kourovka2135.BinaryWeights

/-! The previously proved binary weight arithmetic applied to the actual
surviving exponent coordinates. Degree one has at most one zero-weight
coordinate, present only for a singleton coefficient support. The natural
coefficient has at most one in degree two and none for extension degree two. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinarySurvivorWeights
open PeriodicResolution BinaryCochainGraded BinarySurvivorDegree BinaryWeights
variable {f : ℕ}

def generatorWeight : (Fin f →₀ ℕ) →+ ℕ := Finsupp.weight (fun i : Fin f => 2 ^ (i.val + 1))

@[simp] theorem generatorWeight_single (i : Fin f) :
    generatorWeight (Finsupp.single i 1) = 2 ^ (i.val + 1) := by
  simp [generatorWeight, Finsupp.weight_single]

/-- Actual surviving monomials whose torus character is trivial. -/
abbrev ZeroWeightIndex (I : Finset (Fin f)) (n : ℕ) :=
  {a : SurvivorIndex I n // Nat.ModEq (2 ^ f - 1)
    (∑ i ∈ I, 2 ^ i.val) (generatorWeight a.val.val)}

theorem degree_one_parameters (I : Finset (Fin f)) (a : ZeroWeightIndex I 1) :
    degreeOneEquiv a.val.val ∉ I ∧
      Nat.ModEq (2 ^ f - 1) (∑ i ∈ I, 2 ^ i.val)
        (2 ^ ((degreeOneEquiv a.val.val).val + 1)) := by
  refine ⟨(survivorOneEquiv I a.val).property, ?_⟩
  have h := a.property
  rw [← degreeOneEquiv_single a.val.val, generatorWeight_single] at h
  exact h

/-- Nonsingleton coefficient support has no degree-one zero-weight coordinate. -/
theorem isEmpty_degree_one (hf : 2 ≤ f) (I : Finset (Fin f)) (hI : I.card ≠ 1) :
    IsEmpty (ZeroWeightIndex I 1) := by
  refine ⟨fun a => ?_⟩
  have he := (fin_subsetWeight_modEq_singleton_iff hf _ I).mp (degree_one_parameters I a).2
  apply hI
  rw [he]
  simp

/-- In degree one the zero-weight coordinate space always has at most one index. -/
theorem subsingleton_degree_one (hf : 2 ≤ f) (I : Finset (Fin f)) :
    Subsingleton (ZeroWeightIndex I 1) := by
  by_cases hI : I.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
    obtain ⟨j, _, hu⟩ := natural_h1_weight_unique hf i
    constructor
    intro a b
    have ha : degreeOneEquiv a.val.val ≠ i ∧
        Nat.ModEq (2 ^ f - 1) (2 ^ i.val)
          (2 ^ ((degreeOneEquiv a.val.val).val + 1)) := by
      simpa using degree_one_parameters {i} a
    have hb : degreeOneEquiv b.val.val ≠ i ∧
        Nat.ModEq (2 ^ f - 1) (2 ^ i.val)
          (2 ^ ((degreeOneEquiv b.val.val).val + 1)) := by
      simpa using degree_one_parameters {i} b
    apply Subtype.ext
    apply Subtype.ext
    exact degreeOneEquiv.injective ((hu _ ha).trans (hu _ hb).symm)
  · let := isEmpty_degree_one hf I hI
    infer_instance

/-- For the natural coefficient every degree-two zero-weight monomial is
represented by a pair satisfying the actual binary torus-weight equation. -/
theorem degree_two_parameters (i : Fin f) (a : ZeroWeightIndex {i} 2) :
    ∃ j k : Fin f, j ≠ i ∧ k ≠ i ∧
      Nat.ModEq (2 ^ f - 1) (2 ^ i.val)
        (2 ^ (j.val + 1) + 2 ^ (k.val + 1)) ∧
      a.val.val.val = Finsupp.single j 1 + Finsupp.single k 1 := by
  obtain ⟨j, k, hj, hk, he⟩ := survivor_two_exists {i} a.val
  refine ⟨j, k, by simpa using hj, by simpa using hk, ?_, he⟩
  have ha := a.property
  rw [he, map_add, generatorWeight_single, generatorWeight_single] at ha
  simpa using ha

/-- The natural coefficient has no degree-two zero-weight class at f=2. -/
theorem isEmpty_degree_two_at_two (i : Fin 2) : IsEmpty (ZeroWeightIndex {i} 2) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨j, k, hj, hk, h, _⟩ := degree_two_parameters i a
  exact natural_h2_no_weight_at_two i j k hj hk h

/-- In larger extension degrees there is at most one natural degree-two
zero-weight exponent vector, including the repeated-index possibility. -/
theorem subsingleton_degree_two (hf : 3 ≤ f) (i : Fin f) :
    Subsingleton (ZeroWeightIndex {i} 2) := by
  obtain ⟨jk, _, hu⟩ := natural_h2_weight_unique hf i
  constructor
  intro a b
  obtain ⟨j, k, hj, hk, ha, hea⟩ := degree_two_parameters i a
  obtain ⟨j', k', hj', hk', hb, heb⟩ := degree_two_parameters i b
  have he : (j, k) = (j', k') :=
    (hu (j, k) ⟨hj, hk, ha⟩).trans (hu (j', k') ⟨hj', hk', hb⟩).symm
  have hjj : j = j' := congrArg Prod.fst he
  have hkk : k = k' := congrArg Prod.snd he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [hea, heb, hjj, hkk]

end Kourovka2135.BinarySurvivorWeights

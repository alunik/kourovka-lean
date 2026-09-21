import Kourovka2135.BinaryCochainGraded
import Mathlib.Data.Finsupp.Weight

/-! Concrete low-degree monomials for the surviving cochain coordinates.
Degree one is a single omitted index; degree two is a pair of omitted
indices, allowing repetition. These are statements about the actual
finitely supported exponent vectors used in the cohomology calculation. -/
set_option autoImplicit false
noncomputable section
namespace Kourovka2135.BinarySurvivorDegree
open PeriodicResolution BinaryCochainGraded
variable {ι : Type*}

/-- Every degree-one exponent is exactly one single index. -/
theorem degree_one_exists (a : DegreeIndex ι 1) :
    ∃ i : ι, Finsupp.single i 1 = a.val := by
  have ha : a.val ∈ {d : ι →₀ ℕ | d.degree = 1} := a.property
  rw [← Finsupp.range_single_one] at ha
  exact ha

/-- The actual degree-one exponent type is the original index type. -/
def degreeOneEquiv : DegreeIndex ι 1 ≃ ι :=
  (Equiv.ofBijective (fun i : ι => (⟨Finsupp.single i 1, by simp⟩ : DegreeIndex ι 1))
    ⟨by
      intro i j h
      have he := congrArg Subtype.val h
      exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) he,
    fun a => by obtain ⟨i, hi⟩ := degree_one_exists a; exact ⟨i, Subtype.ext hi⟩⟩).symm

@[simp] theorem degreeOneEquiv_symm_val (i : ι) :
    (degreeOneEquiv.symm i).val = Finsupp.single i 1 := rfl

theorem degreeOneEquiv_single (a : DegreeIndex ι 1) :
    Finsupp.single (degreeOneEquiv a) 1 = a.val :=
  congrArg Subtype.val (degreeOneEquiv.symm_apply_apply a)

/-- Every degree-two exponent is a pair of single indices, possibly equal. -/
theorem degree_two_exists (a : DegreeIndex ι 2) :
    ∃ i j : ι, a.val = Finsupp.single i 1 + Finsupp.single j 1 := by
  have ha : a.val ≠ 0 := by
    intro h
    have hd := a.property
    rw [h] at hd
    simp at hd
  have hex : ∃ i, a.val i ≠ 0 := by
    by_contra! h
    exact ha (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hex
  have hd : (a.val - Finsupp.single i 1).degree = 1 := by
    have hs := degree_sub_single_one_add a.val i hi
    rw [a.property] at hs
    omega
  obtain ⟨j, hj⟩ := degree_one_exists (⟨a.val - Finsupp.single i 1, hd⟩ : DegreeIndex ι 1)
  refine ⟨i, j, ?_⟩
  change Finsupp.single j 1 = a.val - Finsupp.single i 1 at hj
  rw [hj, add_comm, Finsupp.sub_add_single_one_cancel hi]

variable {f : ℕ} (I : Finset (Fin f))

/-- Surviving degree-one monomials are exactly the omitted indices. -/
def survivorOneEquiv : SurvivorIndex I 1 ≃ {i : Fin f // i ∉ I} where
  toFun a := ⟨degreeOneEquiv a.val, by
    intro hi
    have hz := a.property (degreeOneEquiv a.val) hi
    rw [← degreeOneEquiv_single a.val] at hz
    simp at hz⟩
  invFun i := ⟨degreeOneEquiv.symm i.val, by
    intro j hj
    have hji : j ≠ i.val := by intro h; exact i.property (h ▸ hj)
    simp [hji]⟩
  left_inv a := Subtype.ext (degreeOneEquiv.symm_apply_apply a.val)
  right_inv i := Subtype.ext (degreeOneEquiv.apply_symm_apply i.val)

/-- A degree-two survivor is a pair of omitted indices, retaining repeated indices. -/
theorem survivor_two_exists (a : SurvivorIndex I 2) :
    ∃ i j : Fin f, i ∉ I ∧ j ∉ I ∧
      a.val.val = Finsupp.single i 1 + Finsupp.single j 1 := by
  obtain ⟨i, j, he⟩ := degree_two_exists a.val
  refine ⟨i, j, ?_, ?_, he⟩
  · intro hi
    have hz := a.property i hi
    rw [he] at hz
    simp at hz
  · intro hj
    have hz := a.property j hj
    rw [he] at hz
    simp at hz

end Kourovka2135.BinarySurvivorDegree

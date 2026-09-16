import Kourovka.Problems.P21_44.Proof.SectionWords
import Kourovka.Problems.P21_44.Proof.RecurrentSections.WordGeometry

/-! # The two-generated subgroup and its ordinary word balls

The geometry uses the symmetric generating set containing the identity and the
four signed directed generators. Word balls are actual finite subsets of the
concrete subgroup of the inverse limit.
-/

namespace Kourovka.P21_44

open scoped Pointwise

def generatedSubgroup : Subgroup AutTree := Subgroup.closure ({a,b} : Set AutTree)
abbrev Generated := generatedSubgroup
noncomputable instance : DecidableEq Generated := Classical.decEq _

def generatedA : Generated := ⟨a, Subgroup.subset_closure (by simp)⟩
def generatedB : Generated := ⟨b, Subgroup.subset_closure (by simp)⟩

@[simp] theorem generatedA_cube : generatedA ^ 3 = 1 := by
  apply Subtype.ext
  exact a_cube
@[simp] theorem generatedB_cube : generatedB ^ 3 = 1 := by
  apply Subtype.ext
  exact b_cube

@[simp] theorem coe_evalLetter (l : Letter) :
    (evalLetter generatedA generatedB l).val = evalLetter a b l := by
  rcases l with ⟨f,s⟩
  cases f <;> cases s <;> rfl

@[simp] theorem coe_evalWord (w : Word) :
    (evalWord generatedA generatedB w).val = evalWord a b w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    change (evalLetter generatedA generatedB l).val * (evalWord generatedA generatedB w).val = _
    rw [coe_evalLetter, ih, evalWord_cons]

noncomputable def signedGenerators : Finset Generated :=
  {1, generatedA, generatedA⁻¹, generatedB, generatedB⁻¹}

@[simp] theorem one_mem_signedGenerators : (1 : Generated) ∈ signedGenerators := by
  simp [signedGenerators]

theorem evalLetter_mem_signedGenerators (l : Letter) :
    evalLetter generatedA generatedB l ∈ signedGenerators := by
  rcases l with ⟨f,s⟩
  cases f <;> cases s <;> simp [signedGenerators, evalLetter]

theorem inv_mem_signedGenerators (g : Generated) (h : g ∈ signedGenerators) :
    g⁻¹ ∈ signedGenerators := by
  simp only [signedGenerators, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

theorem evalWord_mem_pow (w : Word) :
    evalWord generatedA generatedB w ∈ signedGenerators ^ w.length := by
  induction w with
  | nil => simp
  | cons l w ih =>
    rw [List.length_cons, pow_succ', evalWord_cons]
    exact Finset.mul_mem_mul (evalLetter_mem_signedGenerators l) ih

/-- Every element of the concrete subgroup is represented by a finite signed
word in the two directed generators. -/
theorem exists_generated_word (g : Generated) :
    ∃ w : Word, evalWord generatedA generatedB w = g := by
  obtain ⟨w,hw⟩ := exists_evalWord_of_mem_closure a b g.property
  exact ⟨w, Subtype.ext ((coe_evalWord w).trans hw)⟩

noncomputable def wordGeometry : RecurrentSections.WordGeometry Generated where
  generators := signedGenerators
  one_mem := one_mem_signedGenerators
  inv_mem := inv_mem_signedGenerators
  generates g := by
    obtain ⟨w,rfl⟩ := exists_generated_word g
    exact ⟨w.length, evalWord_mem_pow w⟩

theorem signedGenerator_word (g : Generated) (h : g ∈ signedGenerators) :
    ∃ w : Word, w.length ≤ 1 ∧ evalWord generatedA generatedB w = g := by
  simp only [signedGenerators, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨[], by simp⟩
  · exact ⟨[(false,true)], by simp [evalLetter]⟩
  · exact ⟨[(false,false)], by simp [evalLetter]⟩
  · exact ⟨[(true,true)], by simp [evalLetter]⟩
  · exact ⟨[(true,false)], by simp [evalLetter]⟩

theorem exists_word_of_mem_ball {g : Generated} {n : ℕ} (h : g ∈ wordGeometry.ball n) :
    ∃ w : Word, w.length ≤ n ∧ evalWord generatedA generatedB w = g := by
  change g ∈ signedGenerators ^ n at h
  induction n generalizing g with
  | zero =>
    have hg : g = 1 := by simpa using h
    subst g
    exact ⟨[], by simp⟩
  | succ n ih =>
    rw [pow_succ'] at h
    obtain ⟨g,hg,k,hk,rfl⟩ := Finset.mem_mul.mp h
    obtain ⟨v,hvl,hve⟩ := signedGenerator_word g hg
    obtain ⟨w,hwl,hwe⟩ := ih hk
    exact ⟨v ++ w, by simp only [List.length_append]; omega, by simp [hve,hwe]⟩

/-- Every point of an ordinary word ball has an alternating representative of
at most the radius, with the same concrete tree action. -/
theorem exists_alternating_word_of_mem_ball {g : Generated} {n : ℕ}
    (h : g ∈ wordGeometry.ball n) :
    ∃ w : Word, Alternating w ∧ w.length ≤ n ∧ evalWord a b w = g.val := by
  obtain ⟨w,hw,he⟩ := exists_word_of_mem_ball h
  refine ⟨normalize w, alternating_normalize w, (normalize_length_le w).trans hw, ?_⟩
  rw [evalWord_normalize a b a_cube b_cube]
  exact (coe_evalWord w).symm.trans (congrArg Subtype.val he)

/-- Evaluating a signed word gives an element of the corresponding ordinary
word ball. -/
theorem evalWord_mem_ball (w : Word) :
    evalWord generatedA generatedB w ∈ wordGeometry.ball w.length := evalWord_mem_pow w

theorem treeSection_mem_generated (g : Generated) (i : Alphabet) :
    treeSection g.val i ∈ generatedSubgroup := by
  obtain ⟨w,rfl⟩ := exists_generated_word g
  rw [coe_evalWord, treeSection_evalWord]
  exact (coe_evalWord (rawSections w i)) ▸ (evalWord generatedA generatedB (rawSections w i)).property

/-- The actual section, viewed in the generated subgroup. -/
def generatedSection (g : Generated) (i : Alphabet) : Generated :=
  ⟨treeSection g.val i, treeSection_mem_generated g i⟩

@[simp] theorem generatedSection_evalWord (w : Word) (i : Alphabet) :
    generatedSection (evalWord generatedA generatedB w) i =
      evalWord generatedA generatedB (rawSections w i) := by
  apply Subtype.ext
  change treeSection (evalWord generatedA generatedB w).val i = _
  rw [coe_evalWord]
  exact (treeSection_evalWord w i).trans (coe_evalWord (rawSections w i)).symm

/-- A root permutation and the five actual sections distinguish elements of the
generated subgroup. -/
theorem root_sections_injective : Function.Injective
    (fun g : Generated => (root g.val, generatedSection g)) := by
  intro g h heq
  apply Subtype.ext
  apply decompose_injective
  apply SemidirectProduct.ext
  · funext i
    exact congrArg (fun p : A5 × (Alphabet → Generated) => (p.2 i).val) heq
  · exact congrArg Prod.fst heq

end Kourovka.P21_44

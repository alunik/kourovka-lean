import Kourovka.Problem2153.RootSystem
import Kourovka.Problem2153.Weyl.Data
import Mathlib.Algebra.Group.Subgroup.Pointwise

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace Kourovka.Problem2153.RootSystem.Weyl

/-- Forget the invertibility and ambient-subgroup membership proofs. -/
def matrixHom : G →* WilsonModel.Mat :=
  (Units.coeHom WilsonModel.Mat).comp WilsonModel.ambient.subtype

theorem matrixHom_injective : Function.Injective matrixHom := by
  intro a b h
  exact Subtype.ext (Units.ext h)

def generator (b : Bool) : G := if b then s else r

def evalWord (l : List Bool) : G := (l.map generator).prod

@[simp] theorem evalWord_nil : evalWord [] = 1 := rfl

@[simp] theorem evalWord_cons (b : Bool) (l : List Bool) :
    evalWord (b :: l) = generator b * evalWord l := rfl

def rep (i : Fin 16) : G := evalWord (WeylData.words i)

def indexStep (b : Bool) (i : Fin 16) : Fin 16 :=
  if b then WeylData.leftS i else WeylData.leftR i

def wordIndex (l : List Bool) (i : Fin 16) : Fin 16 := l.foldr indexStep i

theorem generator_matrix_step (b : Bool) (i : Fin 16) :
    matrixHom (generator b) * WeylData.matrix i = WeylData.matrix (indexStep b i) := by
  cases b
  · exact WeylData.rho_left i
  · exact WeylData.sigma_left i

theorem evalWord_matrix_step (l : List Bool) (i : Fin 16) :
    matrixHom (evalWord l) * WeylData.matrix i = WeylData.matrix (wordIndex l i) := by
  induction l with
  | nil => simp [wordIndex]
  | cons b l ih =>
    rw [evalWord_cons, map_mul, mul_assoc, ih]
    exact generator_matrix_step b (wordIndex l i)

theorem words_index : ∀ i : Fin 16, wordIndex (WeylData.words i) 0 = i := by
  decide +kernel

/-- The word representatives agree with the separately checked sparse matrices. -/
theorem rep_matrix (i : Fin 16) : matrixHom (rep i) = WeylData.matrix i := by
  have h := evalWord_matrix_step (WeylData.words i) 0
  simpa only [WeylData.matrix_zero, mul_one, words_index, rep] using h

theorem r_mul_rep (i : Fin 16) : r * rep i = rep (WeylData.leftR i) := by
  apply matrixHom_injective
  rw [map_mul, rep_matrix, rep_matrix]
  exact WeylData.rho_left i

theorem s_mul_rep (i : Fin 16) : s * rep i = rep (WeylData.leftS i) := by
  apply matrixHom_injective
  rw [map_mul, rep_matrix, rep_matrix]
  exact WeylData.sigma_left i

@[simp] theorem rep_zero : rep 0 = 1 := rfl
@[simp] theorem rep_one : rep 1 = r := by simp [rep, WeylData.words, evalWord, generator]
@[simp] theorem rep_two : rep 2 = s := by simp [rep, WeylData.words, evalWord, generator]

theorem generator_mem_W (b : Bool) : generator b ∈ W := by
  cases b
  · exact r_mem_W
  · exact s_mem_W

theorem evalWord_mem_W (l : List Bool) : evalWord l ∈ W := by
  induction l with
  | nil => exact W.one_mem
  | cons b l ih => exact W.mul_mem (generator_mem_W b) ih

theorem rep_mem_W (i : Fin 16) : rep i ∈ W := evalWord_mem_W _

/-- Coverage uses only the 32 generator transitions and the two involution identities. -/
theorem exists_rep_of_mem_W {g : G} (hg : g ∈ W) : ∃ i, g = rep i := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, rep_zero.symm⟩
  | mul_left a ha b hb ih =>
    obtain ⟨i, rfl⟩ := ih
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨WeylData.leftR i, r_mul_rep i⟩
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact ⟨WeylData.leftS i, s_mul_rep i⟩
  | inv_mul_cancel a ha b hb ih =>
    obtain ⟨i, rfl⟩ := ih
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · have hir : r⁻¹ = r := inv_eq_of_mul_eq_one_right
        (Subtype.ext (Units.ext WilsonModel.rho_square))
      exact ⟨WeylData.leftR i, by rw [hir, r_mul_rep]⟩
    · obtain rfl := Set.mem_singleton_iff.mp ha
      have his : s⁻¹ = s := inv_eq_of_mul_eq_one_right
        (Subtype.ext (Units.ext WilsonModel.sigma_square))
      exact ⟨WeylData.leftS i, by rw [his, s_mul_rep]⟩

theorem W_eq_range : (W : Set G) = Set.range rep := by
  ext g
  constructor
  · intro hg
    obtain ⟨i, rfl⟩ := exists_rep_of_mem_W hg
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact rep_mem_W i

theorem rep_injective : Function.Injective rep := by
  intro i j hij
  by_contra hne
  have hm := congrArg matrixHom hij
  rw [rep_matrix, rep_matrix] at hm
  exact WeylData.distinguish_ne i j hne
    (congrFun (congrFun hm (WeylData.distinguish i j).1) (WeylData.distinguish i j).2)

/-- The finite table enumerates the actual generated Weyl subgroup without repetitions. -/
noncomputable def representativesEquiv : Fin 16 ≃ W :=
  Equiv.ofBijective (fun i => ⟨rep i, rep_mem_W i⟩)
    ⟨fun _ _ h => rep_injective (congrArg Subtype.val h), by
      intro g
      obtain ⟨i, hi⟩ := exists_rep_of_mem_W g.property
      exact ⟨i, Subtype.ext hi.symm⟩⟩

theorem card_W : Nat.card W = 16 := by
  rw [← Nat.card_congr representativesEquiv]
  exact Nat.card_fin 16

/-- Among the Weyl representatives only the identity is lower triangular. -/
theorem index_zero_of_lowerTriangular (i : Fin 16)
    (h : ∀ a b : Fin 26, a < b → matrixHom (rep i) a b = 0) : i = 0 := by
  by_contra hi
  obtain ⟨hlt, hnz⟩ := WeylData.above_nonzero i hi
  exact hnz (by simpa only [rep_matrix] using h _ _ hlt)

theorem eq_one_of_mem_W_lowerTriangular {g : G} (hg : g ∈ W)
    (h : ∀ a b : Fin 26, a < b → matrixHom g a b = 0) : g = 1 := by
  obtain ⟨i, rfl⟩ := exists_rep_of_mem_W hg
  rw [index_zero_of_lowerTriangular i h, rep_zero]

theorem generator_mul_rep (b : Bool) (i : Fin 16) :
    generator b * rep i = rep (indexStep b i) := by
  cases b
  · exact r_mul_rep i
  · exact s_mul_rep i

theorem evalWord_mul_rep (l : List Bool) (i : Fin 16) :
    evalWord l * rep i = rep (wordIndex l i) := by
  induction l with
  | nil => simp [wordIndex]
  | cons b l ih =>
    rw [evalWord_cons, mul_assoc, ih]
    exact generator_mul_rep b (wordIndex l i)

def mulIndex (i j : Fin 16) : Fin 16 := wordIndex (WeylData.words i) j

theorem rep_mul (i j : Fin 16) : rep i * rep j = rep (mulIndex i j) :=
  evalWord_mul_rep (WeylData.words i) j

/-- The longest Weyl word. -/
def w0 : G := rep 15

theorem w0_mem_W : w0 ∈ W := rep_mem_W 15

theorem w0_eq : w0 = (r * s) ^ 4 := by
  simp [w0, rep, WeylData.words, evalWord, generator, pow_succ, mul_assoc]

def pairGenerator (i : Fin 16) (b : Bool) : G := if b then rep i else r
def evalPair (i : Fin 16) (l : List Bool) : G := (l.map (pairGenerator i)).prod
def pairIndex (i : Fin 16) (l : List Bool) : Fin 16 :=
  l.foldr (fun b j => mulIndex (if b then i else 1) j) 0

theorem evalPair_eq (i : Fin 16) (l : List Bool) : evalPair i l = rep (pairIndex i l) := by
  induction l with
  | nil => exact rep_zero.symm
  | cons b l ih =>
    change pairGenerator i b * evalPair i l = _
    rw [ih]
    cases b
    · change r * rep (pairIndex i l) = rep (mulIndex 1 (pairIndex i l))
      rw [← rep_one]
      exact rep_mul 1 _
    · exact rep_mul i _

theorem extraction_index : ∀ i : Fin 16, i ≠ 0 → i ≠ 1 →
    pairIndex i (WeylData.extractionWord i) = 15 := by decide +kernel

theorem pairGenerator_mem (i : Fin 16) (b : Bool) :
    pairGenerator i b ∈ Subgroup.closure ({r, rep i} : Set G) := by
  apply Subgroup.subset_closure
  cases b <;> simp [pairGenerator]

theorem evalPair_mem (i : Fin 16) (l : List Bool) :
    evalPair i l ∈ Subgroup.closure ({r, rep i} : Set G) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons b l ih => exact Subgroup.mul_mem _ (pairGenerator_mem i b) ih

/-- Each of the 14 representatives outside `{1,r}` generates the longest word together with `r`. -/
theorem w0_mem_closure (i : Fin 16) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    w0 ∈ Subgroup.closure ({r, rep i} : Set G) := by
  have h := evalPair_mem i (WeylData.extractionWord i)
  rwa [evalPair_eq, extraction_index i hi0 hi1] at h

theorem w0_mem_closure_of_not_mem (Q : Subgroup G) (hr : r ∈ Q)
    (i : Fin 16) (hi : rep i ∉ Q) :
    w0 ∈ Subgroup.closure ({r, rep i} : Set G) := by
  apply w0_mem_closure i
  · intro hi0
    apply hi
    simpa only [hi0, rep_zero] using Q.one_mem
  · intro hi1
    apply hi
    simpa only [hi1, rep_one] using hr

end Kourovka.Problem2153.RootSystem.Weyl

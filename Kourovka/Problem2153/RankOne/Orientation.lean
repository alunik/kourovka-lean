import Kourovka.Problem2153.RankOne.SimpleWeyl
import Kourovka.Problem2153.Weyl

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000

namespace Kourovka.Problem2153.RootSystem.RankOne

def rootStep (b : Bool) (i : Fin 12) : Option (Fin 12) :=
  if b then
    if i = 0 then none else some (sIndex i)
  else
    if i = 1 ∨ i = 3 then none else some (rIndex i)

def rootPath (i : Fin 12) : List Bool → Option (Fin 12)
  | [] => some i
  | b :: l => (rootStep b i).bind (fun j => rootPath j l)

theorem rootStep_sound (b : Bool) (i j : Fin 12) (a : Fin 8)
    (h : rootStep b i = some j) :
    rightConj (root i a) (Weyl.generator b) = root j a := by
  cases b
  · by_cases hi : i = 1 ∨ i = 3
    · simp [rootStep, hi] at h
    · have hj : rIndex i = j := by simpa [rootStep, hi] using h
      subst j
      exact root_conj_r i (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)) a
  · by_cases hi : i = 0
    · simp [rootStep, hi] at h
    · have hj : sIndex i = j := by simpa [rootStep, hi] using h
      subst j
      exact root_conj_s i hi a

theorem rootPath_sound (l : List Bool) (i j : Fin 12) (a : Fin 8)
    (h : rootPath i l = some j) :
    rightConj (root i a) (Weyl.evalWord l) = root j a := by
  induction l generalizing i with
  | nil =>
    have hij : i = j := by simpa [rootPath] using h
    subst i
    simp [rightConj]
  | cons b l ih =>
    cases hs : rootStep b i with
    | none => simp [rootPath, hs] at h
    | some k =>
      have hp : rootPath k l = some j := by simpa [rootPath, hs] using h
      rw [Weyl.evalWord_cons, rightConj_mul, rootStep_sound b i k a hs]
      exact ih k hp

theorem evalWord_append (l m : List Bool) :
    Weyl.evalWord (l ++ m) = Weyl.evalWord l * Weyl.evalWord m := by
  simp [Weyl.evalWord, List.map_append, List.prod_append]

theorem generator_inv (b : Bool) : (Weyl.generator b)⁻¹ = Weyl.generator b := by
  cases b
  · exact r_inv
  · exact s_inv

theorem evalWord_reverse (l : List Bool) :
    Weyl.evalWord l.reverse = (Weyl.evalWord l)⁻¹ := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.reverse_cons, evalWord_append, Weyl.evalWord_cons, Weyl.evalWord_nil,
      mul_one, ih, Weyl.evalWord_cons, mul_inv_rev, generator_inv]

def flipR : Fin 16 → Bool :=
  ![false, true, false, false, true, true, false, false,
    true, true, false, false, true, true, false, true]

def flipS : Fin 16 → Bool :=
  ![false, false, true, true, false, false, true, true,
    false, false, true, true, false, false, true, true]

def selectedIndexR (i : Fin 16) : Fin 16 := if flipR i then Weyl.mulIndex i 1 else i
def selectedIndexS (i : Fin 16) : Fin 16 := if flipS i then Weyl.mulIndex i 2 else i

def targetR1 : Fin 16 → Fin 12 := ![1, 1, 2, 4, 2, 4, 6, 6, 6, 6, 4, 2, 4, 2, 1, 1]
def targetR3 : Fin 16 → Fin 12 := ![3, 3, 7, 10, 7, 10, 11, 11, 11, 11, 10, 7, 10, 7, 3, 3]
def targetS : Fin 16 → Fin 12 := ![0, 5, 0, 5, 8, 9, 8, 9, 9, 8, 9, 8, 5, 0, 5, 0]

/-- Only finite root-index paths are checked here; every step is already a proved
identity of full root curves in the actual matrix group. -/
theorem pathR1 : ∀ i : Fin 16,
    rootPath 1 (WeylData.words (selectedIndexR i)).reverse = some (targetR1 i) := by decide +kernel

theorem pathR3 : ∀ i : Fin 16,
    rootPath 3 (WeylData.words (selectedIndexR i)).reverse = some (targetR3 i) := by decide +kernel

theorem pathS : ∀ i : Fin 16,
    rootPath 0 (WeylData.words (selectedIndexS i)).reverse = some (targetS i) := by decide +kernel

theorem selected_rep_r (i : Fin 16) :
    Weyl.rep (selectedIndexR i) = if flipR i then Weyl.rep i * r else Weyl.rep i := by
  cases h : flipR i
  · simp [selectedIndexR, h]
  · simp only [selectedIndexR, h, ↓reduceIte]
    rw [← Weyl.rep_mul, Weyl.rep_one]

theorem selected_rep_s (i : Fin 16) :
    Weyl.rep (selectedIndexS i) = if flipS i then Weyl.rep i * s else Weyl.rep i := by
  cases h : flipS i
  · simp [selectedIndexS, h]
  · simp only [selectedIndexS, h, ↓reduceIte]
    rw [← Weyl.rep_mul, Weyl.rep_two]

theorem selected_r_root_one (i : Fin 16) (a : Fin 8) :
    rightConj (root 1 a) (Weyl.rep (selectedIndexR i))⁻¹ = root (targetR1 i) a := by
  have h := rootPath_sound _ 1 (targetR1 i) a (pathR1 i)
  simpa only [evalWord_reverse, Weyl.rep] using h

theorem selected_r_root_three (i : Fin 16) (a : Fin 8) :
    rightConj (root 3 a) (Weyl.rep (selectedIndexR i))⁻¹ = root (targetR3 i) a := by
  have h := rootPath_sound _ 3 (targetR3 i) a (pathR3 i)
  simpa only [evalWord_reverse, Weyl.rep] using h

theorem selected_s_root (i : Fin 16) (a : Fin 8) :
    rightConj (root 0 a) (Weyl.rep (selectedIndexS i))⁻¹ = root (targetS i) a := by
  have h := rootPath_sound _ 0 (targetS i) a (pathS i)
  simpa only [evalWord_reverse, Weyl.rep] using h

theorem orientation_r (i : Fin 16) :
    (∀ u ∈ Rr, Weyl.rep i * u * (Weyl.rep i)⁻¹ ∈ U) ∨
      (∀ u ∈ Rr, (Weyl.rep i * r) * u * (Weyl.rep i * r)⁻¹ ∈ U) := by
  have hall : ∀ u ∈ Rr, Weyl.rep (selectedIndexR i) * u *
      (Weyl.rep (selectedIndexR i))⁻¹ ∈ U := by
    intro u hu
    have h := Collection.rightConj_mem_closure_of_generators
      (Set.range rRoot) U (Weyl.rep (selectedIndexR i))⁻¹ (by
        rintro _ ⟨p, rfl⟩
        change rightConj (rRoot p) (Weyl.rep (selectedIndexR i))⁻¹ ∈ U
        rw [rRoot, rightConj_mul_elements, selected_r_root_one, selected_r_root_three]
        exact U.mul_mem (root_mem_U _ _) (root_mem_U _ _)) hu
    simpa only [inv_inv] using h
  cases h : flipR i
  · exact Or.inl (by simpa [selected_rep_r, h] using hall)
  · exact Or.inr (by simpa [selected_rep_r, h] using hall)

theorem orientation_s (i : Fin 16) :
    (∀ u ∈ Rs, Weyl.rep i * u * (Weyl.rep i)⁻¹ ∈ U) ∨
      (∀ u ∈ Rs, (Weyl.rep i * s) * u * (Weyl.rep i * s)⁻¹ ∈ U) := by
  have hall : ∀ u ∈ Rs, Weyl.rep (selectedIndexS i) * u *
      (Weyl.rep (selectedIndexS i))⁻¹ ∈ U := by
    intro u hu
    have h := Collection.rightConj_mem_closure_of_generators
      (Set.range sRoot) U (Weyl.rep (selectedIndexS i))⁻¹ (by
        rintro _ ⟨a, rfl⟩
        change rightConj (root 0 a) (Weyl.rep (selectedIndexS i))⁻¹ ∈ U
        rw [selected_s_root]
        exact root_mem_U _ _) hu
    simpa only [inv_inv] using h
  cases h : flipS i
  · exact Or.inl (by simpa [selected_rep_s, h] using hall)
  · exact Or.inr (by simpa [selected_rep_s, h] using hall)

theorem orientation_r_B (i : Fin 16) :
    (∀ u ∈ Rr, Weyl.rep i * u * (Weyl.rep i)⁻¹ ∈ B) ∨
      (∀ u ∈ Rr, (Weyl.rep i * r) * u * (Weyl.rep i * r)⁻¹ ∈ B) := by
  rcases orientation_r i with h | h
  · exact Or.inl (fun u hu => (show U ≤ B from le_sup_left) (h u hu))
  · exact Or.inr (fun u hu => (show U ≤ B from le_sup_left) (h u hu))

theorem orientation_s_B (i : Fin 16) :
    (∀ u ∈ Rs, Weyl.rep i * u * (Weyl.rep i)⁻¹ ∈ B) ∨
      (∀ u ∈ Rs, (Weyl.rep i * s) * u * (Weyl.rep i * s)⁻¹ ∈ B) := by
  rcases orientation_s i with h | h
  · exact Or.inl (fun u hu => (show U ≤ B from le_sup_left) (h u hu))
  · exact Or.inr (fun u hu => (show U ≤ B from le_sup_left) (h u hu))

end Kourovka.Problem2153.RootSystem.RankOne

import Kourovka.Problem2153.RootSystem

set_option autoImplicit false

namespace Kourovka.Problem2153.RootSystem.RankOne

def rRoot (p : Fin 8 × Fin 8) : G := root 1 p.1 * root 3 p.2
def sRoot (a : Fin 8) : G := root 0 a

def Rr : Subgroup G := Subgroup.closure (Set.range rRoot)
def Rs : Subgroup G := Subgroup.closure (Set.range sRoot)

def Vr : Subgroup G :=
  Subgroup.closure {g | ∃ i : Fin 12, i ≠ 1 ∧ i ≠ 3 ∧ ∃ a, g = root i a}

def Vs : Subgroup G :=
  Subgroup.closure {g | ∃ i : Fin 12, i ≠ 0 ∧ ∃ a, g = root i a}

@[simp] theorem rRoot_zero : rRoot (0, 0) = 1 := by simp [rRoot]
@[simp] theorem sRoot_zero : sRoot 0 = 1 := by simp [sRoot]

theorem rRoot_mem_Rr (p : Fin 8 × Fin 8) : rRoot p ∈ Rr :=
  Subgroup.subset_closure ⟨p, rfl⟩

theorem sRoot_mem_Rs (a : Fin 8) : sRoot a ∈ Rs :=
  Subgroup.subset_closure ⟨a, rfl⟩

theorem root_one_mem_Rr (a : Fin 8) : root 1 a ∈ Rr := by
  simpa [rRoot] using rRoot_mem_Rr (a, 0)

theorem root_three_mem_Rr (a : Fin 8) : root 3 a ∈ Rr := by
  simpa [rRoot] using rRoot_mem_Rr (0, a)

theorem Rr_eq : Rr = Subgroup.closure (Set.range (root 1) ∪ Set.range (root 3)) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨p, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨p.1, rfl⟩))
      (Subgroup.subset_closure (Or.inr ⟨p.2, rfl⟩))
  · apply (Subgroup.closure_le _).mpr
    rintro g (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact root_one_mem_Rr a
    · exact root_three_mem_Rr a

theorem Rr_le_U : Rr ≤ U := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨p, rfl⟩
  exact U.mul_mem (root_mem_U 1 p.1) (root_mem_U 3 p.2)

theorem Rs_le_U : Rs ≤ U := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  exact root_mem_U 0 a

theorem root_mem_Vr (i : Fin 12) (hi1 : i ≠ 1) (hi3 : i ≠ 3) (a : Fin 8) :
    root i a ∈ Vr := Subgroup.subset_closure ⟨i, hi1, hi3, a, rfl⟩

theorem root_mem_Vs (i : Fin 12) (hi : i ≠ 0) (a : Fin 8) :
    root i a ∈ Vs := Subgroup.subset_closure ⟨i, hi, a, rfl⟩

theorem Vr_le_U : Vr ≤ U := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, _, _, a, rfl⟩
  exact root_mem_U i a

theorem Vs_le_U : Vs ≤ U := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, _, a, rfl⟩
  exact root_mem_U i a

end Kourovka.Problem2153.RootSystem.RankOne

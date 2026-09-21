import Kourovka2135.AbelianMovingGenerators
import Kourovka2135.GeneratingSets
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
The commutator map on two cosets of an abelian normal subgroup fills the
complete output coset when the two elements generate and [A,G] = A.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative commutatorElement
open AbelianDifference
variable {G : Type u} [Group G]

theorem closure_commutator_correction_pair (a b : G) :
    Subgroup.closure ({(paperCommutator a b)⁻¹ * b, a * paperCommutator a b} : Set G) =
      Subgroup.closure ({a, b} : Set G) := by
  let C := Subgroup.closure ({a, b} : Set G)
  let D := Subgroup.closure
    ({(paperCommutator a b)⁻¹ * b, a * paperCommutator a b} : Set G)
  have ha : a ∈ C := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hc : paperCommutator a b ∈ C :=
    C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem ha) (C.inv_mem hb)) ha) hb
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact C.mul_mem (C.inv_mem hc) hb
    · have heq := Set.mem_singleton_iff.mp hx
      subst x
      exact C.mul_mem ha hc
  · have he : (paperCommutator a b)⁻¹ * b ∈ D :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hd : a * paperCommutator a b ∈ D :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hbD : b ∈ D := by
      have hm := D.mul_mem (D.mul_mem hd he) (D.inv_mem hd)
      convert hm using 1
      simp only [paperCommutator]
      group
    have haD : a ∈ D := by
      have hm := D.mul_mem (D.mul_mem hbD hd) (D.inv_mem hbD)
      convert hm using 1
      simp only [paperCommutator]
      group
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact haD
    · have heq := Set.mem_singleton_iff.mp hx
      subst x
      exact hbD

theorem closure_inverse_pair (a b : G) :
    Subgroup.closure ({a⁻¹, b⁻¹} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure (Set.mem_insert _ _))
    · have heq : x = b⁻¹ := Set.mem_singleton_iff.mp hx
      subst x
      exact (Subgroup.closure _).inv_mem
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (Subgroup.closure _).inv_mem_iff.mp
        (Subgroup.subset_closure (Set.mem_insert _ _))
    · have heq : x = b := Set.mem_singleton_iff.mp hx
      subst x
      exact (Subgroup.closure _).inv_mem_iff.mp
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

variable (A : Subgroup G) [A.Normal] [IsMulCommutative A]

theorem iSup_conjugation_moving_eq_top (hA : ⁅A, (⊤ : Subgroup G)⁆ = A) :
    (⨆ g : G, movingSubgroup ((MulAut.conjNormal : G →* MulAut A) g)) = ⊤ := by
  let ρ : G →* MulAut A := MulAut.conjNormal
  let M := ⨆ g : G, movingSubgroup (ρ g)
  have hcomm : ⁅A, (⊤ : Subgroup G)⁆ ≤ M.map A.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a ha g _
    refine ⟨delta (ρ g) (⟨a⁻¹, A.inv_mem ha⟩ : A), ?_, ?_⟩
    · exact (le_iSup (fun g : G => movingSubgroup (ρ g)) g)
        (show delta (ρ g) (⟨a⁻¹, A.inv_mem ha⟩ : A) ∈ movingSubgroup (ρ g)
          from ⟨_, rfl⟩)
    · change (a⁻¹)⁻¹ * (g * a⁻¹ * g⁻¹) = a * g * a⁻¹ * g⁻¹
      simp only [inv_inv, mul_assoc]
  rw [hA] at hcomm
  apply top_le_iff.mp
  intro x _
  obtain ⟨y, hy, heq⟩ := hcomm x.property
  have hyx : y = x := Subtype.ext heq
  exact hyx ▸ hy

def abelianCorrection (a b : G) (u v : A) : A :=
  let ρ : G →* MulAut A := MulAut.conjNormal
  let c := paperCommutator a b
  (ρ c⁻¹ u)⁻¹ * (ρ (a * c)⁻¹ v)⁻¹ * ρ b⁻¹ u * v

omit [IsMulCommutative A] in
theorem paperCommutator_mul_eq_correction (a b : G) (u v : A) :
    paperCommutator (a * u) (b * v) =
      paperCommutator a b * (abelianCorrection A a b u v : G) := by
  simp only [abelianCorrection, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
    paperCommutator]
  group

theorem abelianCorrection_eq_deltas (a b : G) (u v : A) :
    abelianCorrection A a b u v =
      delta ((MulAut.conjNormal : G →* MulAut A) ((paperCommutator a b)⁻¹ * b)⁻¹)
        (MulAut.conjNormal (paperCommutator a b)⁻¹ u) *
      delta ((MulAut.conjNormal : G →* MulAut A) (a * paperCommutator a b)⁻¹) v⁻¹ := by
  let ρ : G →* MulAut A := MulAut.conjNormal
  have heq : ρ (((paperCommutator a b)⁻¹ * b)⁻¹)
      (ρ (paperCommutator a b)⁻¹ u) = ρ b⁻¹ u := by
    rw [← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  change _ = delta (ρ (((paperCommutator a b)⁻¹ * b)⁻¹))
    (ρ (paperCommutator a b)⁻¹ u) * delta (ρ (a * paperCommutator a b)⁻¹) v⁻¹
  rw [delta_apply, delta_apply, heq, (ρ (a * paperCommutator a b)⁻¹).map_inv, inv_inv]
  dsimp [abelianCorrection, ρ]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem exists_paperCommutator_mul_eq_of_abelian
    (a b : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (hA : ⁅A, (⊤ : Subgroup G)⁆ = A) (t : A) :
    ∃ u v : A, paperCommutator (a * u) (b * v) = paperCommutator a b * t := by
  let ρ : G →* MulAut A := MulAut.conjNormal
  let c := paperCommutator a b
  have hpair : Subgroup.closure ({(c⁻¹ * b)⁻¹, (a * c)⁻¹} : Set G) = ⊤ := by
    rw [closure_inverse_pair, closure_commutator_correction_pair, hgen]
  obtain ⟨s, z, hsz⟩ := exists_delta_mul_delta_of_generating_pair ρ
    (c⁻¹ * b)⁻¹ (a * c)⁻¹ hpair (iSup_conjugation_moving_eq_top A hA) t
  refine ⟨ρ c s, z⁻¹, ?_⟩
  rw [paperCommutator_mul_eq_correction, abelianCorrection_eq_deltas]
  congr 1
  apply congrArg Subtype.val
  change delta (ρ (c⁻¹ * b)⁻¹) (ρ c⁻¹ (ρ c s)) *
    delta (ρ (a * c)⁻¹) (z⁻¹)⁻¹ = t
  rw [show ρ c⁻¹ (ρ c s) = s by rw [map_inv]; exact (ρ c).symm_apply_apply s, inv_inv]
  exact hsz

end Kourovka2135

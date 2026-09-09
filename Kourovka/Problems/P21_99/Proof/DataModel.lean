import Kourovka.Problems.P21_99.Proof.DataInverseChecks
import Kourovka.Problems.P21_99.Proof.DataStepChecks
import Kourovka.Problems.P21_99.Proof.DataElementary
import Kourovka.Problems.P21_99.Proof.FiniteGroup
import Kourovka.Problems.P21_99.Proof.Generated
import Mathlib.Algebra.Group.Action.Pretransitive

/-! The concrete finite quotient group, built from checked sparse tables.

Only containment of the generated group in the 384-entry table is required.
The six block representatives have explicit words in the eight generators.
-/

namespace Kourovka.P21_99.Data

abbrev Ambient := LinearBlockGroup (Fin 6) (Vec 18)

def table (q : Fin 384) : Ambient :=
  ({ toFun := blockMap q
     invFun := blockMap (inverseIndex q)
     left_inv := (inverseChecks q).2.2.2
     right_inv := (inverseChecks q).2.2.1 },
   addEquivOfInverse (linear (matrixRows q)).toAddMonoidHom
     (linear (matrixRows (inverseIndex q))).toAddMonoidHom
     (fun x => congrArg (fun f : Vec 18 →ₗ[Scalar] Vec 18 => f x)
       (comp_id_of_entries _ _ (inverseChecks q).2.1))
     (fun x => congrArg (fun f : Vec 18 →ₗ[Scalar] Vec 18 => f x)
       (comp_id_of_entries _ _ (inverseChecks q).1)))

@[simp] theorem table_block (q : Fin 384) (i : Fin 6) :
    (table q).1 i = blockMap q i := rfl

@[simp] theorem table_vector (q : Fin 384) (v : Vec 18) :
    (table q).2 v = linear (matrixRows q) v := rfl

theorem table_zero : table 0 = 1 := by
  apply Prod.ext
  · apply Equiv.ext
    exact identity_checked.2
  · apply AddEquiv.ext
    intro v
    change linear (matrixRows 0) v = v
    have h : linear (matrixRows 0) = (LinearMap.id : Vec 18 →ₗ[Scalar] Vec 18) := by
      apply ext_entries
      intro i j
      change entry (matrixRows 0) i j = basisVector j i
      rw [identity_checked.1]
      by_cases hi : i = j
      · subst i; simp [identityEntry, basisVector]
      · simp [identityEntry, basisVector, hi]
    exact congrArg (fun f : Vec 18 →ₗ[Scalar] Vec 18 => f v) h

def generator (g : Fin 8) : Ambient := table (generatorIndex g)

theorem table_step (q : Fin 384) (g : Fin 8) :
    table q * generator g = table (step q g) := by
  apply Prod.ext
  · apply Equiv.ext
    exact (stepChecks q g).2
  · apply AddEquiv.ext
    intro v
    change linear (matrixRows q) (linear (matrixRows (generatorIndex g)) v) =
      linear (matrixRows (step q g)) v
    exact congrArg (fun f : Vec 18 →ₗ[Scalar] Vec 18 => f v)
      (comp_eq_of_entries _ _ _ (stepChecks q g).1)

def K : Subgroup Ambient := Subgroup.closure (Set.range generator)

theorem exists_index (k : K) : ∃ q, table q = (k : Ambient) := by
  apply generated_mem_range table generator ⟨0, table_zero⟩
  · intro q g
    exact ⟨step q g, table_step q g⟩
  · exact k.property

noncomputable def index (k : K) : Fin 384 := Classical.choose (exists_index k)

theorem index_eq (k : K) : table (index k) = (k : Ambient) :=
  Classical.choose_spec (exists_index k)

theorem smul_block (k : K) (i : Fin 6) : k • i = blockMap (index k) i := by
  change (k : Ambient).1 i = _
  rw [← index_eq k]
  rfl

theorem smul_vector (k : K) (v : Vec 18) :
    k • v = linear (matrixRows (index k)) v := by
  change (k : Ambient).2 v = _
  rw [← index_eq k]
  rfl

theorem fold_table (w : List (Fin 8)) (q : Fin 384) :
    table (w.foldl step q) = table q * (w.map generator).prod := by
  induction w generalizing q with
  | nil => simp
  | cons g w ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [ih, ← table_step, mul_assoc]

theorem word_mem (w : List (Fin 8)) : (w.map generator).prod ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons g w ih =>
    exact K.mul_mem (Subgroup.subset_closure ⟨g, rfl⟩) ih

theorem representative_mem (i : Fin 6) : table (representativeIndex i) ∈ K := by
  have h := fold_table (representativeWord i) 0
  change table (wordIndex (representativeWord i)) = _ at h
  rw [(representative_checked i).1, table_zero, one_mul] at h
  rw [h]
  exact word_mem _

def representative (i : Fin 6) : K :=
  ⟨table (representativeIndex i), representative_mem i⟩

theorem representative_smul (i : Fin 6) : representative i • (0 : Fin 6) = i :=
  (representative_checked i).2

instance block_pretransitive : MulAction.IsPretransitive K (Fin 6) where
  exists_smul_eq a b := by
    refine ⟨representative b * (representative a)⁻¹, ?_⟩
    calc
      (representative b * (representative a)⁻¹) • a =
          representative b • ((representative a)⁻¹ • a) := mul_smul _ _ _
      _ = representative b • ((representative a)⁻¹ • (representative a • (0 : Fin 6))) :=
        congrArg (fun x : Fin 6 => representative b • ((representative a)⁻¹ • x))
          (representative_smul a).symm
      _ = b := by rw [inv_smul_smul, representative_smul]

end Kourovka.P21_99.Data

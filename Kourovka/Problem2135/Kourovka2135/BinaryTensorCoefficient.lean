import Kourovka2135.BinaryExteriorCharacter
import Mathlib.Algebra.Module.RingHom

/-! Concrete coefficient modules for the binary squarefree algebra.

For `I ⊆ Fin f`, the coefficient space is the exterior algebra on coordinates
indexed by `I`. Coordinate restriction induces an algebra homomorphism from
the full exterior algebra, and hence its action on the coefficient space.
The resulting action inserts an index in `I` and kills indices outside `I`.
This constructs actual modules; it makes no irreducibility or classification
assertion, and no tensor representation identification is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryTensorCoefficient

open scoped CharTwo IsMulCommutative

variable (k : Type*) [CommRing k]
variable {f : ℕ} (I : Finset (Fin f))

/-- The coefficient space on the coordinates in `I`. -/
abbrev Carrier := ExteriorAlgebra k (I → k)

/-- Its squarefree basis is indexed by actual subsets of `I`. -/
def basis : Module.Basis (Finset I) k (Carrier k I) :=
  (Pi.basisFun k I).ExteriorAlgebra

def generator (i : I) : Carrier k I :=
  ExteriorAlgebra.ι k (Pi.basisFun k I i)

@[simp] theorem basis_empty : basis k I ∅ = 1 := by
  change (Pi.basisFun k I).ExteriorAlgebra ∅ = 1
  rw [ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply _

@[simp] theorem basis_singleton (i : I) : basis k I {i} = generator k I i := by
  let s : Set.powersetCard I 1 := Set.powersetCard.ofCard (Finset.card_singleton i)
  have he : (Set.powersetCard.ofFinEmbEquiv.symm s) 0 = i := by
    have hm : (Set.powersetCard.ofFinEmbEquiv.symm s) 0 ∈ s.val :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨0, rfl⟩
    simpa [s] using hm
  change (Pi.basisFun k I).ExteriorAlgebra {i} = ExteriorAlgebra.ι k (Pi.basisFun k I i)
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  change ExteriorAlgebra.ιMulti k 1
    ((Pi.basisFun k I) ∘ Set.powersetCard.ofFinEmbEquiv.symm s) = _
  simp [ExteriorAlgebra.ιMulti_succ_apply, he]

@[simp] theorem generator_square (i : I) : generator k I i * generator k I i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem basis_mul_of_not_disjoint (J K : Finset I) (h : ¬Disjoint J K) :
    basis k I J * basis k I K = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun k I)
    (Set.powersetCard.ofCard (s := J) rfl)
    (Set.powersetCard.ofCard (s := K) rfl) h

section CharTwo

variable [CharP k 2]

private theorem neg_eq_self (z : Carrier k I) : -z = z := by
  have h := congrArg (fun a : k => a • z) (CharTwo.neg_eq (1 : k))
  simpa only [neg_one_smul, one_smul] using h

private theorem intUnit_smul_eq (u : ℤˣ) (z : Carrier k I) : u • z = z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simpa only [Units.neg_smul, one_smul] using neg_eq_self k I z

theorem basis_mul_of_disjoint (J K : Finset I) (h : Disjoint J K) :
    basis k I J * basis k I K = basis k I (J ∪ K) := by
  let S : Set.powersetCard I J.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard I K.card := Set.powersetCard.ofCard rfl
  have hST : Disjoint S.val T.val := h
  have hm := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun k I) S T hST
  change basis k I J * basis k I K = _ at hm
  rw [intUnit_smul_eq k I] at hm
  simpa only [basis, Set.powersetCard.coe_disjUnion, S, T,
    Set.powersetCard.val_ofCard, Finset.disjUnion_eq_union] using hm

theorem basis_mul (J K : Finset I) :
    basis k I J * basis k I K = if Disjoint J K then basis k I (J ∪ K) else 0 := by
  by_cases h : Disjoint J K
  · rw [ite_eq_left h]
    exact basis_mul_of_disjoint k I J K h
  · rw [ite_eq_right h]
    exact basis_mul_of_not_disjoint k I J K h

theorem basis_mul_comm (J K : Finset I) : basis k I J * basis k I K =
    basis k I K * basis k I J := by
  rw [basis_mul, basis_mul]
  simp only [disjoint_comm, Finset.union_comm]

theorem mul_comm (x y : Carrier k I) : x * y = y * x := by
  have hxy : LinearMap.mulLeft k x = LinearMap.mulRight k x := by
    apply (basis k I).ext
    intro K
    change x * basis k I K = basis k I K * x
    have hK : LinearMap.mulRight k (basis k I K) =
        LinearMap.mulLeft k (basis k I K) := by
      apply (basis k I).ext
      intro J
      exact basis_mul_comm k I J K
    exact LinearMap.congr_fun hK x
  exact LinearMap.congr_fun hxy y

instance instIsMulCommutative : IsMulCommutative (Carrier k I) :=
  IsMulCommutative.of_comm (mul_comm k I)

theorem generator_mul_basis (i : I) (J : Finset I) :
    generator k I i * basis k I J = if i ∈ J then 0 else basis k I (insert i J) := by
  rw [← basis_singleton k I i, basis_mul]
  by_cases h : i ∈ J <;> simp [h]

end CharTwo

/-- Restrict a coordinate vector to the coordinates belonging to `I`. -/
def coordinateRestriction : (Fin f → k) →ₗ[k] (I → k) where
  toFun v i := v i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateRestriction_apply (v : Fin f → k) (i : I) :
    coordinateRestriction k I v i = v i := rfl

theorem coordinateRestriction_basis_of_mem (i : Fin f) (hi : i ∈ I) :
    coordinateRestriction k I (Pi.basisFun k (Fin f) i) = Pi.basisFun k I ⟨i, hi⟩ := by
  ext j
  simp [coordinateRestriction, Pi.single_apply, Subtype.ext_iff]

theorem coordinateRestriction_basis_of_not_mem (i : Fin f) (hi : i ∉ I) :
    coordinateRestriction k I (Pi.basisFun k (Fin f) i) = 0 := by
  ext j
  have hij : i ≠ (j : Fin f) := by
    intro h
    exact hi (h.symm ▸ j.property)
  simp [coordinateRestriction, hij]

/-- The algebra map killing precisely the omitted generators. -/
def projection : BinaryExteriorAlgebra.Carrier k f →ₐ[k] Carrier k I :=
  ExteriorAlgebra.map (coordinateRestriction k I)

@[simp] theorem projection_generator_of_mem (i : Fin f) (hi : i ∈ I) :
    projection k I (BinaryExteriorAlgebra.generator k f i) = generator k I ⟨i, hi⟩ := by
  simp only [projection, BinaryExteriorAlgebra.generator, ExteriorAlgebra.map_apply_ι,
    coordinateRestriction_basis_of_mem k I i hi, generator]

@[simp] theorem projection_generator_of_not_mem (i : Fin f) (hi : i ∉ I) :
    projection k I (BinaryExteriorAlgebra.generator k f i) = 0 := by
  simp only [projection, BinaryExteriorAlgebra.generator, ExteriorAlgebra.map_apply_ι,
    coordinateRestriction_basis_of_not_mem k I i hi, map_zero]

/-- The actual action of the full squarefree algebra, by restriction of scalars. -/
instance instModule : Module (BinaryExteriorAlgebra.Carrier k f) (Carrier k I) :=
  Module.compHom (Carrier k I) (projection k I).toRingHom

theorem smul_eq (a : BinaryExteriorAlgebra.Carrier k f) (v : Carrier k I) :
    a • v = projection k I a * v := rfl

instance instIsScalarTower :
    IsScalarTower k (BinaryExteriorAlgebra.Carrier k f) (Carrier k I) where
  smul_assoc r a v := by
    change projection k I (r • a) * v = r • (projection k I a * v)
    rw [map_smul, smul_mul_assoc]

instance instSMulCommClass :
    SMulCommClass k (BinaryExteriorAlgebra.Carrier k f) (Carrier k I) where
  smul_comm r a v := by
    change r • (projection k I a * v) = projection k I a * (r • v)
    exact (mul_smul_comm _ _ _).symm

/-- An omitted algebra generator acts by zero on the entire coefficient space. -/
theorem generator_smul_of_not_mem (i : Fin f) (hi : i ∉ I) (v : Carrier k I) :
    BinaryExteriorAlgebra.generator k f i • v = 0 := by
  rw [smul_eq, projection_generator_of_not_mem k I i hi, zero_mul]

variable [CharP k 2]

/-- An included algebra generator inserts its index into the coefficient basis. -/
theorem generator_smul_basis (i : I) (J : Finset I) :
    BinaryExteriorAlgebra.generator k f i • basis k I J =
      if i ∈ J then 0 else basis k I (insert i J) := by
  rw [smul_eq, projection_generator_of_mem k I i i.property]
  exact generator_mul_basis k I i J

end Kourovka2135.BinaryTensorCoefficient

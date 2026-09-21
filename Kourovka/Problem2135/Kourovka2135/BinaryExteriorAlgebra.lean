import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.CharP.Two

/-! A concrete squarefree coordinate algebra in characteristic two.

The underlying ring is the exterior algebra. Its existing basis multiplication
theorems become unsigned in characteristic two, and imply commutativity.
No project-specific algebraic or representation-theoretic assumption is used.
-/

set_option autoImplicit false
noncomputable section

namespace Kourovka2135.BinaryExteriorAlgebra

open scoped CharTwo

variable (k : Type*) [CommRing k] (f : ℕ)

/-- The concrete coordinate algebra on `f` square-zero generators. -/
abbrev Carrier := ExteriorAlgebra k (Fin f → k)

/-- The squarefree monomial basis, indexed by subsets of the generators. -/
def basis : Module.Basis (Finset (Fin f)) k (Carrier k f) :=
  (Pi.basisFun k (Fin f)).ExteriorAlgebra

/-- The generator indexed by `i`. -/
def generator (i : Fin f) : Carrier k f :=
  ExteriorAlgebra.ι k (Pi.basisFun k (Fin f) i)

@[simp] theorem basis_empty : basis k f ∅ = 1 := by
  change (Pi.basisFun k (Fin f)).ExteriorAlgebra ∅ = 1
  rw [ExteriorAlgebra.basis_apply]
  simp [ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply _

@[simp] theorem basis_singleton (i : Fin f) :
    basis k f {i} = generator k f i := by
  let s : Set.powersetCard (Fin f) 1 :=
    Set.powersetCard.ofCard (Finset.card_singleton i)
  have he : (Set.powersetCard.ofFinEmbEquiv.symm s) 0 = i := by
    have hm : (Set.powersetCard.ofFinEmbEquiv.symm s) 0 ∈ s.val :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨0, rfl⟩
    simpa [s] using hm
  change (Pi.basisFun k (Fin f)).ExteriorAlgebra {i} =
    ExteriorAlgebra.ι k (Pi.basisFun k (Fin f) i)
  rw [ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  change ExteriorAlgebra.ιMulti k 1
    ((Pi.basisFun k (Fin f)) ∘ Set.powersetCard.ofFinEmbEquiv.symm s) = _
  simp [ExteriorAlgebra.ιMulti_succ_apply, he]

@[simp] theorem generator_square (i : Fin f) :
    generator k f i * generator k f i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem basis_mul_of_not_disjoint (s t : Finset (Fin f))
    (h : ¬Disjoint s t) : basis k f s * basis k f t = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun k (Fin f))
    (Set.powersetCard.ofCard (s := s) rfl)
    (Set.powersetCard.ofCard (s := t) rfl) h

variable [CharP k 2]

private theorem neg_eq_self (z : Carrier k f) : -z = z := by
  have h := congrArg (fun a : k => a • z) (CharTwo.neg_eq (1 : k))
  simpa only [neg_one_smul, one_smul] using h

private theorem intUnit_smul_eq (u : ℤˣ) (z : Carrier k f) : u • z = z := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simpa only [Units.neg_smul, one_smul] using neg_eq_self k f z

theorem basis_mul_of_disjoint (s t : Finset (Fin f))
    (h : Disjoint s t) : basis k f s * basis k f t = basis k f (s ∪ t) := by
  let S : Set.powersetCard (Fin f) s.card := Set.powersetCard.ofCard rfl
  let T : Set.powersetCard (Fin f) t.card := Set.powersetCard.ofCard rfl
  have hST : Disjoint S.val T.val := h
  have hm := ExteriorAlgebra.basis_mul_of_disjoint (Pi.basisFun k (Fin f)) S T hST
  change basis k f s * basis k f t = _ at hm
  rw [intUnit_smul_eq k f] at hm
  simpa only [basis, Set.powersetCard.coe_disjUnion, S, T,
    Set.powersetCard.val_ofCard, Finset.disjUnion_eq_union] using hm

/-- The complete multiplication table of the squarefree basis. -/
theorem basis_mul (s t : Finset (Fin f)) :
    basis k f s * basis k f t =
      if Disjoint s t then basis k f (s ∪ t) else 0 := by
  by_cases h : Disjoint s t
  · rw [ite_eq_left h]
    exact basis_mul_of_disjoint k f s t h
  · rw [ite_eq_right h]
    exact basis_mul_of_not_disjoint k f s t h

theorem basis_mul_comm (s t : Finset (Fin f)) :
    basis k f s * basis k f t = basis k f t * basis k f s := by
  rw [basis_mul, basis_mul]
  simp only [disjoint_comm, Finset.union_comm]

/-- Commutativity follows from the basis multiplication table by bilinearity. -/
theorem mul_comm (x y : Carrier k f) : x * y = y * x := by
  have hxy : LinearMap.mulLeft k x = LinearMap.mulRight k x := by
    apply (basis k f).ext
    intro t
    change x * basis k f t = basis k f t * x
    have ht : LinearMap.mulRight k (basis k f t) =
        LinearMap.mulLeft k (basis k f t) := by
      apply (basis k f).ext
      intro s
      exact basis_mul_comm k f s t
    exact LinearMap.congr_fun ht x
  exact LinearMap.congr_fun hxy y

/-- Opening the existing `IsMulCommutative` scope gives a `CommRing` on this
same ring, with no change to multiplication. -/
instance instIsMulCommutative : IsMulCommutative (Carrier k f) :=
  IsMulCommutative.of_comm (mul_comm k f)

/-- A generator either kills a monomial containing it or adjoins its index. -/
theorem generator_mul_basis (i : Fin f) (s : Finset (Fin f)) :
    generator k f i * basis k f s =
      if i ∈ s then 0 else basis k f (insert i s) := by
  rw [← basis_singleton k f i, basis_mul]
  by_cases h : i ∈ s
  · simp [h]
  · simp [h]

end Kourovka2135.BinaryExteriorAlgebra

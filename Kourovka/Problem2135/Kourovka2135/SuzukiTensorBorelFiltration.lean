import Kourovka2135.SuzukiTensorNatural
import Kourovka2135.SuzukiNaturalBorelFiltration
import Kourovka2135.TriangularBasisH1
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Finset.Sort

/-! The complete Borel flag in the actual tensor of natural Frobenius twists.
An order extending the pointwise order on pure basis tuples makes the action
upper triangular. The resulting scalar characters are the products of the
actual natural diagonal characters, with their Frobenius multiplicities. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiTensorBorelFiltration

open SuzukiTorusMovingRank SuzukiTensorNatural
open SuzukiNaturalBorelFiltration (B matrix diagonalCharacter torusInBorel rootInBorel)
open scoped PiTensorProduct

variable (m : ℕ) (I : Finset (Fin (2 * m + 1)))

abbrev Index := I → Fin 4
abbrev Space := TensorSpace (K m) m I

def representation : Representation (K m) (B m) (Space m I) :=
  (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m))).comp
    (SuzukiGeometry.borel m).subtype

abbrev extensionOrder : LinearOrder (Index m I) :=
  inferInstanceAs (LinearOrder (LinearExtension (Index m I)))

/-- A chosen linear extension, with no choice of a representation isomorphism. -/
def enumeration : Fin (Fintype.card (Index m I)) ≃ Index m I := by
  let : LinearOrder (Index m I) := extensionOrder m I
  let : PartialOrder (Index m I) := (extensionOrder m I).toPartialOrder
  let : Preorder (Index m I) := (extensionOrder m I).toPreorder
  let : LE (Index m I) := (extensionOrder m I).toLE
  exact (Fintype.orderIsoFinOfCardEq (Index m I) rfl).toEquiv

theorem enumeration_mono {a b : Fin (Fintype.card (Index m I))}
    (h : ∀ i : I, enumeration m I a i ≤ enumeration m I b i) : a ≤ b := by
  have he : @LE.le (Index m I) (extensionOrder m I).toLE
      (enumeration m I a) (enumeration m I b) := toLinearExtension.monotone h
  let : LinearOrder (Index m I) := extensionOrder m I
  let : PartialOrder (Index m I) := (extensionOrder m I).toPartialOrder
  let : Preorder (Index m I) := (extensionOrder m I).toPreorder
  let : LE (Index m I) := (extensionOrder m I).toLE
  exact (Fintype.orderIsoFinOfCardEq (Index m I) rfl).le_iff_le.mp he

def orderedBasis : Module.Basis (Fin (Fintype.card (Index m I))) (K m) (Space m I) :=
  (tensorBasis (K m) m I).reindex (enumeration m I).symm

/-- The actual matrix coefficient on pure tensors is a product of entries. -/
theorem basis_coefficient (g : B m) (a b : Index m I) :
    (tensorBasis (K m) m I).repr
      (representation m I g (tensorBasis (K m) m I b)) a =
        ∏ i : I, matrix m g (a i) (b i) ^ (2 ^ i.val.val) := by
  change (tensorBasis (K m) m I).repr
    (SuzukiTensorNatural.representation (K m) m I (RingHom.id (K m)) g.val
      (tensorBasis (K m) m I b)) a = _
  simp only [tensorBasis, Basis.piTensorProduct_apply, representation_tprod,
    Basis.piTensorProduct_repr_tprod_apply]
  apply Finset.prod_congr rfl
  intro i _
  simp [naturalTwist_apply, Pi.basisFun_apply, matrix, matrixHom, Pi.single_apply]

theorem orderedBasis_upper (g : B m) (a b : Fin (Fintype.card (Index m I)))
    (hba : b < a) :
    (orderedBasis m I).repr (representation m I g (orderedBasis m I b)) a = 0 := by
  rw [orderedBasis, Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply,
    basis_coefficient]
  simp only [Equiv.symm_symm]
  by_contra hn
  have hab : ∀ i : I, enumeration m I a i ≤ enumeration m I b i := by
    intro i
    by_contra hi
    have hz : matrix m g (enumeration m I a i) (enumeration m I b i) = 0 :=
      SuzukiNaturalBorelFiltration.matrix_upper m g _ _ (lt_of_not_ge hi)
    apply hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [hz, zero_pow (by positivity : 2 ^ i.val.val ≠ 0)]
  exact (not_le_of_gt hba) (enumeration_mono m I hab)

/-- The actual scalar Borel character of the indicated pure tensor. -/
def tensorCharacter (a : Index m I) : B m →* (K m)ˣ where
  toFun g := ∏ i : I, diagonalCharacter m (a i) g ^ (2 ^ i.val.val)
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, mul_pow, Finset.prod_mul_distrib]

theorem tensorCharacter_coe (a : Index m I) (g : B m) :
    (tensorCharacter m I a g : K m) =
      ∏ i : I, matrix m g (a i) (a i) ^ (2 ^ i.val.val) := by
  simp [tensorCharacter]

def scalar (a : Index m I) : Representation (K m) (B m) (K m) where
  toFun g := (tensorCharacter m I a g : K m) • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp
  map_mul' g h := by apply LinearMap.ext; intro x; simp [mul_assoc, mul_left_comm]

@[simp] theorem scalar_apply (a : Index m I) (g : B m) (x : K m) :
    scalar m I a g x = (tensorCharacter m I a g : K m) * x := rfl

theorem diagonal_eq (n : Fin (Fintype.card (Index m I))) (g : B m) :
    TriangularBasisH1.entry (representation m I) (orderedBasis m I) g n n =
      (tensorCharacter m I (enumeration m I n) g : K m) := by
  rw [TriangularBasisH1.entry, orderedBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, basis_coefficient, tensorCharacter_coe]
  simp only [Equiv.symm_symm]

def scalarEquiv (n : Fin (Fintype.card (Index m I))) :
    (TriangularBasisH1.weightRepresentation (representation m I) (orderedBasis m I)
      (orderedBasis_upper m I) n).Equiv (scalar m I (enumeration m I n)) := by
  refine Representation.Equiv.mk (LinearEquiv.refl (K m) (K m)) ?_
  intro g
  apply LinearMap.ext
  intro x
  change TriangularBasisH1.entry (representation m I) (orderedBasis m I) g n n * x =
    (tensorCharacter m I (enumeration m I n) g : K m) * x
  rw [diagonal_eq]

abbrev flag (n : ℕ) := TriangularBasisH1.flag (orderedBasis m I) n
abbrev layer (n : ℕ) := TriangularBasisH1.layer (representation m I) (orderedBasis m I)
  (orderedBasis_upper m I) n

/-- The actual coordinate short exact sequence at every pure-basis position. -/
theorem step_shortExact (n : Fin (Fintype.card (Index m I))) :
    (TriangularBasisH1.stepComplex (representation m I) (orderedBasis m I)
      (orderedBasis_upper m I) n).ShortExact :=
  TriangularBasisH1.stepComplex_shortExact (representation m I) (orderedBasis m I)
    (orderedBasis_upper m I) n

def factorEquiv (n : Fin (Fintype.card (Index m I))) :=
  (TriangularBasisH1.factorEquiv (representation m I) (orderedBasis m I)
    (orderedBasis_upper m I) n).trans (scalarEquiv m I n)

theorem tensorCharacter_root (a : Index m I) (r : SuzukiGeometry.root m) :
    tensorCharacter m I a (rootInBorel m r) = 1 := by
  simp [tensorCharacter, SuzukiNaturalBorelFiltration.diagonalCharacter_root]

def torusCharacter (a : Index m I) : (K m)ˣ →* (K m)ˣ :=
  (tensorCharacter m I a).comp (torusInBorel m)

/-- Signed exponents in the actual natural diagonal order. -/
def diagonalExponent : Fin 4 → ℤ :=
  ![((1 + 2 ^ m : ℕ) : ℤ), ((2 ^ m : ℕ) : ℤ),
    -((2 ^ m : ℕ) : ℤ), -((1 + 2 ^ m : ℕ) : ℤ)]

def tensorExponent (a : Index m I) : ℤ :=
  ∑ i : I, (2 : ℤ) ^ i.val.val * diagonalExponent m (a i)

theorem diagonal_torus_exponent (j : Fin 4) (u : (K m)ˣ) :
    diagonalCharacter m j (torusInBorel m u) = u ^ diagonalExponent m j := by
  apply Units.ext
  rw [SuzukiNaturalBorelFiltration.diagonalCharacter_torus]
  fin_cases j
  · change (u : K m) ^ (1 + 2 ^ m) = ((u ^ (((1 + 2 ^ m : ℕ) : ℤ)) : (K m)ˣ) : K m)
    simp only [zpow_natCast, Units.val_pow_eq_pow_val]
  · change (u : K m) ^ (2 ^ m) = ((u ^ (((2 ^ m : ℕ) : ℤ)) : (K m)ˣ) : K m)
    simp only [zpow_natCast, Units.val_pow_eq_pow_val]
  · change ((u : K m) ^ (2 ^ m))⁻¹ = ((u ^ (-((2 ^ m : ℕ) : ℤ)) : (K m)ˣ) : K m)
    simp only [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  · change ((u : K m) ^ (1 + 2 ^ m))⁻¹ = ((u ^ (-((1 + 2 ^ m : ℕ) : ℤ)) : (K m)ˣ) : K m)
    simp only [zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

theorem torusCharacter_exponent (a : Index m I) (u : (K m)ˣ) :
    torusCharacter m I a u = u ^ tensorExponent m I a := by
  classical
  have hz (s : Finset I) :
      (∏ i ∈ s, u ^ ((2 : ℤ) ^ i.val.val * diagonalExponent m (a i))) =
        u ^ (∑ i ∈ s, (2 : ℤ) ^ i.val.val * diagonalExponent m (a i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  change (∏ i : I, diagonalCharacter m (a i) (torusInBorel m u) ^ (2 ^ i.val.val)) = _
  simp only [diagonal_torus_exponent, tensorExponent]
  rw [← hz Finset.univ]
  apply Finset.prod_congr rfl
  intro i _
  calc
    _ = (u ^ diagonalExponent m (a i)) ^ ((2 ^ i.val.val : ℕ) : ℤ) :=
      (zpow_natCast _ _).symm
    _ = u ^ (diagonalExponent m (a i) * ((2 ^ i.val.val : ℕ) : ℤ)) :=
      (zpow_mul _ _ _).symm
    _ = _ := by congr 1; push_cast; ring

/-- The tensor Borel H1 is bounded by its genuine scalar factors, with multiplicity. -/
theorem finrank_H1_le_sum :
    Module.finrank (K m) (groupCohomology (Rep.of (representation m I)) 1) ≤
      ∑ a : Index m I, Module.finrank (K m) (groupCohomology (Rep.of (scalar m I a)) 1) := by
  have h := TriangularBasisH1.finrank_H1_le_sum
    (representation m I) (orderedBasis m I) (orderedBasis_upper m I)
  calc
    _ ≤ ∑ n : Fin (Fintype.card (Index m I)), Module.finrank (K m)
      (groupCohomology (Rep.of (TriangularBasisH1.weightRepresentation
        (representation m I) (orderedBasis m I) (orderedBasis_upper m I) n)) 1) := h
    _ = ∑ n : Fin (Fintype.card (Index m I)), Module.finrank (K m)
      (groupCohomology (Rep.of (scalar m I (enumeration m I n))) 1) := by
      apply Finset.sum_congr rfl
      intro n _
      exact RepresentationCohomologyAlternative.finrank_cohomology_eq _ _ (scalarEquiv m I n) 1
    _ = _ := Equiv.sum_comp (enumeration m I) (fun a : Index m I =>
      Module.finrank (K m) (groupCohomology (Rep.of (scalar m I a)) 1))

end Kourovka2135.SuzukiTensorBorelFiltration

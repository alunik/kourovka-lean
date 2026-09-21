import Kourovka2135.SuzukiBruhat
import Kourovka2135.CohomologyH1FiltrationBound
import Mathlib.LinearAlgebra.Isomorphisms

/-! The actual four-step coordinate flag of the natural Suzuki module on
its actual Borel subgroup. Each next-coordinate map is a surjective
intertwiner to the corresponding diagonal character, with kernel precisely
the previous coordinate layer. No factor splitting or cohomology input is
assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kourovka2135.SuzukiNaturalBorelFiltration

open CategoryTheory BenderSuzuki.MatrixGroups SuzukiGeometry
open scoped Matrix MatrixGroups Pointwise

abbrev B (m : ℕ) := borel m
abbrev V (m : ℕ) := Fin 4 → K m

def representation (m : ℕ) : Representation (K m) (B m) (V m) :=
  (SuzukiTorusMovingRank.natural m).comp (borel m).subtype

def matrix (m : ℕ) (g : B m) : Matrix (Fin 4) (Fin 4) (K m) :=
  (((g : G m) : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m))

@[simp] theorem matrix_one (m : ℕ) : matrix m 1 = 1 := rfl
@[simp] theorem matrix_mul (m : ℕ) (g h : B m) :
    matrix m (g * h) = matrix m g * matrix m h := rfl

theorem representation_apply (m : ℕ) (g : B m) (v : V m) (i : Fin 4) :
    representation m g v i = ∑ j : Fin 4, matrix m g i j * v j :=
  SuzukiTorusMovingRank.natural_apply m g.val v i

/-- Actual normalized root-times-torus coordinates for every Borel element. -/
theorem exists_root_torus (m : ℕ) (g : B m) :
    ∃ a b : K m, ∃ u : (K m)ˣ,
      ((g : G m) : GL (Fin 4) (K m)) = SuzukiRootGL m a b * SuzukiTorusGL m u := by
  have hg : ((g : G m) : GL (Fin 4) (K m)) ∈
      (rootGL m : Set (GL (Fin 4) (K m))) * (torusGL m : Set (GL (Fin 4) (K m))) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (torusGL_le_normalizer_rootGL m)]
    exact g.property
  obtain ⟨f, hf, h, hh, hfh⟩ := hg
  obtain ⟨a, b, hab⟩ := (suzukiRootGL_mem_closure_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m) f).mp hf
  obtain ⟨u, hu⟩ := (suzukiTorusGL_mem_closure_iff m h).mp hh
  exact ⟨a, b, u, hfh.symm.trans (by rw [hab, hu])⟩

theorem matrix_upper (m : ℕ) (g : B m) (i j : Fin 4) (hji : j < i) :
    matrix m g i j = 0 := by
  obtain ⟨a, b, u, hg⟩ := exists_root_torus m g
  have hm := congrArg (fun A : GL (Fin 4) (K m) =>
    (A : Matrix (Fin 4) (Fin 4) (K m))) hg
  change matrix m g = (SuzukiRootGL m a b : Matrix (Fin 4) (Fin 4) (K m)) *
    (SuzukiTorusGL m u : Matrix (Fin 4) (Fin 4) (K m)) at hm
  rw [hm]
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mul_apply, Fin.sum_univ_four] at hji ⊢

theorem diagonal_mul (m : ℕ) (i : Fin 4) (g h : B m) :
    matrix m (g * h) i i = matrix m g i i * matrix m h i i := by
  rw [matrix_mul, Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [matrix_upper m g i j hj, zero_mul]
    · rw [matrix_upper m h j i hj, mul_zero]
  · simp

def diagonalHom (m : ℕ) (i : Fin 4) : B m →* K m where
  toFun g := matrix m g i i
  map_one' := by simp
  map_mul' g h := diagonal_mul m i g h

def diagonalCharacter (m : ℕ) (i : Fin 4) : B m →* (K m)ˣ :=
  (diagonalHom m i).toHomUnits

@[simp] theorem diagonalCharacter_coe (m : ℕ) (i : Fin 4) (g : B m) :
    (diagonalCharacter m i g : K m) = matrix m g i i := rfl

def weightRepresentation (m : ℕ) (i : Fin 4) : Representation (K m) (B m) (K m) where
  toFun g := matrix m g i i • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change matrix m (g * h) i i * x = matrix m g i i * (matrix m h i i * x)
    rw [diagonal_mul, mul_assoc]

@[simp] theorem weightRepresentation_apply (m : ℕ) (i : Fin 4) (g : B m) (x : K m) :
    weightRepresentation m i g x = (diagonalCharacter m i g : K m) * x := rfl

def rootInBorel (m : ℕ) : root m →* B m :=
  Subgroup.inclusion (Subgroup.comap_mono (show rootGL m ≤ borelGL m from le_sup_left))

def torusInBorel (m : ℕ) : (K m)ˣ →* B m :=
  (SuzukiTorusMovingRank.torusHom m).codRestrict (borel m) (fun u => by
    change SuzukiTorusGL m u ∈ borelGL m
    exact (show torusGL m ≤ borelGL m from le_sup_right)
      (Subgroup.subset_closure ⟨u, rfl⟩))

theorem diagonalCharacter_root (m : ℕ) (i : Fin 4) (r : root m) :
    diagonalCharacter m i (rootInBorel m r) = 1 := by
  apply Units.ext
  obtain ⟨a, b, hab⟩ := (suzukiRootGL_mem_closure_iff m (tits m)
    (SuzukiTorusMovingRank.tits_sq m) (SuzukiTorusMovingRank.tits_apply m)
    ((r : G m) : GL (Fin 4) (K m))).mp r.property
  change (((r : G m) : GL (Fin 4) (K m)) : Matrix (Fin 4) (Fin 4) (K m)) i i = 1
  rw [hab]
  fin_cases i <;> simp [SuzukiRootGL, SuzukiRootMatrix]

theorem diagonalCharacter_torus (m : ℕ) (i : Fin 4) (u : (K m)ˣ) :
    (diagonalCharacter m i (torusInBorel m u) : K m) =
      SuzukiTorusMovingRank.torusWeights m u i := by
  change (SuzukiTorusGL m u : Matrix (Fin 4) (Fin 4) (K m)) i i = _
  fin_cases i <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, SuzukiTorusMovingRank.torusWeights]

/-- The first n coordinates, as an actual submodule of the natural module. -/
def flag (m n : ℕ) : Submodule (K m) (V m) where
  carrier := {v | ∀ i : Fin 4, n ≤ i.val → v i = 0}
  zero_mem' := by simp
  add_mem' hv hw := by intro i hi; simp [hv i hi, hw i hi]
  smul_mem' c v hv := by intro i hi; simp [hv i hi]

theorem flag_mono (m : ℕ) {n l : ℕ} (h : n ≤ l) : flag m n ≤ flag m l := by
  intro v hv i hi
  exact hv i (h.trans hi)

theorem flag_invariant (m n : ℕ) (g : B m) :
    flag m n ≤ (flag m n).comap (representation m g) := by
  intro v hv i hi
  rw [representation_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < n
  · rw [matrix_upper m g i j (show j < i from Nat.lt_of_lt_of_le hj hi), zero_mul]
  · rw [hv j (by omega), mul_zero]

def layer (m n : ℕ) : Representation (K m) (B m) (flag m n) :=
  (representation m).subrepresentation (flag m n) (flag_invariant m n)

def coordinate (m : ℕ) (i : Fin 4) : flag m (i.val + 1) →ₗ[K m] K m :=
  (LinearMap.proj i).comp (flag m (i.val + 1)).subtype

theorem coordinate_action (m : ℕ) (i : Fin 4) (g : B m)
    (v : flag m (i.val + 1)) :
    coordinate m i (layer m (i.val + 1) g v) =
      weightRepresentation m i g (coordinate m i v) := by
  change representation m g v.val i = matrix m g i i * v.val i
  rw [representation_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [matrix_upper m g i j hj, zero_mul]
    · rw [v.property j (by exact hj), mul_zero]
  · simp

def inclusion (m : ℕ) (i : Fin 4) : flag m i.val →ₗ[K m] flag m (i.val + 1) :=
  Submodule.inclusion (flag_mono m (Nat.le_succ _))

def inclusionMap (m : ℕ) (i : Fin 4) : Rep.of (layer m i.val) ⟶ Rep.of (layer m (i.val + 1)) :=
  Rep.ofHom ⟨inclusion m i, by intro g; ext v; rfl⟩

def coordinateMap (m : ℕ) (i : Fin 4) : Rep.of (layer m (i.val + 1)) ⟶
    Rep.of (weightRepresentation m i) :=
  Rep.ofHom ⟨coordinate m i, by intro g; ext v; exact coordinate_action m i g v⟩

theorem coordinate_surjective (m : ℕ) (i : Fin 4) : Function.Surjective (coordinate m i) := by
  intro a
  refine ⟨⟨Pi.single i a, ?_⟩, by simp [coordinate]⟩
  intro j hj
  have hji : j ≠ i := by intro h; subst j; omega
  simp [hji]

theorem inclusion_range_eq_coordinate_ker (m : ℕ) (i : Fin 4) :
    LinearMap.range (inclusion m i) = LinearMap.ker (coordinate m i) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact u.property i (le_refl _)
  · intro hv
    change v.val i = 0 at hv
    refine ⟨⟨v.val, ?_⟩, rfl⟩
    intro j hj
    by_cases hji : j = i
    · simpa only [hji] using hv
    · exact v.property j (by have := Fin.val_ne_of_ne hji; omega)

def stepComplex (m : ℕ) (i : Fin 4) : ShortComplex (Rep (K m) (B m)) :=
  ShortComplex.mk (inclusionMap m i) (coordinateMap m i) (by
    ext v
    exact v.property i (le_refl _))

theorem stepComplex_shortExact (m : ℕ) (i : Fin 4) : (stepComplex m i).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((stepComplex m i).exact_map_iff_of_faithful
      (forget₂ (Rep (K m) (B m)) (ModuleCat (K m)))).mp
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact inclusion_range_eq_coordinate_ker m i
  · apply (Rep.mono_iff_injective _).mpr
    intro x y h
    change inclusion m i x = inclusion m i y at h
    exact Subtype.ext (congrArg (fun z : flag m (i.val + 1) => z.val) h)
  · exact (Rep.epi_iff_surjective _).mpr (coordinate_surjective m i)

theorem coordinate_ker_invariant (m : ℕ) (i : Fin 4) (g : B m) :
    LinearMap.ker (coordinate m i) ≤
      (LinearMap.ker (coordinate m i)).comap (layer m (i.val + 1) g) := by
  intro v hv
  change coordinate m i (layer m (i.val + 1) g v) = 0
  rw [coordinate_action, show coordinate m i v = 0 from hv, map_zero]

/-- The genuine quotient by the previous layer, expressed through its equal
coordinate kernel, is equivariantly the corresponding scalar weight. -/
def factorEquiv (m : ℕ) (i : Fin 4) :
    ((layer m (i.val + 1)).quotient (LinearMap.ker (coordinate m i))
      (coordinate_ker_invariant m i)).Equiv (weightRepresentation m i) := by
  refine Representation.Equiv.mk
    ((coordinate m i).quotKerEquivOfSurjective (coordinate_surjective m i)) ?_
  intro g
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := (LinearMap.ker (coordinate m i)).mkQ_surjective z
  exact coordinate_action m i g v

theorem flag_zero_subsingleton (m : ℕ) : Subsingleton (flag m 0) := by
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  funext i
  exact (x.property i (Nat.zero_le _)).trans (y.property i (Nat.zero_le _)).symm

/-- The fourth coordinate layer is the whole actual natural module. -/
def topEquiv (m : ℕ) : (layer m 4).Equiv (representation m) := by
  let e : flag m 4 ≃ₗ[K m] V m := LinearEquiv.ofBijective (flag m 4).subtype
    ⟨Subtype.val_injective, fun v => ⟨⟨v, by intro i hi; omega⟩, rfl⟩⟩
  exact Representation.Equiv.mk e (by intro g; ext v; rfl)

/-- Each concrete coordinate step has the actual H1 dimension inequality. -/
theorem finrank_H1_step_le (m : ℕ) (i : Fin 4) :
    Module.finrank (K m) (groupCohomology (Rep.of (layer m (i.val + 1))) 1) ≤
      Module.finrank (K m) (groupCohomology (Rep.of (layer m i.val)) 1) +
        Module.finrank (K m) (groupCohomology (Rep.of (weightRepresentation m i)) 1) := by
  let : FiniteDimensional (K m) (stepComplex m i).X₁ :=
    inferInstanceAs (FiniteDimensional (K m) (flag m i.val))
  let : FiniteDimensional (K m) (stepComplex m i).X₂ :=
    inferInstanceAs (FiniteDimensional (K m) (flag m (i.val + 1)))
  let : FiniteDimensional (K m) (stepComplex m i).X₃ :=
    inferInstanceAs (FiniteDimensional (K m) (K m))
  exact CohomologyH1FiltrationBound.finrank_H1_le_of_shortExact (stepComplex m i)
    (stepComplex_shortExact m i)

end Kourovka2135.SuzukiNaturalBorelFiltration

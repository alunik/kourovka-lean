import Kourovka2135.CohomologyH1FiltrationBound
import Kourovka2135.RepresentationCohomologyAlternative
import Mathlib.LinearAlgebra.Isomorphisms

/-! An upper triangular action on an actual ordered basis gives its complete
invariant flag, scalar quotients, and the sum bound for actual H1. -/

set_option autoImplicit false
noncomputable section
universe u
namespace Kourovka2135.TriangularBasisH1

open CategoryTheory

variable {k G V : Type u} [Field k] [Group G] [AddCommGroup V] [Module k V]
variable {N : ℕ} (ρ : Representation k G V) (b : Module.Basis (Fin N) k V)
variable (hu : ∀ (g : G) (i j : Fin N), j < i → b.repr (ρ g (b j)) i = 0)

def entry (g : G) (i j : Fin N) : k := b.repr (ρ g (b j)) i

theorem apply_coordinate (g : G) (v : V) (i : Fin N) :
    b.repr (ρ g v) i = ∑ j : Fin N, entry ρ b g i j * b.repr v j := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, entry]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

include hu in
theorem diagonal_mul (i : Fin N) (g h : G) :
    entry ρ b (g * h) i i = entry ρ b g i i * entry ρ b h i i := by
  change b.repr (ρ (g * h) (b i)) i = _
  rw [map_mul]
  change b.repr (ρ g (ρ h (b i))) i = _
  rw [apply_coordinate]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [show entry ρ b g i j = 0 from hu g i j hj, zero_mul]
    · rw [hu h j i hj, mul_zero]
  · simp

def diagonalHom (i : Fin N) : G →* k where
  toFun g := entry ρ b g i i
  map_one' := by simp [entry]
  map_mul' := diagonal_mul ρ b hu i

def diagonalCharacter (i : Fin N) : G →* kˣ := (diagonalHom ρ b hu i).toHomUnits

def weightRepresentation (i : Fin N) : Representation k G k where
  toFun g := entry ρ b g i i • LinearMap.id
  map_one' := by apply LinearMap.ext; intro x; simp [entry]
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change entry ρ b (g * h) i i * x = entry ρ b g i i * (entry ρ b h i i * x)
    rw [diagonal_mul ρ b hu, mul_assoc]

@[simp] theorem weightRepresentation_apply (i : Fin N) (g : G) (x : k) :
    weightRepresentation ρ b hu i g x = (diagonalCharacter ρ b hu i g : k) * x := rfl

def flag (n : ℕ) : Submodule k V where
  carrier := {v | ∀ i : Fin N, n ≤ i.val → b.repr v i = 0}
  zero_mem' := by simp
  add_mem' hv hw := by intro i hi; simp [hv i hi, hw i hi]
  smul_mem' c v hv := by intro i hi; simp [hv i hi]

theorem flag_mono {n l : ℕ} (h : n ≤ l) : flag b n ≤ flag b l := by
  intro v hv i hi
  exact hv i (h.trans hi)

include hu in
theorem flag_invariant (n : ℕ) (g : G) : flag b n ≤ (flag b n).comap (ρ g) := by
  intro v hv i hi
  rw [apply_coordinate]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < n
  · rw [show entry ρ b g i j = 0 from hu g i j (Nat.lt_of_lt_of_le hj hi), zero_mul]
  · rw [hv j (by omega), mul_zero]

def layer (n : ℕ) : Representation k G (flag b n) :=
  ρ.subrepresentation (flag b n) (flag_invariant ρ b hu n)

def coordinate (i : Fin N) : flag b (i.val + 1) →ₗ[k] k :=
  (b.coord i).comp (flag b (i.val + 1)).subtype

theorem coordinate_action (i : Fin N) (g : G) (v : flag b (i.val + 1)) :
    coordinate b i (layer ρ b hu (i.val + 1) g v) =
      weightRepresentation ρ b hu i g (coordinate b i v) := by
  change b.repr (ρ g v.val) i = entry ρ b g i i * b.repr v.val i
  rw [apply_coordinate]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [show entry ρ b g i j = 0 from hu g i j hj, zero_mul]
    · rw [v.property j (by exact hj), mul_zero]
  · simp

def inclusion (i : Fin N) : flag b i.val →ₗ[k] flag b (i.val + 1) :=
  Submodule.inclusion (flag_mono b (Nat.le_succ _))

def inclusionMap (i : Fin N) :
    Rep.of (layer ρ b hu i.val) ⟶ Rep.of (layer ρ b hu (i.val + 1)) :=
  Rep.ofHom ⟨inclusion b i, by intro g; ext v; rfl⟩

def coordinateMap (i : Fin N) : Rep.of (layer ρ b hu (i.val + 1)) ⟶
    Rep.of (weightRepresentation ρ b hu i) :=
  Rep.ofHom ⟨coordinate b i, by intro g; ext v; exact coordinate_action ρ b hu i g v⟩

theorem coordinate_surjective (i : Fin N) : Function.Surjective (coordinate b i) := by
  intro a
  refine ⟨⟨a • b i, ?_⟩, by simp [coordinate]⟩
  intro j hj
  have hji : i ≠ j := by intro h; subst j; omega
  simp [hji]

theorem inclusion_range_eq_coordinate_ker (i : Fin N) :
    LinearMap.range (inclusion b i) = LinearMap.ker (coordinate b i) := by
  ext v
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property i (le_refl _)
  · intro hv
    change b.repr v.val i = 0 at hv
    refine ⟨⟨v.val, ?_⟩, rfl⟩
    intro j hj
    by_cases hji : j = i
    · simpa only [hji] using hv
    · exact v.property j (by have := Fin.val_ne_of_ne hji; omega)

def stepComplex (i : Fin N) : ShortComplex (Rep k G) :=
  ShortComplex.mk (inclusionMap ρ b hu i) (coordinateMap ρ b hu i) (by
    ext v
    exact v.property i (le_refl _))

theorem stepComplex_shortExact (i : Fin N) : (stepComplex ρ b hu i).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((stepComplex ρ b hu i).exact_map_iff_of_faithful
      (forget₂ (Rep k G) (ModuleCat k))).mp
    apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact inclusion_range_eq_coordinate_ker b i
  · apply (Rep.mono_iff_injective _).mpr
    intro x y h
    change inclusion b i x = inclusion b i y at h
    exact Subtype.ext (congrArg (fun z : flag b (i.val + 1) => z.val) h)
  · exact (Rep.epi_iff_surjective _).mpr (coordinate_surjective b i)

theorem coordinate_ker_invariant (i : Fin N) (g : G) :
    LinearMap.ker (coordinate b i) ≤
      (LinearMap.ker (coordinate b i)).comap (layer ρ b hu (i.val + 1) g) := by
  intro v hv
  change coordinate b i (layer ρ b hu (i.val + 1) g v) = 0
  rw [coordinate_action, show coordinate b i v = 0 from hv, map_zero]

/-- Each actual consecutive quotient is its scalar diagonal character. -/
def factorEquiv (i : Fin N) :
    ((layer ρ b hu (i.val + 1)).quotient (LinearMap.ker (coordinate b i))
      (coordinate_ker_invariant ρ b hu i)).Equiv (weightRepresentation ρ b hu i) := by
  refine Representation.Equiv.mk
    ((coordinate b i).quotKerEquivOfSurjective (coordinate_surjective b i)) ?_
  intro g
  apply LinearMap.ext
  intro z
  obtain ⟨v, rfl⟩ := (LinearMap.ker (coordinate b i)).mkQ_surjective z
  exact coordinate_action ρ b hu i g v

theorem flag_zero_subsingleton : Subsingleton (flag b 0) := by
  refine ⟨fun x y => ?_⟩
  apply Subtype.ext
  apply b.repr.injective
  ext i
  exact (x.property i (Nat.zero_le _)).trans (y.property i (Nat.zero_le _)).symm

def topEquiv : (layer ρ b hu N).Equiv ρ := by
  let e : flag b N ≃ₗ[k] V := LinearEquiv.ofBijective (flag b N).subtype
    ⟨Subtype.val_injective, fun v => ⟨⟨v, by intro i hi; omega⟩, rfl⟩⟩
  exact Representation.Equiv.mk e (by intro g; ext v; rfl)

theorem zero_layer_H1 :
    Module.finrank k (groupCohomology (Rep.of (layer ρ b hu 0)) 1) = 0 := by
  let : Subsingleton (flag b 0) := flag_zero_subsingleton b
  let : Subsingleton (groupCohomology (Rep.of (layer ρ b hu 0)) 1) :=
    ((ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (groupCohomology.H1π (Rep.of (layer ρ b hu 0))))).subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem finrank_H1_step_le [Finite G] (i : Fin N) :
    Module.finrank k (groupCohomology (Rep.of (layer ρ b hu (i.val + 1))) 1) ≤
      Module.finrank k (groupCohomology (Rep.of (layer ρ b hu i.val)) 1) +
        Module.finrank k (groupCohomology (Rep.of (weightRepresentation ρ b hu i)) 1) := by
  let : FiniteDimensional k V := b.finiteDimensional_of_finite
  let : FiniteDimensional k (stepComplex ρ b hu i).X₁ :=
    inferInstanceAs (FiniteDimensional k (flag b i.val))
  let : FiniteDimensional k (stepComplex ρ b hu i).X₂ :=
    inferInstanceAs (FiniteDimensional k (flag b (i.val + 1)))
  let : FiniteDimensional k (stepComplex ρ b hu i).X₃ :=
    inferInstanceAs (FiniteDimensional k k)
  exact CohomologyH1FiltrationBound.finrank_H1_le_of_shortExact
    (stepComplex ρ b hu i) (stepComplex_shortExact ρ b hu i)

/-- A finite triangular basis bounds H1 by the sum of its scalar H1 dimensions. -/
theorem finrank_H1_le_sum [Finite G] :
    Module.finrank k (groupCohomology (Rep.of ρ) 1) ≤
      ∑ i : Fin N, Module.finrank k
        (groupCohomology (Rep.of (weightRepresentation ρ b hu i)) 1) := by
  classical
  let d : Fin N → ℕ := fun i => Module.finrank k
    (groupCohomology (Rep.of (weightRepresentation ρ b hu i)) 1)
  have h : ∀ n ≤ N, Module.finrank k
      (groupCohomology (Rep.of (layer ρ b hu n)) 1) ≤
        ∑ i : Fin N with i.val < n, d i := by
    intro n
    induction n with
    | zero => intro _; simp [zero_layer_H1]
    | succ n ih =>
      intro hn
      have hp := ih (by omega)
      have hs := finrank_H1_step_le ρ b hu ⟨n, by omega⟩
      have hf : Finset.univ.filter (fun i : Fin N => i.val < n + 1) =
          insert ⟨n, by omega⟩ (Finset.univ.filter (fun i : Fin N => i.val < n)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff]
        omega
      rw [hf, Finset.sum_insert (by simp)]
      change Module.finrank k (groupCohomology (Rep.of (layer ρ b hu (n + 1))) 1) ≤
        Module.finrank k (groupCohomology (Rep.of (layer ρ b hu n)) 1) + d ⟨n, by omega⟩ at hs
      omega
  have hn := h N le_rfl
  rw [RepresentationCohomologyAlternative.finrank_cohomology_eq
    (layer ρ b hu N) ρ (topEquiv ρ b hu) 1] at hn
  simpa [d] using hn

end Kourovka2135.TriangularBasisH1

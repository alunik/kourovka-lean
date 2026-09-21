import Kourovka2135.SuzukiPrincipalSeriesBorel
import Kourovka2135.CoinducedLinearCharacter

/-! Genuine Suzuki principal series and actual embeddings. These are the
coinduced function spaces in mathlib, with left Borel covariance and right
group translation. Evaluation at the identity recovers the inducing
functional, so the intertwiner is nonzero; an irreducible source makes it
injective. No identification of abstract modules is assumed. -/

set_option autoImplicit false
noncomputable section
universe u v

namespace Kourovka2135.SuzukiPrincipalSeries

open SuzukiGeometry SuzukiPrincipalSeriesBorel

variable (m : ℕ) {k : Type u} [Field k] (σ : K m →+* k) (n : ℕ)

abbrev Space := CoinducedLinearCharacter.Space (borel m) (character m σ n)

def representation : Representation k (G m) (Space m σ n) :=
  CoinducedLinearCharacter.induced (borel m) (character m σ n)

@[simp] theorem representation_apply (g : G m) (f : Space m σ n) (h : G m) :
    (representation m σ n g f).val h = f.val (h * g) := rfl

theorem covariance (f : Space m σ n) (b : borel m) (g : G m) :
    f.val ((b : G m) * g) = (character m σ n b : k) * f.val g := f.property b g

instance spaceFiniteDimensional : FiniteDimensional k (Space m σ n) :=
  CoinducedLinearCharacter.spaceFiniteDimensional (borel m) (character m σ n)

variable {V : Type v} [AddCommGroup V] [Module k V]
variable (ρ : Representation k (G m) V) (ell : Module.Dual k V)
variable (hcov : ∀ (b : borel m) (v : V),
  ell (ρ (b : G m) v) = (character m σ n b : k) * ell v)

/-- The concrete coefficient function of the original representation. -/
def embeddingLinear : V →ₗ[k] Space m σ n where
  toFun v := ⟨fun g => ell (ρ g v), by
    intro b g
    change ell (ρ ((b : G m) * g) v) = (character m σ n b : k) * ell (ρ g v)
    rw [map_mul, Module.End.mul_apply, hcov]⟩
  map_add' v w := by
    apply Subtype.ext
    funext g
    change ell (ρ g (v + w)) = ell (ρ g v) + ell (ρ g w)
    simp only [map_add]
  map_smul' c v := by
    apply Subtype.ext
    funext g
    change ell (ρ g (c • v)) = c • ell (ρ g v)
    simp only [map_smul]

@[simp] theorem embeddingLinear_apply (v : V) (g : G m) :
    (embeddingLinear m σ n ρ ell hcov v).val g = ell (ρ g v) := rfl

@[simp] theorem embeddingLinear_one (v : V) :
    (embeddingLinear m σ n ρ ell hcov v).val 1 = ell v := by
  rw [embeddingLinear_apply, map_one]
  rfl

theorem embeddingLinear_action (g : G m) (v : V) :
    embeddingLinear m σ n ρ ell hcov (ρ g v) =
      representation m σ n g (embeddingLinear m σ n ρ ell hcov v) := by
  apply Subtype.ext
  funext h
  change ell (ρ h (ρ g v)) = ell (ρ (h * g) v)
  rw [map_mul]
  rfl

def embedding : ρ.IntertwiningMap (representation m σ n) :=
  (embeddingLinear m σ n ρ ell hcov).intertwiningMap_of_isIntertwiningMap
    ρ (representation m σ n) (embeddingLinear_action m σ n ρ ell hcov)

@[simp] theorem embedding_apply (v : V) (g : G m) :
    (embedding m σ n ρ ell hcov v).val g = ell (ρ g v) := rfl

theorem embedding_ne_zero (hell : ell ≠ 0) : embedding m σ n ρ ell hcov ≠ 0 := by
  intro he
  apply hell
  apply LinearMap.ext
  intro v
  have hv : (embedding m σ n ρ ell hcov v).val 1 = 0 := by rw [he]; rfl
  change ell v = 0
  simpa only [embedding_apply, map_one, Module.End.one_apply] using hv

theorem embedding_injective [ρ.IsIrreducible] (hell : ell ≠ 0) :
    Function.Injective (embedding m σ n ρ ell hcov) :=
  (Representation.IsIrreducible.injective_or_eq_zero (embedding m σ n ρ ell hcov)).resolve_right
    (embedding_ne_zero m σ n ρ ell hcov hell)

/-- Every irreducible binary Suzuki module embeds in one of the actual
principal series with a reduced torus exponent. -/
theorem exists_principal_series_embedding [CharP k 2] [ρ.IsIrreducible] :
    ∃ n : ℕ, n < Nat.card (K m) - 1 ∧
      ∃ j : ρ.IntertwiningMap (representation m σ n), j ≠ 0 ∧ Function.Injective j := by
  let : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra k (G m)) ρ.asModule
  let : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨n, hn, ell, hell, hc⟩ := exists_borel_character m σ ρ
  exact ⟨n, hn, embedding m σ n ρ ell hc,
    embedding_ne_zero m σ n ρ ell hc hell,
    embedding_injective m σ n ρ ell hc hell⟩

end Kourovka2135.SuzukiPrincipalSeries

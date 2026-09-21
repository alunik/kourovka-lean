import Kourovka2135.GeneratingSets
import Kourovka2135.SolubleSupplement

/-!
# Prime-power commutator-closed generators of finite soluble groups

This proves the existence assertion of Alves–Shumyatsky, Lemma 2.1, by a
shorter induction through a normal p-subgroup with a proper supplement.
Prime-power order includes order one (exponent zero).
-/

set_option autoImplicit false
universe u v
namespace Kourovka2135
variable {G : Type u} {H : Type v} [Group G] [Group H]

def HasPrimePowerOrder (x : G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ n : ℕ, orderOf x = p ^ n

theorem HasPrimePowerOrder.one : HasPrimePowerOrder (1 : G) :=
  ⟨2, Nat.prime_two, 0, by simp⟩

theorem HasPrimePowerOrder.map_injective {x : G} (hx : HasPrimePowerOrder x)
    (f : G →* H) (hf : Function.Injective f) : HasPrimePowerOrder (f x) := by
  obtain ⟨p, hp, n, hn⟩ := hx
  exact ⟨p, hp, n, by rw [orderOf_injective f hf x, hn]⟩

/-- Adjoining a normal p-subgroup to a commutator-closed set preserves closure
under commutators. Normality is required only of the adjoined subgroup. -/
theorem IsCommutatorClosed.union_normal {X : Set G} (hX : IsCommutatorClosed X)
    (P : Subgroup G) [P.Normal] : IsCommutatorClosed ((P : Set G) ∪ X) := by
  have left (x y : G) (hx : x ∈ P) : paperCommutator x y ∈ P := by
    have hc := (inferInstance : P.Normal).conj_mem x hx y⁻¹
    simpa only [paperCommutator, inv_inv, mul_assoc] using P.mul_mem (P.inv_mem hx) hc
  have right (x y : G) (hy : y ∈ P) : paperCommutator x y ∈ P := by
    have h := P.inv_mem (left y x hy)
    simpa only [paperCommutator, mul_inv_rev, inv_inv, mul_assoc] using h
  intro x hx y hy
  rcases hx with hx | hx
  · exact Or.inl (left x y hx)
  · rcases hy with hy | hy
    · exact Or.inl (right x y hy)
    · exact Or.inr (hX x hx y hy)

/-- Every finite soluble group has a commutator-closed generating set of
prime-power-order elements. The identity is allowed as a prime-power element. -/
theorem exists_primePower_commutatorClosed_generatingSet
    [Finite G] (hsolv : Group.IsSolvable G) :
    ∃ X : Set G, IsCommutatorClosed X ∧ Subgroup.closure X = ⊤ ∧
      ∀ x ∈ X, HasPrimePowerOrder x := by
  classical
  let T : ℕ → Prop := fun n =>
    ∀ (K : Type u) [Group K] [Finite K], Nat.card K = n → Group.IsSolvable K →
      ∃ X : Set K, IsCommutatorClosed X ∧ Subgroup.closure X = ⊤ ∧
        ∀ x ∈ X, HasPrimePowerOrder x
  have main : ∀ n, T n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih K _ _ hcard hK
    have : Group.IsSolvable K := hK
    rcases subsingleton_or_nontrivial K with htriv | hnontriv
    · letI := htriv
      refine ⟨Set.univ, ?_, by simp, ?_⟩
      · intro x _ y _; trivial
      · intro x _
        rw [Subsingleton.elim x 1]
        exact HasPrimePowerOrder.one
    · letI := hnontriv
      obtain ⟨p, hp, P, M, hPnormal, hP, hM, hsup⟩ :=
        Soluble.exists_normal_pSubgroup_proper_supplement hK
      letI : P.Normal := hPnormal
      letI : Fact p.Prime := ⟨hp⟩
      have hlt : Nat.card M < n := by
        rw [← hcard]
        simpa only [Subgroup.card_top] using
          (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hM))
      obtain ⟨Y, hY, hYgen, hYpow⟩ :=
        ih (Nat.card M) hlt M rfl (by infer_instance)
      let X : Set K := (P : Set K) ∪ (M.subtype '' Y)
      refine ⟨X, (hY.image M.subtype).union_normal P, ?_, ?_⟩
      · change Subgroup.closure ((P : Set K) ∪ M.subtype '' Y) = ⊤
        rw [Subgroup.closure_union, Subgroup.closure_eq,
          ← MonoidHom.map_closure, hYgen, ← MonoidHom.range_eq_map,
          M.range_subtype, hsup]
      · intro x hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨x, hx⟩ : P)
          exact ⟨p, hp, k, by simpa only [Subgroup.orderOf_mk] using hk⟩
        · exact (hYpow y hy).map_injective M.subtype M.subtype_injective
  exact main (Nat.card G) G rfl hsolv

end Kourovka2135

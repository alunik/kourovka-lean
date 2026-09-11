import Kourovka.Problems.P21_68.Proof.Obstruction
import Mathlib.Tactic

namespace Kourovka.P21_68

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem linearCharacterInertia_conj (lam : N →* ℂˣ) (g : G) :
    linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom) =
      (linearCharacterInertia N lam).comap (MulAut.conj g).toMonoidHom := by
  ext a
  change (∀ n, lam (MulAut.conjNormal g (MulAut.conjNormal a n)) =
    lam (MulAut.conjNormal g n)) ↔
    ∀ n, lam (MulAut.conjNormal (MulAut.conj g a) n) = lam n
  have heq (n : N) :
      MulAut.conjNormal (MulAut.conj g a) (MulAut.conjNormal g n) =
        MulAut.conjNormal g (MulAut.conjNormal a n) := by
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  constructor
  · intro h n
    obtain ⟨n, rfl⟩ := (MulAut.conjNormal g).surjective n
    rw [heq]
    exact h n
  · intro h n
    simpa only [heq] using h (MulAut.conjNormal g n)

def subgroupComapEquiv (I : Subgroup G) (e : G ≃* G) :
    I.comap e.toMonoidHom ≃* I where
  toFun x := ⟨e x, x.property⟩
  invFun x := ⟨e.symm x, by simp⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    exact e.map_mul (x : G) (y : G)

/-- Conjugating a normal-subgroup character conjugates its inertia subgroup. -/
noncomputable def weightInertiaEquiv (lam : N →* ℂˣ) (g : G) :
    linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom) ≃*
      linearCharacterInertia N lam :=
  (MulEquiv.subgroupCongr (linearCharacterInertia_conj N lam g)).trans
    (subgroupComapEquiv _ (MulAut.conj g))

@[simp] theorem weightInertiaEquiv_coe (lam : N →* ℂˣ) (g : G)
    (x : linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom)) :
    (weightInertiaEquiv N lam g x : G) = g * (x : G) * g⁻¹ := rfl

theorem weightInertia_index (lam : N →* ℂˣ) (g : G) :
    (linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom)).index =
      (linearCharacterInertia N lam).index := by
  rw [linearCharacterInertia_conj]
  exact Subgroup.index_comap_of_surjective _ (MulAut.conj g).surjective

/-- A quotient of one inertia group transports to every conjugate inertia group;
its kernel remains inside the normal subgroup. -/
theorem exists_conjugate_inertia_projection {H : Type} [Group H]
    (lam : N →* ℂˣ) (q : linearCharacterInertia N lam →* H)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ N.subgroupOf (linearCharacterInertia N lam)) (g : G) :
    ∃ q' : linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom) →* H,
      Function.Surjective q' ∧
      q'.ker ≤ N.subgroupOf
        (linearCharacterInertia N (lam.comp (MulAut.conjNormal g).toMonoidHom)) := by
  let e := weightInertiaEquiv N lam g
  refine ⟨q.comp e.toMonoidHom, hq.comp e.surjective, ?_⟩
  intro x hx
  have he : (e x : G) ∈ N := hker hx
  have hh : g⁻¹ * (e x : G) * g ∈ N := by
    simpa using (inferInstance : N.Normal).conj_mem (e x) he g⁻¹
  change g⁻¹ * (g * (x : G) * g⁻¹) * g ∈ N at hh
  change (x : G) ∈ N
  simpa [mul_assoc] using hh

end Kourovka.P21_68

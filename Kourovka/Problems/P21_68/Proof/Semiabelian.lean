import Kourovka.Problems.P21_68.Statement
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

namespace Kourovka.P21_68

theorem IsSemiabelianStep.congr {H K H' K' : Type}
    [Group H] [Group K] [Group H'] [Group K']
    (h : IsSemiabelianStep H K) (e : H ≃* H') (d : K ≃* K') :
    IsSemiabelianStep H' K' := by
  obtain ⟨A, cA, α, f, hf⟩ := h
  let α' : H' →* MulAut A := α.comp e.symm.toMonoidHom
  let c : A ⋊[α] H ≃* A ⋊[α'] H' :=
    SemidirectProduct.congr (MulEquiv.refl A) e (by intro g; ext a; simp [α'])
  exact ⟨A, cA, α', d.toMonoidHom.comp (f.comp c.symm.toMonoidHom),
    d.surjective.comp (hf.comp c.symm.surjective)⟩

/-- Transport a subgroup chain along an embedding and append one quotient step. -/
theorem IsSemiabelian.append {H K : Type} [Group H] [Group K]
    (h : IsSemiabelian H) (f : H →* K) (hf : Function.Injective f)
    (s : IsSemiabelianStep H K) : IsSemiabelian K := by
  obtain ⟨n, C, h0, hn, hm, hs⟩ := h
  let D : ℕ → Subgroup K := fun i => if i ≤ n then (C i).map f else ⊤
  refine ⟨n + 1, D, ?_, ?_, ?_, ?_⟩
  · simp [D, h0]
  · simp [D]
  · intro i j hij
    dsimp [D]
    split_ifs with hi hj
    · exact Subgroup.map_mono (hm hij)
    · exact le_top
    · omega
    · exact le_rfl
  · intro i hi
    by_cases hin : i < n
    · have hi0 : i ≤ n := by omega
      have hi1 : i + 1 ≤ n := by omega
      exact (hs i hin).congr
        (((C i).equivMapOfInjective f hf).trans
          (MulEquiv.subgroupCongr (by simp [D, hi0])))
        (((C (i + 1)).equivMapOfInjective f hf).trans
          (MulEquiv.subgroupCongr (by simp [D, hi1])))
    · have hin : i = n := by omega
      subst i
      exact s.congr
        ((Subgroup.topEquiv.symm.trans ((⊤ : Subgroup H).equivMapOfInjective f hf)).trans
          (MulEquiv.subgroupCongr (by simp [D, hn])))
        (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr (by simp [D])))

theorem IsSemiabelian.of_subsingleton (G : Type) [Group G] [Subsingleton G] :
    IsSemiabelian G := by
  refine ⟨0, fun _ => ⊤, ?_, rfl, monotone_const, ?_⟩
  · ext g
    simp [Subsingleton.elim g 1]
  · omega

theorem IsSemiabelianStep.of_commGroup (H A : Type) [Group H]
    [CommGroup A] : IsSemiabelianStep H A := by
  let α : H →* MulAut A := 1
  let f : A ⋊[α] H →* A := SemidirectProduct.lift (MonoidHom.id A) 1
    (by intro h; ext a; simp [α])
  refine ⟨A, inferInstance, α, f, ?_⟩
  intro a
  exact ⟨SemidirectProduct.inl a, by simp [f]⟩

theorem IsSemiabelian.of_commGroup (A : Type) [CommGroup A] :
    IsSemiabelian A :=
  (IsSemiabelian.of_subsingleton PUnit).append (1 : PUnit →* A)
    (Function.injective_of_subsingleton _) (IsSemiabelianStep.of_commGroup PUnit A)

/-- An abelian split extension extends the source's actual subgroup chain. -/
theorem IsSemiabelian.semidirect {H A : Type} [Group H] [CommGroup A]
    (h : IsSemiabelian H) (α : H →* MulAut A) : IsSemiabelian (A ⋊[α] H) :=
  h.append SemidirectProduct.inr SemidirectProduct.inr_injective
    ⟨A, inferInstance, α, MonoidHom.id _, Function.surjective_id⟩

end Kourovka.P21_68

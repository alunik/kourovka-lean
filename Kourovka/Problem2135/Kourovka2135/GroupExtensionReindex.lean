import Mathlib.GroupTheory.GroupExtension.Basic

/-! Reindex an actual short exact sequence by actual group isomorphisms. -/

set_option autoImplicit false
namespace Kourovka2135.GroupExtensionReindex

variable {N N' G Q Q' : Type*} [Group N] [Group N'] [Group G] [Group Q] [Group Q']

/-- Transport kernel and quotient without changing the middle group. -/
def reindex (S : GroupExtension N G Q) (a : N' ≃* N) (b : Q ≃* Q') :
    GroupExtension N' G Q' where
  inl := S.inl.comp a.toMonoidHom
  rightHom := b.toMonoidHom.comp S.rightHom
  inl_injective := S.inl_injective.comp a.injective
  rightHom_surjective := b.surjective.comp S.rightHom_surjective
  range_inl_eq_ker_rightHom := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      change b (S.rightHom (S.inl (a n))) = 1
      rw [S.rightHom_inl, map_one]
    · intro hg
      change b (S.rightHom g) = 1 at hg
      have hq : S.rightHom g = 1 := b.injective (by simpa only [map_one] using hg)
      have hm : g ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom]
        exact hq
      obtain ⟨n, hn⟩ := hm
      refine ⟨a.symm n, ?_⟩
      change S.inl (a (a.symm n)) = g
      rw [a.apply_symm_apply, hn]

@[simp] theorem reindex_inl (S : GroupExtension N G Q) (a : N' ≃* N) (b : Q ≃* Q')
    (n : N') : (reindex S a b).inl n = S.inl (a n) := rfl

@[simp] theorem reindex_rightHom (S : GroupExtension N G Q) (a : N' ≃* N) (b : Q ≃* Q')
    (g : G) : (reindex S a b).rightHom g = b (S.rightHom g) := rfl

@[simp] theorem reindex_inl_range (S : GroupExtension N G Q) (a : N' ≃* N) (b : Q ≃* Q') :
    (reindex S a b).inl.range = S.inl.range := by
  ext g
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨a n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨a.symm n, by simpa only [reindex_inl, a.apply_symm_apply] using hn⟩

end Kourovka2135.GroupExtensionReindex

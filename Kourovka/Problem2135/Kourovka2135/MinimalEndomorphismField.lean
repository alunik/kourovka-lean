import Kourovka2135.MinimalIrreducible
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.Algebra.Field.Equiv

/-! The endomorphism ring of the actual finite irreducible module is a field,
using mathlib's Schur lemma and little Wedderburn theorem. -/
set_option autoImplicit false
namespace Kourovka2135
open scoped MonoidAlgebra IsMulCommutative

theorem irreducible_intertwining_endomorphisms_isField
    {S k V : Type*} [Monoid S] [Field k] [AddCommGroup V] [Module k V] [Finite V]
    (ρ : Representation k S V) [ρ.IsIrreducible] :
    IsField (ρ.IntertwiningMap ρ) := by
  classical
  let : Finite ρ.asModule := Finite.of_injective ρ.asModuleEquiv ρ.asModuleEquiv.injective
  let E := Module.End k[S] ρ.asModule
  let : Finite E := Finite.of_injective (fun f : E => (f : ρ.asModule → ρ.asModule))
    DFunLike.coe_injective
  let : Field E := inferInstance
  exact (Representation.IntertwiningMap.equivAlgEnd (ρ := ρ)).toRingEquiv.toMulEquiv.isField
    (Field.toIsField E)

theorem minimal_center_endomorphisms_isField
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hmin : ∀ H : Subgroup G, H.Normal → H < N → H ≤ Subgroup.center G)
    (hnonabelian : ¬ IsMulCommutative N)
    (R : Subgroup G) [R.Normal] (hR : IsPGroup p R)
    [IsElementaryAbelian p (N ⧸ Subgroup.center N)] :
    let σ := minimalCenterRepresentation N hN hmin R hR
    IsField (σ.IntertwiningMap σ) := by
  let σ := minimalCenterRepresentation N hN hmin R hR
  let : σ.IsIrreducible :=
    minimal_quotient_center_representation_irreducible N hmin p hN hnonabelian R hR
  exact irreducible_intertwining_endomorphisms_isField σ

end Kourovka2135

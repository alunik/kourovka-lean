import Kourovka2135.Complement
import Kourovka2135.Vendor.OddOrder.Isaacs.Ch05_Transfer.Main

/-!
# Frobenius' normal p-complement criterion

The licensed Isaacs development supplies Frobenius' theorem.  The public
interface here uses the project's cardinality definition of a normal complement
and the elementwise normalizer-centralization hypothesis.
-/

set_option autoImplicit false

universe u
namespace Kourovka2135

/-- Convert the Sylow-complement formulation to the cardinality formulation. -/
theorem hasNormalPComplement_of_oddOrder
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (h : OddOrder.Isaacs.Ch05.HasNormalPComplement p G) :
    HasNormalPComplement p G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, hN, hcomp⟩ := h
  let P : Sylow p G := default
  refine ⟨N, hN, ?_, ?_⟩
  · exact (hp.coprime_iff_not_dvd.mpr
      (OddOrder.Isaacs.Ch05.not_dvd_card_of_isComplement'_sylow P (hcomp P))).symm
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
    exact ⟨n, (hcomp P).symm.index_eq_card.trans hn⟩

/-- Frobenius' criterion: p'-elements of p-subgroup normalizers act trivially. -/
theorem hasNormalPComplement_of_normalizer_centralization
    {p : ℕ} (hp : p.Prime) {G : Type u} [Group G] [Finite G]
    (h : ∀ P : Subgroup G, IsPGroup p P → ∀ x : G,
      ¬ p ∣ orderOf x → x ∈ Subgroup.normalizer (P : Set G) → ∀ g ∈ P, Commute g x) :
    HasNormalPComplement p G := by
  let : Fact p.Prime := ⟨hp⟩
  apply hasNormalPComplement_of_oddOrder hp
  apply OddOrder.Isaacs.Ch05.hasNormalPComplement_of_prime_subgroups_centralize
  intro q hq hqp P Q hP hQ hQP x hx
  have hxorder : ¬ p ∣ orderOf x := by
    have hcop : (orderOf (⟨x, hx⟩ : Q)).Coprime p :=
      hQ.orderOf_coprime ((Nat.coprime_primes hq.out hp).mpr hqp) ⟨x, hx⟩
    simpa only [Subgroup.orderOf_mk] using hp.coprime_iff_not_dvd.mp hcop.symm
  exact Subgroup.mem_centralizer_iff.mpr (fun g hg => (h P hP x hxorder (hQP hx) g hg).eq)

end Kourovka2135

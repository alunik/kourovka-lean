import Kourovka2135.OddKernelExponent
import Kourovka2135.MinimalFrattiniAbelian

/-!
In a finite perfect group, a minimal noncentral normal odd-p subgroup of the
Frattini subgroup is abelian. The proof uses corrected addition and a functional
stabilizer; it assumes neither an automorphism splitting theorem nor a character theorem.
-/

set_option autoImplicit false
universe u
namespace Kourovka2135
open scoped IsMulCommutative
open ClassTwoAdditive
variable {G : Type u} [Group G] [Finite G] [Group.IsPerfect G]

theorem minimal_noncentral_odd_frattini_isMulCommutative
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)
    (hFrattini : N ≤ frattini G)
    (hnoncentral : ¬ N ≤ Subgroup.center G)
    (hmin : ∀ M : Subgroup G, M.Normal → M < N → M ≤ Subgroup.center G) :
    IsMulCommutative N := by
  classical
  let primeInstance : Fact p.Prime := ⟨hp⟩
  let nilpotentInstance : Group.IsNilpotent N := hN.isNilpotent
  let quotientElementary : IsElementaryAbelian p (N ⧸ Subgroup.center N) :=
    minimal_noncentral_quotient_center_isElementaryAbelian hp N hN hmin
  let derivedElementary : IsElementaryAbelian p (commutator N) :=
    minimal_noncentral_commutator_isElementaryAbelian hp N hN hmin
  have hpow := minimal_noncentral_pow_prime_eq_one hp hodd N hN hnoncentral hmin
  let D : ClassTwoData N := ClassTwoData.ofOddPrime hp hodd
    (minimal_noncentral_commutator_le_internal_center N hmin) (fun c _ => hpow c)
  let additiveModule : Module (ZMod p) (ClassTwoAdditive D) := zmodModule D p hpow
  exact minimal_frattini_isMulCommutative_of_classTwoModule N hFrattini hmin p D

end Kourovka2135

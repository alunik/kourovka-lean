import Kourovka.Problem2153.WilsonModel.ClassTests.ProductReduction
import Kourovka.Problem2153.WilsonModel.ClassTests.Product00
import Kourovka.Problem2153.WilsonModel.ClassTests.Product02
import Kourovka.Problem2153.WilsonModel.ClassTests.Product04
import Kourovka.Problem2153.WilsonModel.ClassTests.Product06
import Kourovka.Problem2153.WilsonModel.ClassTests.Product08
import Kourovka.Problem2153.WilsonModel.ClassTests.Product10
import Kourovka.Problem2153.WilsonModel.ClassTests.Product12
import Kourovka.Problem2153.WilsonModel.ClassTests.Product14
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
namespace Kourovka.Problem2153.WilsonModel.ClassTests
open RootSystem

def productExponent : Fin 7 → Fin 8 → ℕ :=
  ![![1, 2, 2, 2, 2, 4, 4, 5],
    ![2, 2, 2, 2, 2, 4, 4, 7],
    ![2, 2, 2, 2, 2, 4, 4, 13],
    ![2, 2, 2, 2, 2, 4, 4, 7],
    ![2, 2, 2, 2, 2, 4, 4, 13],
    ![2, 2, 2, 2, 2, 4, 4, 7],
    ![2, 2, 2, 2, 2, 4, 4, 13]]

theorem product_power_even (a : Fin 7) (w : Fin 8) :
    classProduct a (evenIndex w) ^ productExponent a w = 1 := by
  fin_cases a <;> fin_cases w
  · exact product_power_0_0
  · exact product_power_0_2
  · exact product_power_0_4
  · exact product_power_0_6
  · exact product_power_0_8
  · exact product_power_0_10
  · exact product_power_0_12
  · exact product_power_0_14
  · exact product_power_1_0
  · exact product_power_1_2
  · exact product_power_1_4
  · exact product_power_1_6
  · exact product_power_1_8
  · exact product_power_1_10
  · exact product_power_1_12
  · exact product_power_1_14
  · exact product_power_2_0
  · exact product_power_2_2
  · exact product_power_2_4
  · exact product_power_2_6
  · exact product_power_2_8
  · exact product_power_2_10
  · exact product_power_2_12
  · exact product_power_2_14
  · exact product_power_3_0
  · exact product_power_3_2
  · exact product_power_3_4
  · exact product_power_3_6
  · exact product_power_3_8
  · exact product_power_3_10
  · exact product_power_3_12
  · exact product_power_3_14
  · exact product_power_4_0
  · exact product_power_4_2
  · exact product_power_4_4
  · exact product_power_4_6
  · exact product_power_4_8
  · exact product_power_4_10
  · exact product_power_4_12
  · exact product_power_4_14
  · exact product_power_5_0
  · exact product_power_5_2
  · exact product_power_5_4
  · exact product_power_5_6
  · exact product_power_5_8
  · exact product_power_5_10
  · exact product_power_5_12
  · exact product_power_5_14
  · exact product_power_6_0
  · exact product_power_6_2
  · exact product_power_6_4
  · exact product_power_6_6
  · exact product_power_6_8
  · exact product_power_6_10
  · exact product_power_6_12
  · exact product_power_6_14

private theorem exponent_not_dvd_three : ∀ a w, ¬ 3 ∣ productExponent a w := by decide +kernel

/-- No product of the fixed central involution with a torus-reduced Weyl conjugate
of a nonidentity central root element has order three. -/
theorem product_order_ne_three (a : Fin 7) (w : Fin 16) :
    orderOf (classProduct a w) ≠ 3 := by
  rw [classProduct_reduce]
  intro h
  have hd := orderOf_dvd_of_pow_eq_one (product_power_even a (halfIndex w))
  rw [h] at hd
  exact exponent_not_dvd_three a (halfIndex w) hd

theorem product_order_not_dvd_three (a : Fin 7) (w : Fin 16) :
    ¬ 3 ∣ orderOf (classProduct a w) := by
  rw [classProduct_reduce]
  intro h
  exact exponent_not_dvd_three a (halfIndex w)
    (h.trans (orderOf_dvd_of_pow_eq_one (product_power_even a (halfIndex w))))

theorem product_torus_weyl_order_ne_three (a c d : Fin 7) (w : Fin 16) :
    orderOf (root 11 1 * rightConj (root 11 a.succ) (torus c d * Weyl.rep w)) ≠ 3 := by
  rw [rightConj_mul, root_conj_torus]
  obtain ⟨b, hb⟩ := Fin.eq_succ_of_ne_zero
    (parameterAction_ne_zero 11 c d (Fin.succ_ne_zero a))
  rw [hb]
  exact product_order_ne_three b w

end Kourovka.Problem2153.WilsonModel.ClassTests

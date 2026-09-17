import Kourovka.Problem2153.WilsonModel.CertificateRows
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel
open Field8 F8
theorem wilsonT_square : wilsonT * wilsonT = 1 := by
  apply Sparse.mul_eq_of_check_alignment wilsonT certRows_wilsonT _ _ certAlignment_wilsonT
  decide +kernel

theorem rho_square : rho * rho = 1 := by
  apply Sparse.mul_eq_of_check_alignment rho certRows_rho _ _ certAlignment_rho
  decide +kernel

theorem sigma_square : sigma * sigma = 1 := by
  apply Sparse.mul_eq_of_check_alignment sigma certRows_sigma _ _ certAlignment_sigma
  decide +kernel

theorem x2_eq : wilsonX * wilsonX = x2 := by
  apply Sparse.mul_eq_of_check_alignment wilsonX certRows_wilsonX _ _ certAlignment_wilsonX
  decide +kernel

theorem x3_eq : x2 * wilsonX = x3 := by
  apply Sparse.mul_eq_of_check_alignment x2 certRows_x2 _ _ certAlignment_x2
  decide +kernel

theorem x_mul_x3 : wilsonX * x3 = 1 := by
  apply Sparse.mul_eq_of_check_alignment wilsonX certRows_wilsonX _ _ certAlignment_wilsonX
  decide +kernel

theorem x3_mul_x : x3 * wilsonX = 1 := by
  apply Sparse.mul_eq_of_check_alignment x3 certRows_x3 _ _ certAlignment_x3
  decide +kernel

theorem sr_eq : sigma * rho = sr := by
  apply Sparse.mul_eq_of_check_alignment sigma certRows_sigma _ _ certAlignment_sigma
  decide +kernel

theorem srs_eq : sr * sigma = srs := by
  apply Sparse.mul_eq_of_check_alignment sr certRows_sr _ _ certAlignment_sr
  decide +kernel

theorem srsr_eq : srs * rho = srsr := by
  apply Sparse.mul_eq_of_check_alignment srs certRows_srs _ _ certAlignment_srs
  decide +kernel

theorem srsrs_eq : srsr * sigma = srsrs := by
  apply Sparse.mul_eq_of_check_alignment srsr certRows_srsr _ _ certAlignment_srsr
  decide +kernel

theorem srsrsr_eq : srsrs * rho = srsrsr := by
  apply Sparse.mul_eq_of_check_alignment srsrs certRows_srsrs _ _ certAlignment_srsrs
  decide +kernel

theorem w_eq : srsrsr * sigma = w := by
  apply Sparse.mul_eq_of_check_alignment srsrsr certRows_srsrsr _ _ certAlignment_srsrsr
  decide +kernel

theorem srs_square : srs * srs = 1 := by
  apply Sparse.mul_eq_of_check_alignment srs certRows_srs _ _ certAlignment_srs
  decide +kernel

theorem w_square : w * w = 1 := by
  apply Sparse.mul_eq_of_check_alignment w certRows_w _ _ certAlignment_w
  decide +kernel

theorem zxLeft_eq : srs * x2 = zxLeft := by
  apply Sparse.mul_eq_of_check_alignment srs certRows_srs _ _ certAlignment_srs
  decide +kernel

theorem witnessX_eq : zxLeft * srs = witnessX := by
  apply Sparse.mul_eq_of_check_alignment zxLeft certRows_zxLeft _ _ certAlignment_zxLeft
  decide +kernel

theorem zyLeft_eq : hInv * witnessX = zyLeft := by
  apply Sparse.mul_eq_of_check_alignment hInv certRows_hInv _ _ certAlignment_hInv
  decide +kernel

theorem witnessY_eq : zyLeft * h = witnessY := by
  apply Sparse.mul_eq_of_check_alignment zyLeft certRows_zyLeft _ _ certAlignment_zyLeft
  decide +kernel

theorem zaLeft_eq : w * witnessX = zaLeft := by
  apply Sparse.mul_eq_of_check_alignment w certRows_w _ _ certAlignment_w
  decide +kernel

theorem witnessA_eq : zaLeft * w = witnessA := by
  apply Sparse.mul_eq_of_check_alignment zaLeft certRows_zaLeft _ _ certAlignment_zaLeft
  decide +kernel

theorem witnessX_square : witnessX * witnessX = 1 := by
  apply Sparse.mul_eq_of_check_alignment witnessX certRows_witnessX _ _ certAlignment_witnessX
  decide +kernel

theorem witnessY_square : witnessY * witnessY = 1 := by
  apply Sparse.mul_eq_of_check_alignment witnessY certRows_witnessY _ _ certAlignment_witnessY
  decide +kernel

theorem witnessA_square : witnessA * witnessA = 1 := by
  apply Sparse.mul_eq_of_check_alignment witnessA certRows_witnessA _ _ certAlignment_witnessA
  decide +kernel

theorem ax_eq : witnessA * witnessX = ax := by
  apply Sparse.mul_eq_of_check_alignment witnessA certRows_witnessA _ _ certAlignment_witnessA
  decide +kernel

theorem ax2_eq : ax * ax = ax2 := by
  apply Sparse.mul_eq_of_check_alignment ax certRows_ax _ _ certAlignment_ax
  decide +kernel

theorem ax4_eq : ax2 * ax2 = ax4 := by
  apply Sparse.mul_eq_of_check_alignment ax2 certRows_ax2 _ _ certAlignment_ax2
  decide +kernel

theorem ax_fifth_step : ax4 * ax = 1 := by
  apply Sparse.mul_eq_of_check_alignment ax4 certRows_ax4 _ _ certAlignment_ax4
  decide +kernel

theorem ay_eq : witnessA * witnessY = ay := by
  apply Sparse.mul_eq_of_check_alignment witnessA certRows_witnessA _ _ certAlignment_witnessA
  decide +kernel

theorem ay2_eq : ay * ay = ay2 := by
  apply Sparse.mul_eq_of_check_alignment ay certRows_ay _ _ certAlignment_ay
  decide +kernel

theorem ay4_eq : ay2 * ay2 = ay4 := by
  apply Sparse.mul_eq_of_check_alignment ay2 certRows_ay2 _ _ certAlignment_ay2
  decide +kernel

theorem ay6_eq : ay4 * ay2 = ay6 := by
  apply Sparse.mul_eq_of_check_alignment ay4 certRows_ay4 _ _ certAlignment_ay4
  decide +kernel

theorem ay_seventh_step : ay6 * ay = 1 := by
  apply Sparse.mul_eq_of_check_alignment ay6 certRows_ay6 _ _ certAlignment_ay6
  decide +kernel

theorem witnessX_ne_one : witnessX ≠ 1 := by decide +kernel

theorem witnessY_ne_one : witnessY ≠ 1 := by decide +kernel

theorem witnessA_ne_one : witnessA ≠ 1 := by decide +kernel

theorem ax_ne_one : ax ≠ 1 := by decide +kernel

theorem ay_ne_one : ay ≠ 1 := by decide +kernel

theorem witnessX_ne_Y : witnessX ≠ witnessY := by decide +kernel

theorem torusDiag_ne_zero : ∀ a b : Fin 7, ∀ i : Fin 26, torusDiag a b i ≠ 0 := by
  decide +kernel

theorem h_eq_diagonal : h = Matrix.diagonal (torusDiag 1 0) := by decide +kernel

theorem hInv_eq_diagonal : hInv = Matrix.diagonal (fun i => (torusDiag 1 0 i)⁻¹) := by
  decide +kernel

end Kourovka.Problem2153.WilsonModel

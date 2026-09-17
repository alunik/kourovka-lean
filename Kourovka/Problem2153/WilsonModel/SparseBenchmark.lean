import Kourovka.Problem2153.WilsonModel.Data
import Kourovka.Problem2153.WilsonModel.Sparse
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel
open Field8 F8
def wilsonTSparse : Sparse.Table (Fin 26) := ![[(0, e1)],
  [(0, e1), (1, e1)],
  [(2, e1)],
  [(3, e1)],
  [(4, e1)],
  [(3, e1), (5, e1)],
  [(4, e1), (6, e1)],
  [(4, e1), (7, e1)],
  [(4, e1), (6, e1), (7, e1), (8, e1)],
  [(9, e1)],
  [(9, e1), (10, e1)],
  [(11, e1)],
  [(11, e1), (12, e1)],
  [(13, e1)],
  [(11, e1), (13, e1), (14, e1)],
  [(15, e1)],
  [(15, e1), (16, e1)],
  [(17, e1)],
  [(17, e1), (18, e1)],
  [(17, e1), (19, e1)],
  [(20, e1)],
  [(17, e1), (18, e1), (19, e1), (21, e1)],
  [(20, e1), (22, e1)],
  [(23, e1)],
  [(24, e1)],
  [(24, e1), (25, e1)]]
theorem wilsonT_alignment : wilsonT = Sparse.eval wilsonTSparse := by decide +kernel
theorem wilsonT_square_sparse : wilsonT * wilsonT = 1 := by
  apply Sparse.mul_eq_of_check_alignment wilsonT wilsonTSparse wilsonT 1 wilsonT_alignment
  decide +kernel

def rhoSparse : Sparse.Table (Fin 26) := ![[(0, e1)],
  [(4, e1)],
  [(3, e1)],
  [(2, e1)],
  [(1, e1)],
  [(11, e1)],
  [(6, e1)],
  [(9, e1)],
  [(17, e1)],
  [(7, e1)],
  [(15, e1)],
  [(5, e1)],
  [(12, e1)],
  [(13, e1)],
  [(20, e1)],
  [(10, e1)],
  [(18, e1)],
  [(8, e1)],
  [(16, e1)],
  [(19, e1)],
  [(14, e1)],
  [(24, e1)],
  [(23, e1)],
  [(22, e1)],
  [(21, e1)],
  [(25, e1)]]
theorem rho_alignment : rho = Sparse.eval rhoSparse := by decide +kernel
theorem rho_square_sparse : rho * rho = 1 := by
  apply Sparse.mul_eq_of_check_alignment rho rhoSparse rho 1 rho_alignment
  decide +kernel

def sigmaSparse : Sparse.Table (Fin 26) := ![[(1, e1)],
  [(0, e1)],
  [(2, e1)],
  [(5, e1)],
  [(8, e1)],
  [(3, e1)],
  [(7, e1)],
  [(6, e1)],
  [(4, e1)],
  [(10, e1)],
  [(9, e1)],
  [(14, e1)],
  [(12, e1), (13, e1)],
  [(13, e1)],
  [(11, e1)],
  [(16, e1)],
  [(15, e1)],
  [(21, e1)],
  [(19, e1)],
  [(18, e1)],
  [(22, e1)],
  [(17, e1)],
  [(20, e1)],
  [(23, e1)],
  [(25, e1)],
  [(24, e1)]]
theorem sigma_alignment : sigma = Sparse.eval sigmaSparse := by decide +kernel
theorem sigma_square_sparse : sigma * sigma = 1 := by
  apply Sparse.mul_eq_of_check_alignment sigma sigmaSparse sigma 1 sigma_alignment
  decide +kernel

end Kourovka.Problem2153.WilsonModel

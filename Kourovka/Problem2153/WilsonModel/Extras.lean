import Kourovka.Problem2153.WilsonModel.Certificates
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel
open Field8 F8
def c3 : Mat :=
  !![e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e1, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e1, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e1, e0, e1, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e1, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e1, e0, e1, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1]

def c3Squared : Mat :=
  !![e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e1, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e1, e0, e1, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e1, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e1, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e1, e0, e1, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e1, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0, e0, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0, e0;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e1;
    e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e0, e1, e0]

theorem c3_eq : wilsonT * sigma = c3 := by decide +kernel
theorem c3Squared_eq : c3 * c3 = c3Squared := by decide +kernel
theorem c3_cubed_step : c3Squared * c3 = 1 := by decide +kernel
theorem c3_ne_one : c3 ≠ 1 := by decide +kernel
end Kourovka.Problem2153.WilsonModel

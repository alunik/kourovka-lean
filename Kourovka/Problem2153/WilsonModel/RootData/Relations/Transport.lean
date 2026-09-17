import Kourovka.Problem2153.WilsonModel.RootData.Relations.Structured
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.WilsonModel.RootData.Relations

abbrev Transport (n : ℕ) := Fin n × (Fin 7 × Fin 7)

private def commPair_0_1 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (0, (0, 0)), some (0, (5, 5)), some (0, (6, 6)), some (0, (1, 1)), some (0, (2, 2)), some (0, (3, 3)), some (0, (4, 4))],
    ![none, some (0, (4, 6)), some (0, (2, 3)), some (0, (5, 2)), some (0, (0, 4)), some (0, (3, 1)), some (0, (1, 0)), some (0, (6, 5))],
    ![none, some (0, (5, 1)), some (0, (1, 6)), some (0, (3, 4)), some (0, (6, 3)), some (0, (0, 5)), some (0, (4, 2)), some (0, (2, 0))],
    ![none, some (0, (6, 2)), some (0, (3, 0)), some (0, (2, 1)), some (0, (4, 5)), some (0, (1, 4)), some (0, (0, 6)), some (0, (5, 3))],
    ![none, some (0, (1, 3)), some (0, (6, 4)), some (0, (4, 0)), some (0, (3, 2)), some (0, (5, 6)), some (0, (2, 5)), some (0, (0, 1))],
    ![none, some (0, (2, 4)), some (0, (0, 2)), some (0, (1, 5)), some (0, (5, 0)), some (0, (4, 3)), some (0, (6, 1)), some (0, (3, 6))],
    ![none, some (0, (3, 5)), some (0, (4, 1)), some (0, (0, 3)), some (0, (2, 6)), some (0, (6, 0)), some (0, (5, 4)), some (0, (1, 2))]]
private def commPair_0_2 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (1, (0, 0)), some (1, (5, 5)), some (1, (6, 6)), some (1, (1, 1)), some (1, (2, 2)), some (1, (3, 3)), some (1, (4, 4))],
    ![none, some (1, (3, 1)), some (1, (4, 6)), some (1, (0, 4)), some (1, (2, 3)), some (1, (6, 5)), some (1, (5, 2)), some (1, (1, 0))],
    ![none, some (1, (4, 2)), some (1, (2, 0)), some (1, (5, 1)), some (1, (0, 5)), some (1, (3, 4)), some (1, (1, 6)), some (1, (6, 3))],
    ![none, some (1, (5, 3)), some (1, (1, 4)), some (1, (3, 0)), some (1, (6, 2)), some (1, (0, 6)), some (1, (4, 5)), some (1, (2, 1))],
    ![none, some (1, (6, 4)), some (1, (3, 2)), some (1, (2, 5)), some (1, (4, 0)), some (1, (1, 3)), some (1, (0, 1)), some (1, (5, 6))],
    ![none, some (1, (1, 5)), some (1, (6, 1)), some (1, (4, 3)), some (1, (3, 6)), some (1, (5, 0)), some (1, (2, 4)), some (1, (0, 2))],
    ![none, some (1, (2, 6)), some (1, (0, 3)), some (1, (1, 2)), some (1, (5, 4)), some (1, (4, 1)), some (1, (6, 0)), some (1, (3, 5))]]
private def commPair_0_3 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (2, (0, 0)), some (2, (6, 6)), some (2, (1, 1)), some (2, (2, 2)), some (2, (3, 3)), some (2, (4, 4)), some (2, (5, 5))],
    ![none, some (2, (4, 6)), some (2, (5, 2)), some (2, (0, 4)), some (2, (3, 1)), some (2, (1, 0)), some (2, (6, 5)), some (2, (2, 3))],
    ![none, some (2, (5, 1)), some (2, (3, 4)), some (2, (6, 3)), some (2, (0, 5)), some (2, (4, 2)), some (2, (2, 0)), some (2, (1, 6))],
    ![none, some (2, (6, 2)), some (2, (2, 1)), some (2, (4, 5)), some (2, (1, 4)), some (2, (0, 6)), some (2, (5, 3)), some (2, (3, 0))],
    ![none, some (2, (1, 3)), some (2, (4, 0)), some (2, (3, 2)), some (2, (5, 6)), some (2, (2, 5)), some (2, (0, 1)), some (2, (6, 4))],
    ![none, some (2, (2, 4)), some (2, (1, 5)), some (2, (5, 0)), some (2, (4, 3)), some (2, (6, 1)), some (2, (3, 6)), some (2, (0, 2))],
    ![none, some (2, (3, 5)), some (2, (0, 3)), some (2, (2, 6)), some (2, (6, 0)), some (2, (5, 4)), some (2, (1, 2)), some (2, (4, 1))]]
private def commPair_0_4 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (3, (0, 0)), some (3, (6, 6)), some (3, (1, 1)), some (3, (2, 2)), some (3, (3, 3)), some (3, (4, 4)), some (3, (5, 5))],
    ![none, some (3, (1, 0)), some (3, (4, 6)), some (3, (3, 1)), some (3, (5, 2)), some (3, (2, 3)), some (3, (0, 4)), some (3, (6, 5))],
    ![none, some (3, (2, 0)), some (3, (1, 6)), some (3, (5, 1)), some (3, (4, 2)), some (3, (6, 3)), some (3, (3, 4)), some (3, (0, 5))],
    ![none, some (3, (3, 0)), some (3, (0, 6)), some (3, (2, 1)), some (3, (6, 2)), some (3, (5, 3)), some (3, (1, 4)), some (3, (4, 5))],
    ![none, some (3, (4, 0)), some (3, (5, 6)), some (3, (0, 1)), some (3, (3, 2)), some (3, (1, 3)), some (3, (6, 4)), some (3, (2, 5))],
    ![none, some (3, (5, 0)), some (3, (3, 6)), some (3, (6, 1)), some (3, (0, 2)), some (3, (4, 3)), some (3, (2, 4)), some (3, (1, 5))],
    ![none, some (3, (6, 0)), some (3, (2, 6)), some (3, (4, 1)), some (3, (1, 2)), some (3, (0, 3)), some (3, (5, 4)), some (3, (3, 5))]]
private def commPair_0_5 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (4, (0, 0)), some (4, (2, 2)), some (4, (3, 3)), some (4, (4, 4)), some (4, (5, 5)), some (4, (6, 6)), some (4, (1, 1))],
    ![none, some (4, (2, 3)), some (4, (4, 6)), some (4, (6, 5)), some (4, (3, 1)), some (4, (0, 4)), some (4, (1, 0)), some (4, (5, 2))],
    ![none, some (4, (3, 4)), some (4, (6, 3)), some (4, (5, 1)), some (4, (1, 6)), some (4, (4, 2)), some (4, (0, 5)), some (4, (2, 0))],
    ![none, some (4, (4, 5)), some (4, (3, 0)), some (4, (1, 4)), some (4, (6, 2)), some (4, (2, 1)), some (4, (5, 3)), some (4, (0, 6))],
    ![none, some (4, (5, 6)), some (4, (0, 1)), some (4, (4, 0)), some (4, (2, 5)), some (4, (1, 3)), some (4, (3, 2)), some (4, (6, 4))],
    ![none, some (4, (6, 1)), some (4, (1, 5)), some (4, (0, 2)), some (4, (5, 0)), some (4, (3, 6)), some (4, (2, 4)), some (4, (4, 3))],
    ![none, some (4, (1, 2)), some (4, (5, 4)), some (4, (2, 6)), some (4, (0, 3)), some (4, (6, 0)), some (4, (4, 1)), some (4, (3, 5))]]
private def commPair_0_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (5, (0, 0)), some (5, (6, 6)), some (5, (1, 1)), some (5, (2, 2)), some (5, (3, 3)), some (5, (4, 4)), some (5, (5, 5))],
    ![none, some (5, (0, 4)), some (5, (6, 5)), some (5, (1, 0)), some (5, (2, 3)), some (5, (3, 1)), some (5, (4, 6)), some (5, (5, 2))],
    ![none, some (5, (0, 5)), some (5, (6, 3)), some (5, (1, 6)), some (5, (2, 0)), some (5, (3, 4)), some (5, (4, 2)), some (5, (5, 1))],
    ![none, some (5, (0, 6)), some (5, (6, 2)), some (5, (1, 4)), some (5, (2, 1)), some (5, (3, 0)), some (5, (4, 5)), some (5, (5, 3))],
    ![none, some (5, (0, 1)), some (5, (6, 4)), some (5, (1, 3)), some (5, (2, 5)), some (5, (3, 2)), some (5, (4, 0)), some (5, (5, 6))],
    ![none, some (5, (0, 2)), some (5, (6, 1)), some (5, (1, 5)), some (5, (2, 4)), some (5, (3, 6)), some (5, (4, 3)), some (5, (5, 0))],
    ![none, some (5, (0, 3)), some (5, (6, 0)), some (5, (1, 2)), some (5, (2, 6)), some (5, (3, 5)), some (5, (4, 1)), some (5, (5, 4))]]
private def commPair_0_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (6, (0, 0)), some (6, (6, 6)), some (6, (1, 1)), some (6, (2, 2)), some (6, (3, 3)), some (6, (4, 4)), some (6, (5, 5))],
    ![none, some (6, (3, 1)), some (6, (0, 4)), some (6, (2, 3)), some (6, (6, 5)), some (6, (5, 2)), some (6, (1, 0)), some (6, (4, 6))],
    ![none, some (6, (4, 2)), some (6, (5, 1)), some (6, (0, 5)), some (6, (3, 4)), some (6, (1, 6)), some (6, (6, 3)), some (6, (2, 0))],
    ![none, some (6, (5, 3)), some (6, (3, 0)), some (6, (6, 2)), some (6, (0, 6)), some (6, (4, 5)), some (6, (2, 1)), some (6, (1, 4))],
    ![none, some (6, (6, 4)), some (6, (2, 5)), some (6, (4, 0)), some (6, (1, 3)), some (6, (0, 1)), some (6, (5, 6)), some (6, (3, 2))],
    ![none, some (6, (1, 5)), some (6, (4, 3)), some (6, (3, 6)), some (6, (5, 0)), some (6, (2, 4)), some (6, (0, 2)), some (6, (6, 1))],
    ![none, some (6, (2, 6)), some (6, (1, 2)), some (6, (5, 4)), some (6, (4, 1)), some (6, (6, 0)), some (6, (3, 5)), some (6, (0, 3))]]
private def commPair_0_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (7, (0, 0)), some (7, (2, 2)), some (7, (3, 3)), some (7, (4, 4)), some (7, (5, 5)), some (7, (6, 6)), some (7, (1, 1))],
    ![none, some (7, (6, 5)), some (7, (1, 0)), some (7, (0, 4)), some (7, (5, 2)), some (7, (3, 1)), some (7, (2, 3)), some (7, (4, 6))],
    ![none, some (7, (1, 6)), some (7, (5, 1)), some (7, (2, 0)), some (7, (0, 5)), some (7, (6, 3)), some (7, (4, 2)), some (7, (3, 4))],
    ![none, some (7, (2, 1)), some (7, (4, 5)), some (7, (6, 2)), some (7, (3, 0)), some (7, (0, 6)), some (7, (1, 4)), some (7, (5, 3))],
    ![none, some (7, (3, 2)), some (7, (6, 4)), some (7, (5, 6)), some (7, (1, 3)), some (7, (4, 0)), some (7, (0, 1)), some (7, (2, 5))],
    ![none, some (7, (4, 3)), some (7, (3, 6)), some (7, (1, 5)), some (7, (6, 1)), some (7, (2, 4)), some (7, (5, 0)), some (7, (0, 2))],
    ![none, some (7, (5, 4)), some (7, (0, 3)), some (7, (4, 1)), some (7, (2, 6)), some (7, (1, 2)), some (7, (3, 5)), some (7, (6, 0))]]
private def commPair_0_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (8, (0, 0)), some (8, (4, 4)), some (8, (5, 5)), some (8, (6, 6)), some (8, (1, 1)), some (8, (2, 2)), some (8, (3, 3))],
    ![none, some (8, (5, 2)), some (8, (2, 3)), some (8, (1, 0)), some (8, (3, 1)), some (8, (6, 5)), some (8, (0, 4)), some (8, (4, 6))],
    ![none, some (8, (6, 3)), some (8, (5, 1)), some (8, (3, 4)), some (8, (2, 0)), some (8, (4, 2)), some (8, (1, 6)), some (8, (0, 5))],
    ![none, some (8, (1, 4)), some (8, (0, 6)), some (8, (6, 2)), some (8, (4, 5)), some (8, (3, 0)), some (8, (5, 3)), some (8, (2, 1))],
    ![none, some (8, (2, 5)), some (8, (3, 2)), some (8, (0, 1)), some (8, (1, 3)), some (8, (5, 6)), some (8, (4, 0)), some (8, (6, 4))],
    ![none, some (8, (3, 6)), some (8, (1, 5)), some (8, (4, 3)), some (8, (0, 2)), some (8, (2, 4)), some (8, (6, 1)), some (8, (5, 0))],
    ![none, some (8, (4, 1)), some (8, (6, 0)), some (8, (2, 6)), some (8, (5, 4)), some (8, (0, 3)), some (8, (3, 5)), some (8, (1, 2))]]
private def commPair_0_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (9, (0, 0)), some (9, (1, 1)), some (9, (2, 2)), some (9, (3, 3)), some (9, (4, 4)), some (9, (5, 5)), some (9, (6, 6))],
    ![none, some (9, (1, 0)), some (9, (3, 1)), some (9, (5, 2)), some (9, (2, 3)), some (9, (0, 4)), some (9, (6, 5)), some (9, (4, 6))],
    ![none, some (9, (2, 0)), some (9, (5, 1)), some (9, (4, 2)), some (9, (6, 3)), some (9, (3, 4)), some (9, (0, 5)), some (9, (1, 6))],
    ![none, some (9, (3, 0)), some (9, (2, 1)), some (9, (6, 2)), some (9, (5, 3)), some (9, (1, 4)), some (9, (4, 5)), some (9, (0, 6))],
    ![none, some (9, (4, 0)), some (9, (0, 1)), some (9, (3, 2)), some (9, (1, 3)), some (9, (6, 4)), some (9, (2, 5)), some (9, (5, 6))],
    ![none, some (9, (5, 0)), some (9, (6, 1)), some (9, (0, 2)), some (9, (4, 3)), some (9, (2, 4)), some (9, (1, 5)), some (9, (3, 6))],
    ![none, some (9, (6, 0)), some (9, (4, 1)), some (9, (1, 2)), some (9, (0, 3)), some (9, (5, 4)), some (9, (3, 5)), some (9, (2, 6))]]
private def commPair_0_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (10, (0, 0)), some (10, (1, 1)), some (10, (2, 2)), some (10, (3, 3)), some (10, (4, 4)), some (10, (5, 5)), some (10, (6, 6))],
    ![none, some (10, (0, 4)), some (10, (1, 0)), some (10, (2, 3)), some (10, (3, 1)), some (10, (4, 6)), some (10, (5, 2)), some (10, (6, 5))],
    ![none, some (10, (0, 5)), some (10, (1, 6)), some (10, (2, 0)), some (10, (3, 4)), some (10, (4, 2)), some (10, (5, 1)), some (10, (6, 3))],
    ![none, some (10, (0, 6)), some (10, (1, 4)), some (10, (2, 1)), some (10, (3, 0)), some (10, (4, 5)), some (10, (5, 3)), some (10, (6, 2))],
    ![none, some (10, (0, 1)), some (10, (1, 3)), some (10, (2, 5)), some (10, (3, 2)), some (10, (4, 0)), some (10, (5, 6)), some (10, (6, 4))],
    ![none, some (10, (0, 2)), some (10, (1, 5)), some (10, (2, 4)), some (10, (3, 6)), some (10, (4, 3)), some (10, (5, 0)), some (10, (6, 1))],
    ![none, some (10, (0, 3)), some (10, (1, 2)), some (10, (2, 6)), some (10, (3, 5)), some (10, (4, 1)), some (10, (5, 4)), some (10, (6, 0))]]
private def commPair_1_2 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (11, (0, 0)), some (11, (4, 6)), some (11, (5, 1)), some (11, (6, 2)), some (11, (1, 3)), some (11, (2, 4)), some (11, (3, 5))],
    ![none, some (11, (6, 4)), some (11, (5, 5)), some (11, (3, 0)), some (11, (2, 3)), some (11, (4, 1)), some (11, (1, 6)), some (11, (0, 2))],
    ![none, some (11, (1, 5)), some (11, (0, 3)), some (11, (6, 6)), some (11, (4, 0)), some (11, (3, 4)), some (11, (5, 2)), some (11, (2, 1))],
    ![none, some (11, (2, 6)), some (11, (3, 2)), some (11, (0, 4)), some (11, (1, 1)), some (11, (5, 0)), some (11, (4, 5)), some (11, (6, 3))],
    ![none, some (11, (3, 1)), some (11, (1, 4)), some (11, (4, 3)), some (11, (0, 5)), some (11, (2, 2)), some (11, (6, 0)), some (11, (5, 6))],
    ![none, some (11, (4, 2)), some (11, (6, 1)), some (11, (2, 5)), some (11, (5, 4)), some (11, (0, 6)), some (11, (3, 3)), some (11, (1, 0))],
    ![none, some (11, (5, 3)), some (11, (2, 0)), some (11, (1, 2)), some (11, (3, 6)), some (11, (6, 5)), some (11, (0, 1)), some (11, (4, 4))]]
private def commPair_1_3 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (12, (0, 0)), some (13, (0, 0)), some (14, (0, 0)), some (15, (0, 0)), some (16, (0, 0)), some (17, (0, 0)), some (18, (0, 0))],
    ![none, some (15, (0, 2)), some (14, (0, 2)), some (18, (0, 2)), some (17, (0, 2)), some (13, (0, 2)), some (16, (0, 2)), some (12, (0, 2))],
    ![none, some (16, (0, 3)), some (12, (0, 3)), some (15, (0, 3)), some (13, (0, 3)), some (18, (0, 3)), some (14, (0, 3)), some (17, (0, 3))],
    ![none, some (17, (0, 4)), some (18, (0, 4)), some (12, (0, 4)), some (16, (0, 4)), some (14, (0, 4)), some (13, (0, 4)), some (15, (0, 4))],
    ![none, some (18, (0, 5)), some (16, (0, 5)), some (13, (0, 5)), some (12, (0, 5)), some (17, (0, 5)), some (15, (0, 5)), some (14, (0, 5))],
    ![none, some (13, (0, 6)), some (15, (0, 6)), some (17, (0, 6)), some (14, (0, 6)), some (12, (0, 6)), some (18, (0, 6)), some (16, (0, 6))],
    ![none, some (14, (0, 1)), some (17, (0, 1)), some (16, (0, 1)), some (18, (0, 1)), some (15, (0, 1)), some (12, (0, 1)), some (13, (0, 1))]]
private def commPair_1_4 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (19, (0, 0)), some (19, (4, 6)), some (19, (5, 1)), some (19, (6, 2)), some (19, (1, 3)), some (19, (2, 4)), some (19, (3, 5))],
    ![none, some (19, (3, 0)), some (19, (1, 6)), some (19, (4, 1)), some (19, (0, 2)), some (19, (2, 3)), some (19, (6, 4)), some (19, (5, 5))],
    ![none, some (19, (4, 0)), some (19, (6, 6)), some (19, (2, 1)), some (19, (5, 2)), some (19, (0, 3)), some (19, (3, 4)), some (19, (1, 5))],
    ![none, some (19, (5, 0)), some (19, (2, 6)), some (19, (1, 1)), some (19, (3, 2)), some (19, (6, 3)), some (19, (0, 4)), some (19, (4, 5))],
    ![none, some (19, (6, 0)), some (19, (5, 6)), some (19, (3, 1)), some (19, (2, 2)), some (19, (4, 3)), some (19, (1, 4)), some (19, (0, 5))],
    ![none, some (19, (1, 0)), some (19, (0, 6)), some (19, (6, 1)), some (19, (4, 2)), some (19, (3, 3)), some (19, (5, 4)), some (19, (2, 5))],
    ![none, some (19, (2, 0)), some (19, (3, 6)), some (19, (0, 1)), some (19, (1, 2)), some (19, (5, 3)), some (19, (4, 4)), some (19, (6, 5))]]
private def commPair_1_5 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (20, (0, 0)), some (20, (4, 6)), some (20, (5, 1)), some (20, (6, 2)), some (20, (1, 3)), some (20, (2, 4)), some (20, (3, 5))],
    ![none, some (20, (2, 3)), some (20, (3, 0)), some (20, (0, 2)), some (20, (1, 6)), some (20, (5, 5)), some (20, (4, 1)), some (20, (6, 4))],
    ![none, some (20, (3, 4)), some (20, (1, 5)), some (20, (4, 0)), some (20, (0, 3)), some (20, (2, 1)), some (20, (6, 6)), some (20, (5, 2))],
    ![none, some (20, (4, 5)), some (20, (6, 3)), some (20, (2, 6)), some (20, (5, 0)), some (20, (0, 4)), some (20, (3, 2)), some (20, (1, 1))],
    ![none, some (20, (5, 6)), some (20, (2, 2)), some (20, (1, 4)), some (20, (3, 1)), some (20, (6, 0)), some (20, (0, 5)), some (20, (4, 3))],
    ![none, some (20, (6, 1)), some (20, (5, 4)), some (20, (3, 3)), some (20, (2, 5)), some (20, (4, 2)), some (20, (1, 0)), some (20, (0, 6))],
    ![none, some (20, (1, 2)), some (20, (0, 1)), some (20, (6, 5)), some (20, (4, 4)), some (20, (3, 6)), some (20, (5, 3)), some (20, (2, 0))]]
private def commPair_1_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (21, (0, 0)), some (21, (6, 2)), some (21, (1, 3)), some (21, (2, 4)), some (21, (3, 5)), some (21, (4, 6)), some (21, (5, 1))],
    ![none, some (21, (0, 2)), some (21, (6, 4)), some (21, (1, 6)), some (21, (2, 3)), some (21, (3, 0)), some (21, (4, 1)), some (21, (5, 5))],
    ![none, some (21, (0, 3)), some (21, (6, 6)), some (21, (1, 5)), some (21, (2, 1)), some (21, (3, 4)), some (21, (4, 0)), some (21, (5, 2))],
    ![none, some (21, (0, 4)), some (21, (6, 3)), some (21, (1, 1)), some (21, (2, 6)), some (21, (3, 2)), some (21, (4, 5)), some (21, (5, 0))],
    ![none, some (21, (0, 5)), some (21, (6, 0)), some (21, (1, 4)), some (21, (2, 2)), some (21, (3, 1)), some (21, (4, 3)), some (21, (5, 6))],
    ![none, some (21, (0, 6)), some (21, (6, 1)), some (21, (1, 0)), some (21, (2, 5)), some (21, (3, 3)), some (21, (4, 2)), some (21, (5, 4))],
    ![none, some (21, (0, 1)), some (21, (6, 5)), some (21, (1, 2)), some (21, (2, 0)), some (21, (3, 6)), some (21, (4, 4)), some (21, (5, 3))]]
private def commPair_1_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (22, (0, 0)), some (22, (5, 1)), some (22, (6, 2)), some (22, (1, 3)), some (22, (2, 4)), some (22, (3, 5)), some (22, (4, 6))],
    ![none, some (22, (6, 4)), some (22, (3, 0)), some (22, (2, 3)), some (22, (4, 1)), some (22, (1, 6)), some (22, (0, 2)), some (22, (5, 5))],
    ![none, some (22, (1, 5)), some (22, (6, 6)), some (22, (4, 0)), some (22, (3, 4)), some (22, (5, 2)), some (22, (2, 1)), some (22, (0, 3))],
    ![none, some (22, (2, 6)), some (22, (0, 4)), some (22, (1, 1)), some (22, (5, 0)), some (22, (4, 5)), some (22, (6, 3)), some (22, (3, 2))],
    ![none, some (22, (3, 1)), some (22, (4, 3)), some (22, (0, 5)), some (22, (2, 2)), some (22, (6, 0)), some (22, (5, 6)), some (22, (1, 4))],
    ![none, some (22, (4, 2)), some (22, (2, 5)), some (22, (5, 4)), some (22, (0, 6)), some (22, (3, 3)), some (22, (1, 0)), some (22, (6, 1))],
    ![none, some (22, (5, 3)), some (22, (1, 2)), some (22, (3, 6)), some (22, (6, 5)), some (22, (0, 1)), some (22, (4, 4)), some (22, (2, 0))]]
private def commPair_1_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (23, (0, 0)), some (23, (5, 1)), some (23, (6, 2)), some (23, (1, 3)), some (23, (2, 4)), some (23, (3, 5)), some (23, (4, 6))],
    ![none, some (23, (1, 6)), some (23, (6, 4)), some (23, (4, 1)), some (23, (3, 0)), some (23, (5, 5)), some (23, (2, 3)), some (23, (0, 2))],
    ![none, some (23, (2, 1)), some (23, (0, 3)), some (23, (1, 5)), some (23, (5, 2)), some (23, (4, 0)), some (23, (6, 6)), some (23, (3, 4))],
    ![none, some (23, (3, 2)), some (23, (4, 5)), some (23, (0, 4)), some (23, (2, 6)), some (23, (6, 3)), some (23, (5, 0)), some (23, (1, 1))],
    ![none, some (23, (4, 3)), some (23, (2, 2)), some (23, (5, 6)), some (23, (0, 5)), some (23, (3, 1)), some (23, (1, 4)), some (23, (6, 0))],
    ![none, some (23, (5, 4)), some (23, (1, 0)), some (23, (3, 3)), some (23, (6, 1)), some (23, (0, 6)), some (23, (4, 2)), some (23, (2, 5))],
    ![none, some (23, (6, 5)), some (23, (3, 6)), some (23, (2, 0)), some (23, (4, 4)), some (23, (1, 2)), some (23, (0, 1)), some (23, (5, 3))]]
private def commPair_1_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (24, (0, 0)), some (24, (5, 1)), some (24, (6, 2)), some (24, (1, 3)), some (24, (2, 4)), some (24, (3, 5)), some (24, (4, 6))],
    ![none, some (24, (4, 1)), some (24, (2, 3)), some (24, (5, 5)), some (24, (0, 2)), some (24, (3, 0)), some (24, (1, 6)), some (24, (6, 4))],
    ![none, some (24, (5, 2)), some (24, (1, 5)), some (24, (3, 4)), some (24, (6, 6)), some (24, (0, 3)), some (24, (4, 0)), some (24, (2, 1))],
    ![none, some (24, (6, 3)), some (24, (3, 2)), some (24, (2, 6)), some (24, (4, 5)), some (24, (1, 1)), some (24, (0, 4)), some (24, (5, 0))],
    ![none, some (24, (1, 4)), some (24, (6, 0)), some (24, (4, 3)), some (24, (3, 1)), some (24, (5, 6)), some (24, (2, 2)), some (24, (0, 5))],
    ![none, some (24, (2, 5)), some (24, (0, 6)), some (24, (1, 0)), some (24, (5, 4)), some (24, (4, 2)), some (24, (6, 1)), some (24, (3, 3))],
    ![none, some (24, (3, 6)), some (24, (4, 4)), some (24, (0, 1)), some (24, (2, 0)), some (24, (6, 5)), some (24, (5, 3)), some (24, (1, 2))]]
private def commPair_1_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (25, (0, 0)), some (25, (5, 1)), some (25, (6, 2)), some (25, (1, 3)), some (25, (2, 4)), some (25, (3, 5)), some (25, (4, 6))],
    ![none, some (25, (3, 0)), some (25, (4, 1)), some (25, (0, 2)), some (25, (2, 3)), some (25, (6, 4)), some (25, (5, 5)), some (25, (1, 6))],
    ![none, some (25, (4, 0)), some (25, (2, 1)), some (25, (5, 2)), some (25, (0, 3)), some (25, (3, 4)), some (25, (1, 5)), some (25, (6, 6))],
    ![none, some (25, (5, 0)), some (25, (1, 1)), some (25, (3, 2)), some (25, (6, 3)), some (25, (0, 4)), some (25, (4, 5)), some (25, (2, 6))],
    ![none, some (25, (6, 0)), some (25, (3, 1)), some (25, (2, 2)), some (25, (4, 3)), some (25, (1, 4)), some (25, (0, 5)), some (25, (5, 6))],
    ![none, some (25, (1, 0)), some (25, (6, 1)), some (25, (4, 2)), some (25, (3, 3)), some (25, (5, 4)), some (25, (2, 5)), some (25, (0, 6))],
    ![none, some (25, (2, 0)), some (25, (0, 1)), some (25, (1, 2)), some (25, (5, 3)), some (25, (4, 4)), some (25, (6, 5)), some (25, (3, 6))]]
private def commPair_1_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (26, (0, 0)), some (26, (1, 3)), some (26, (2, 4)), some (26, (3, 5)), some (26, (4, 6)), some (26, (5, 1)), some (26, (6, 2))],
    ![none, some (26, (0, 2)), some (26, (1, 6)), some (26, (2, 3)), some (26, (3, 0)), some (26, (4, 1)), some (26, (5, 5)), some (26, (6, 4))],
    ![none, some (26, (0, 3)), some (26, (1, 5)), some (26, (2, 1)), some (26, (3, 4)), some (26, (4, 0)), some (26, (5, 2)), some (26, (6, 6))],
    ![none, some (26, (0, 4)), some (26, (1, 1)), some (26, (2, 6)), some (26, (3, 2)), some (26, (4, 5)), some (26, (5, 0)), some (26, (6, 3))],
    ![none, some (26, (0, 5)), some (26, (1, 4)), some (26, (2, 2)), some (26, (3, 1)), some (26, (4, 3)), some (26, (5, 6)), some (26, (6, 0))],
    ![none, some (26, (0, 6)), some (26, (1, 0)), some (26, (2, 5)), some (26, (3, 3)), some (26, (4, 2)), some (26, (5, 4)), some (26, (6, 1))],
    ![none, some (26, (0, 1)), some (26, (1, 2)), some (26, (2, 0)), some (26, (3, 6)), some (26, (4, 4)), some (26, (5, 3)), some (26, (6, 5))]]
private def commPair_2_3 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (27, (0, 0)), some (27, (1, 5)), some (27, (2, 6)), some (27, (3, 1)), some (27, (4, 2)), some (27, (5, 3)), some (27, (6, 4))],
    ![none, some (27, (4, 6)), some (27, (0, 3)), some (27, (3, 2)), some (27, (1, 4)), some (27, (6, 1)), some (27, (2, 0)), some (27, (5, 5))],
    ![none, some (27, (5, 1)), some (27, (6, 6)), some (27, (0, 4)), some (27, (4, 3)), some (27, (2, 5)), some (27, (1, 2)), some (27, (3, 0))],
    ![none, some (27, (6, 2)), some (27, (4, 0)), some (27, (1, 1)), some (27, (0, 5)), some (27, (5, 4)), some (27, (3, 6)), some (27, (2, 3))],
    ![none, some (27, (1, 3)), some (27, (3, 4)), some (27, (5, 0)), some (27, (2, 2)), some (27, (0, 6)), some (27, (6, 5)), some (27, (4, 1))],
    ![none, some (27, (2, 4)), some (27, (5, 2)), some (27, (4, 5)), some (27, (6, 0)), some (27, (3, 3)), some (27, (0, 1)), some (27, (1, 6))],
    ![none, some (27, (3, 5)), some (27, (2, 1)), some (27, (6, 3)), some (27, (5, 6)), some (27, (1, 0)), some (27, (4, 4)), some (27, (0, 2))]]
private def commPair_2_4 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (28, (0, 0)), some (28, (2, 6)), some (28, (3, 1)), some (28, (4, 2)), some (28, (5, 3)), some (28, (6, 4)), some (28, (1, 5))],
    ![none, some (28, (2, 0)), some (28, (4, 6)), some (28, (6, 1)), some (28, (3, 2)), some (28, (0, 3)), some (28, (1, 4)), some (28, (5, 5))],
    ![none, some (28, (3, 0)), some (28, (6, 6)), some (28, (5, 1)), some (28, (1, 2)), some (28, (4, 3)), some (28, (0, 4)), some (28, (2, 5))],
    ![none, some (28, (4, 0)), some (28, (3, 6)), some (28, (1, 1)), some (28, (6, 2)), some (28, (2, 3)), some (28, (5, 4)), some (28, (0, 5))],
    ![none, some (28, (5, 0)), some (28, (0, 6)), some (28, (4, 1)), some (28, (2, 2)), some (28, (1, 3)), some (28, (3, 4)), some (28, (6, 5))],
    ![none, some (28, (6, 0)), some (28, (1, 6)), some (28, (0, 1)), some (28, (5, 2)), some (28, (3, 3)), some (28, (2, 4)), some (28, (4, 5))],
    ![none, some (28, (1, 0)), some (28, (5, 6)), some (28, (2, 1)), some (28, (0, 2)), some (28, (6, 3)), some (28, (4, 4)), some (28, (3, 5))]]
private def commPair_2_5 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (29, (0, 0)), some (29, (1, 5)), some (29, (2, 6)), some (29, (3, 1)), some (29, (4, 2)), some (29, (5, 3)), some (29, (6, 4))],
    ![none, some (29, (6, 1)), some (29, (4, 6)), some (29, (1, 4)), some (29, (0, 3)), some (29, (5, 5)), some (29, (3, 2)), some (29, (2, 0))],
    ![none, some (29, (1, 2)), some (29, (3, 0)), some (29, (5, 1)), some (29, (2, 5)), some (29, (0, 4)), some (29, (6, 6)), some (29, (4, 3))],
    ![none, some (29, (2, 3)), some (29, (5, 4)), some (29, (4, 0)), some (29, (6, 2)), some (29, (3, 6)), some (29, (0, 5)), some (29, (1, 1))],
    ![none, some (29, (3, 4)), some (29, (2, 2)), some (29, (6, 5)), some (29, (5, 0)), some (29, (1, 3)), some (29, (4, 1)), some (29, (0, 6))],
    ![none, some (29, (4, 5)), some (29, (0, 1)), some (29, (3, 3)), some (29, (1, 6)), some (29, (6, 0)), some (29, (2, 4)), some (29, (5, 2))],
    ![none, some (29, (5, 6)), some (29, (6, 3)), some (29, (0, 2)), some (29, (4, 4)), some (29, (2, 1)), some (29, (1, 0)), some (29, (3, 5))]]
private def commPair_2_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (30, (0, 0)), some (30, (6, 4)), some (30, (1, 5)), some (30, (2, 6)), some (30, (3, 1)), some (30, (4, 2)), some (30, (5, 3))],
    ![none, some (30, (0, 3)), some (30, (6, 1)), some (30, (1, 4)), some (30, (2, 0)), some (30, (3, 2)), some (30, (4, 6)), some (30, (5, 5))],
    ![none, some (30, (0, 4)), some (30, (6, 6)), some (30, (1, 2)), some (30, (2, 5)), some (30, (3, 0)), some (30, (4, 3)), some (30, (5, 1))],
    ![none, some (30, (0, 5)), some (30, (6, 2)), some (30, (1, 1)), some (30, (2, 3)), some (30, (3, 6)), some (30, (4, 0)), some (30, (5, 4))],
    ![none, some (30, (0, 6)), some (30, (6, 5)), some (30, (1, 3)), some (30, (2, 2)), some (30, (3, 4)), some (30, (4, 1)), some (30, (5, 0))],
    ![none, some (30, (0, 1)), some (30, (6, 0)), some (30, (1, 6)), some (30, (2, 4)), some (30, (3, 3)), some (30, (4, 5)), some (30, (5, 2))],
    ![none, some (30, (0, 2)), some (30, (6, 3)), some (30, (1, 0)), some (30, (2, 1)), some (30, (3, 5)), some (30, (4, 4)), some (30, (5, 6))]]
private def commPair_2_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (31, (0, 0)), some (32, (0, 0)), some (33, (0, 0)), some (34, (0, 0)), some (35, (0, 0)), some (36, (0, 0)), some (37, (0, 0))],
    ![none, some (34, (0, 3)), some (33, (0, 3)), some (37, (0, 3)), some (36, (0, 3)), some (32, (0, 3)), some (35, (0, 3)), some (31, (0, 3))],
    ![none, some (35, (0, 4)), some (31, (0, 4)), some (34, (0, 4)), some (32, (0, 4)), some (37, (0, 4)), some (33, (0, 4)), some (36, (0, 4))],
    ![none, some (36, (0, 5)), some (37, (0, 5)), some (31, (0, 5)), some (35, (0, 5)), some (33, (0, 5)), some (32, (0, 5)), some (34, (0, 5))],
    ![none, some (37, (0, 6)), some (35, (0, 6)), some (32, (0, 6)), some (31, (0, 6)), some (36, (0, 6)), some (34, (0, 6)), some (33, (0, 6))],
    ![none, some (32, (0, 1)), some (34, (0, 1)), some (36, (0, 1)), some (33, (0, 1)), some (31, (0, 1)), some (37, (0, 1)), some (35, (0, 1))],
    ![none, some (33, (0, 2)), some (36, (0, 2)), some (35, (0, 2)), some (37, (0, 2)), some (34, (0, 2)), some (31, (0, 2)), some (32, (0, 2))]]
private def commPair_2_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (38, (0, 0)), some (38, (6, 4)), some (38, (1, 5)), some (38, (2, 6)), some (38, (3, 1)), some (38, (4, 2)), some (38, (5, 3))],
    ![none, some (38, (3, 2)), some (38, (0, 3)), some (38, (2, 0)), some (38, (6, 1)), some (38, (5, 5)), some (38, (1, 4)), some (38, (4, 6))],
    ![none, some (38, (4, 3)), some (38, (5, 1)), some (38, (0, 4)), some (38, (3, 0)), some (38, (1, 2)), some (38, (6, 6)), some (38, (2, 5))],
    ![none, some (38, (5, 4)), some (38, (3, 6)), some (38, (6, 2)), some (38, (0, 5)), some (38, (4, 0)), some (38, (2, 3)), some (38, (1, 1))],
    ![none, some (38, (6, 5)), some (38, (2, 2)), some (38, (4, 1)), some (38, (1, 3)), some (38, (0, 6)), some (38, (5, 0)), some (38, (3, 4))],
    ![none, some (38, (1, 6)), some (38, (4, 5)), some (38, (3, 3)), some (38, (5, 2)), some (38, (2, 4)), some (38, (0, 1)), some (38, (6, 0))],
    ![none, some (38, (2, 1)), some (38, (1, 0)), some (38, (5, 6)), some (38, (4, 4)), some (38, (6, 3)), some (38, (3, 5)), some (38, (0, 2))]]
private def commPair_2_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (39, (0, 0)), some (39, (1, 5)), some (39, (2, 6)), some (39, (3, 1)), some (39, (4, 2)), some (39, (5, 3)), some (39, (6, 4))],
    ![none, some (39, (1, 4)), some (39, (3, 2)), some (39, (5, 5)), some (39, (2, 0)), some (39, (0, 3)), some (39, (6, 1)), some (39, (4, 6))],
    ![none, some (39, (2, 5)), some (39, (5, 1)), some (39, (4, 3)), some (39, (6, 6)), some (39, (3, 0)), some (39, (0, 4)), some (39, (1, 2))],
    ![none, some (39, (3, 6)), some (39, (2, 3)), some (39, (6, 2)), some (39, (5, 4)), some (39, (1, 1)), some (39, (4, 0)), some (39, (0, 5))],
    ![none, some (39, (4, 1)), some (39, (0, 6)), some (39, (3, 4)), some (39, (1, 3)), some (39, (6, 5)), some (39, (2, 2)), some (39, (5, 0))],
    ![none, some (39, (5, 2)), some (39, (6, 0)), some (39, (0, 1)), some (39, (4, 5)), some (39, (2, 4)), some (39, (1, 6)), some (39, (3, 3))],
    ![none, some (39, (6, 3)), some (39, (4, 4)), some (39, (1, 0)), some (39, (0, 2)), some (39, (5, 6)), some (39, (3, 5)), some (39, (2, 1))]]
private def commPair_2_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (40, (0, 0)), some (40, (3, 1)), some (40, (4, 2)), some (40, (5, 3)), some (40, (6, 4)), some (40, (1, 5)), some (40, (2, 6))],
    ![none, some (40, (2, 0)), some (40, (6, 1)), some (40, (3, 2)), some (40, (0, 3)), some (40, (1, 4)), some (40, (5, 5)), some (40, (4, 6))],
    ![none, some (40, (3, 0)), some (40, (5, 1)), some (40, (1, 2)), some (40, (4, 3)), some (40, (0, 4)), some (40, (2, 5)), some (40, (6, 6))],
    ![none, some (40, (4, 0)), some (40, (1, 1)), some (40, (6, 2)), some (40, (2, 3)), some (40, (5, 4)), some (40, (0, 5)), some (40, (3, 6))],
    ![none, some (40, (5, 0)), some (40, (4, 1)), some (40, (2, 2)), some (40, (1, 3)), some (40, (3, 4)), some (40, (6, 5)), some (40, (0, 6))],
    ![none, some (40, (6, 0)), some (40, (0, 1)), some (40, (5, 2)), some (40, (3, 3)), some (40, (2, 4)), some (40, (4, 5)), some (40, (1, 6))],
    ![none, some (40, (1, 0)), some (40, (2, 1)), some (40, (0, 2)), some (40, (6, 3)), some (40, (4, 4)), some (40, (3, 5)), some (40, (5, 6))]]
private def commPair_2_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (41, (0, 0)), some (41, (1, 5)), some (41, (2, 6)), some (41, (3, 1)), some (41, (4, 2)), some (41, (5, 3)), some (41, (6, 4))],
    ![none, some (41, (0, 3)), some (41, (1, 4)), some (41, (2, 0)), some (41, (3, 2)), some (41, (4, 6)), some (41, (5, 5)), some (41, (6, 1))],
    ![none, some (41, (0, 4)), some (41, (1, 2)), some (41, (2, 5)), some (41, (3, 0)), some (41, (4, 3)), some (41, (5, 1)), some (41, (6, 6))],
    ![none, some (41, (0, 5)), some (41, (1, 1)), some (41, (2, 3)), some (41, (3, 6)), some (41, (4, 0)), some (41, (5, 4)), some (41, (6, 2))],
    ![none, some (41, (0, 6)), some (41, (1, 3)), some (41, (2, 2)), some (41, (3, 4)), some (41, (4, 1)), some (41, (5, 0)), some (41, (6, 5))],
    ![none, some (41, (0, 1)), some (41, (1, 6)), some (41, (2, 4)), some (41, (3, 3)), some (41, (4, 5)), some (41, (5, 2)), some (41, (6, 0))],
    ![none, some (41, (0, 2)), some (41, (1, 0)), some (41, (2, 1)), some (41, (3, 5)), some (41, (4, 4)), some (41, (5, 6)), some (41, (6, 3))]]
private def commPair_3_4 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (42, (0, 0)), some (42, (4, 6)), some (42, (5, 1)), some (42, (6, 2)), some (42, (1, 3)), some (42, (2, 4)), some (42, (3, 5))],
    ![none, some (42, (4, 0)), some (42, (6, 6)), some (42, (2, 1)), some (42, (5, 2)), some (42, (0, 3)), some (42, (3, 4)), some (42, (1, 5))],
    ![none, some (42, (5, 0)), some (42, (2, 6)), some (42, (1, 1)), some (42, (3, 2)), some (42, (6, 3)), some (42, (0, 4)), some (42, (4, 5))],
    ![none, some (42, (6, 0)), some (42, (5, 6)), some (42, (3, 1)), some (42, (2, 2)), some (42, (4, 3)), some (42, (1, 4)), some (42, (0, 5))],
    ![none, some (42, (1, 0)), some (42, (0, 6)), some (42, (6, 1)), some (42, (4, 2)), some (42, (3, 3)), some (42, (5, 4)), some (42, (2, 5))],
    ![none, some (42, (2, 0)), some (42, (3, 6)), some (42, (0, 1)), some (42, (1, 2)), some (42, (5, 3)), some (42, (4, 4)), some (42, (6, 5))],
    ![none, some (42, (3, 0)), some (42, (1, 6)), some (42, (4, 1)), some (42, (0, 2)), some (42, (2, 3)), some (42, (6, 4)), some (42, (5, 5))]]
private def commPair_3_5 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (43, (0, 0)), some (43, (4, 6)), some (43, (5, 1)), some (43, (6, 2)), some (43, (1, 3)), some (43, (2, 4)), some (43, (3, 5))],
    ![none, some (43, (3, 4)), some (43, (1, 5)), some (43, (4, 0)), some (43, (0, 3)), some (43, (2, 1)), some (43, (6, 6)), some (43, (5, 2))],
    ![none, some (43, (4, 5)), some (43, (6, 3)), some (43, (2, 6)), some (43, (5, 0)), some (43, (0, 4)), some (43, (3, 2)), some (43, (1, 1))],
    ![none, some (43, (5, 6)), some (43, (2, 2)), some (43, (1, 4)), some (43, (3, 1)), some (43, (6, 0)), some (43, (0, 5)), some (43, (4, 3))],
    ![none, some (43, (6, 1)), some (43, (5, 4)), some (43, (3, 3)), some (43, (2, 5)), some (43, (4, 2)), some (43, (1, 0)), some (43, (0, 6))],
    ![none, some (43, (1, 2)), some (43, (0, 1)), some (43, (6, 5)), some (43, (4, 4)), some (43, (3, 6)), some (43, (5, 3)), some (43, (2, 0))],
    ![none, some (43, (2, 3)), some (43, (3, 0)), some (43, (0, 2)), some (43, (1, 6)), some (43, (5, 5)), some (43, (4, 1)), some (43, (6, 4))]]
private def commPair_3_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (44, (0, 0)), some (44, (6, 2)), some (44, (1, 3)), some (44, (2, 4)), some (44, (3, 5)), some (44, (4, 6)), some (44, (5, 1))],
    ![none, some (44, (0, 3)), some (44, (6, 6)), some (44, (1, 5)), some (44, (2, 1)), some (44, (3, 4)), some (44, (4, 0)), some (44, (5, 2))],
    ![none, some (44, (0, 4)), some (44, (6, 3)), some (44, (1, 1)), some (44, (2, 6)), some (44, (3, 2)), some (44, (4, 5)), some (44, (5, 0))],
    ![none, some (44, (0, 5)), some (44, (6, 0)), some (44, (1, 4)), some (44, (2, 2)), some (44, (3, 1)), some (44, (4, 3)), some (44, (5, 6))],
    ![none, some (44, (0, 6)), some (44, (6, 1)), some (44, (1, 0)), some (44, (2, 5)), some (44, (3, 3)), some (44, (4, 2)), some (44, (5, 4))],
    ![none, some (44, (0, 1)), some (44, (6, 5)), some (44, (1, 2)), some (44, (2, 0)), some (44, (3, 6)), some (44, (4, 4)), some (44, (5, 3))],
    ![none, some (44, (0, 2)), some (44, (6, 4)), some (44, (1, 6)), some (44, (2, 3)), some (44, (3, 0)), some (44, (4, 1)), some (44, (5, 5))]]
private def commPair_3_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (45, (0, 0)), some (45, (5, 1)), some (45, (6, 2)), some (45, (1, 3)), some (45, (2, 4)), some (45, (3, 5)), some (45, (4, 6))],
    ![none, some (45, (1, 5)), some (45, (6, 6)), some (45, (4, 0)), some (45, (3, 4)), some (45, (5, 2)), some (45, (2, 1)), some (45, (0, 3))],
    ![none, some (45, (2, 6)), some (45, (0, 4)), some (45, (1, 1)), some (45, (5, 0)), some (45, (4, 5)), some (45, (6, 3)), some (45, (3, 2))],
    ![none, some (45, (3, 1)), some (45, (4, 3)), some (45, (0, 5)), some (45, (2, 2)), some (45, (6, 0)), some (45, (5, 6)), some (45, (1, 4))],
    ![none, some (45, (4, 2)), some (45, (2, 5)), some (45, (5, 4)), some (45, (0, 6)), some (45, (3, 3)), some (45, (1, 0)), some (45, (6, 1))],
    ![none, some (45, (5, 3)), some (45, (1, 2)), some (45, (3, 6)), some (45, (6, 5)), some (45, (0, 1)), some (45, (4, 4)), some (45, (2, 0))],
    ![none, some (45, (6, 4)), some (45, (3, 0)), some (45, (2, 3)), some (45, (4, 1)), some (45, (1, 6)), some (45, (0, 2)), some (45, (5, 5))]]
private def commPair_3_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (46, (0, 0)), some (46, (5, 1)), some (46, (6, 2)), some (46, (1, 3)), some (46, (2, 4)), some (46, (3, 5)), some (46, (4, 6))],
    ![none, some (46, (2, 1)), some (46, (0, 3)), some (46, (1, 5)), some (46, (5, 2)), some (46, (4, 0)), some (46, (6, 6)), some (46, (3, 4))],
    ![none, some (46, (3, 2)), some (46, (4, 5)), some (46, (0, 4)), some (46, (2, 6)), some (46, (6, 3)), some (46, (5, 0)), some (46, (1, 1))],
    ![none, some (46, (4, 3)), some (46, (2, 2)), some (46, (5, 6)), some (46, (0, 5)), some (46, (3, 1)), some (46, (1, 4)), some (46, (6, 0))],
    ![none, some (46, (5, 4)), some (46, (1, 0)), some (46, (3, 3)), some (46, (6, 1)), some (46, (0, 6)), some (46, (4, 2)), some (46, (2, 5))],
    ![none, some (46, (6, 5)), some (46, (3, 6)), some (46, (2, 0)), some (46, (4, 4)), some (46, (1, 2)), some (46, (0, 1)), some (46, (5, 3))],
    ![none, some (46, (1, 6)), some (46, (6, 4)), some (46, (4, 1)), some (46, (3, 0)), some (46, (5, 5)), some (46, (2, 3)), some (46, (0, 2))]]
private def commPair_3_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (47, (0, 0)), some (47, (5, 1)), some (47, (6, 2)), some (47, (1, 3)), some (47, (2, 4)), some (47, (3, 5)), some (47, (4, 6))],
    ![none, some (47, (5, 2)), some (47, (1, 5)), some (47, (3, 4)), some (47, (6, 6)), some (47, (0, 3)), some (47, (4, 0)), some (47, (2, 1))],
    ![none, some (47, (6, 3)), some (47, (3, 2)), some (47, (2, 6)), some (47, (4, 5)), some (47, (1, 1)), some (47, (0, 4)), some (47, (5, 0))],
    ![none, some (47, (1, 4)), some (47, (6, 0)), some (47, (4, 3)), some (47, (3, 1)), some (47, (5, 6)), some (47, (2, 2)), some (47, (0, 5))],
    ![none, some (47, (2, 5)), some (47, (0, 6)), some (47, (1, 0)), some (47, (5, 4)), some (47, (4, 2)), some (47, (6, 1)), some (47, (3, 3))],
    ![none, some (47, (3, 6)), some (47, (4, 4)), some (47, (0, 1)), some (47, (2, 0)), some (47, (6, 5)), some (47, (5, 3)), some (47, (1, 2))],
    ![none, some (47, (4, 1)), some (47, (2, 3)), some (47, (5, 5)), some (47, (0, 2)), some (47, (3, 0)), some (47, (1, 6)), some (47, (6, 4))]]
private def commPair_3_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (48, (0, 0)), some (48, (5, 1)), some (48, (6, 2)), some (48, (1, 3)), some (48, (2, 4)), some (48, (3, 5)), some (48, (4, 6))],
    ![none, some (48, (4, 0)), some (48, (2, 1)), some (48, (5, 2)), some (48, (0, 3)), some (48, (3, 4)), some (48, (1, 5)), some (48, (6, 6))],
    ![none, some (48, (5, 0)), some (48, (1, 1)), some (48, (3, 2)), some (48, (6, 3)), some (48, (0, 4)), some (48, (4, 5)), some (48, (2, 6))],
    ![none, some (48, (6, 0)), some (48, (3, 1)), some (48, (2, 2)), some (48, (4, 3)), some (48, (1, 4)), some (48, (0, 5)), some (48, (5, 6))],
    ![none, some (48, (1, 0)), some (48, (6, 1)), some (48, (4, 2)), some (48, (3, 3)), some (48, (5, 4)), some (48, (2, 5)), some (48, (0, 6))],
    ![none, some (48, (2, 0)), some (48, (0, 1)), some (48, (1, 2)), some (48, (5, 3)), some (48, (4, 4)), some (48, (6, 5)), some (48, (3, 6))],
    ![none, some (48, (3, 0)), some (48, (4, 1)), some (48, (0, 2)), some (48, (2, 3)), some (48, (6, 4)), some (48, (5, 5)), some (48, (1, 6))]]
private def commPair_3_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (49, (0, 0)), some (49, (1, 3)), some (49, (2, 4)), some (49, (3, 5)), some (49, (4, 6)), some (49, (5, 1)), some (49, (6, 2))],
    ![none, some (49, (0, 3)), some (49, (1, 5)), some (49, (2, 1)), some (49, (3, 4)), some (49, (4, 0)), some (49, (5, 2)), some (49, (6, 6))],
    ![none, some (49, (0, 4)), some (49, (1, 1)), some (49, (2, 6)), some (49, (3, 2)), some (49, (4, 5)), some (49, (5, 0)), some (49, (6, 3))],
    ![none, some (49, (0, 5)), some (49, (1, 4)), some (49, (2, 2)), some (49, (3, 1)), some (49, (4, 3)), some (49, (5, 6)), some (49, (6, 0))],
    ![none, some (49, (0, 6)), some (49, (1, 0)), some (49, (2, 5)), some (49, (3, 3)), some (49, (4, 2)), some (49, (5, 4)), some (49, (6, 1))],
    ![none, some (49, (0, 1)), some (49, (1, 2)), some (49, (2, 0)), some (49, (3, 6)), some (49, (4, 4)), some (49, (5, 3)), some (49, (6, 5))],
    ![none, some (49, (0, 2)), some (49, (1, 6)), some (49, (2, 3)), some (49, (3, 0)), some (49, (4, 1)), some (49, (5, 5)), some (49, (6, 4))]]
private def commPair_4_5 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (50, (0, 0)), some (50, (3, 0)), some (50, (4, 0)), some (50, (5, 0)), some (50, (6, 0)), some (50, (1, 0)), some (50, (2, 0))],
    ![none, some (50, (5, 6)), some (50, (4, 6)), some (50, (2, 6)), some (50, (1, 6)), some (50, (3, 6)), some (50, (6, 6)), some (50, (0, 6))],
    ![none, some (50, (6, 1)), some (50, (0, 1)), some (50, (5, 1)), some (50, (3, 1)), some (50, (2, 1)), some (50, (4, 1)), some (50, (1, 1))],
    ![none, some (50, (1, 2)), some (50, (2, 2)), some (50, (0, 2)), some (50, (6, 2)), some (50, (4, 2)), some (50, (3, 2)), some (50, (5, 2))],
    ![none, some (50, (2, 3)), some (50, (6, 3)), some (50, (3, 3)), some (50, (0, 3)), some (50, (1, 3)), some (50, (5, 3)), some (50, (4, 3))],
    ![none, some (50, (3, 4)), some (50, (5, 4)), some (50, (1, 4)), some (50, (4, 4)), some (50, (0, 4)), some (50, (2, 4)), some (50, (6, 4))],
    ![none, some (50, (4, 5)), some (50, (1, 5)), some (50, (6, 5)), some (50, (2, 5)), some (50, (5, 5)), some (50, (0, 5)), some (50, (3, 5))]]
private def commPair_4_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (51, (0, 0)), some (51, (6, 0)), some (51, (1, 0)), some (51, (2, 0)), some (51, (3, 0)), some (51, (4, 0)), some (51, (5, 0))],
    ![none, some (51, (0, 6)), some (51, (6, 6)), some (51, (1, 6)), some (51, (2, 6)), some (51, (3, 6)), some (51, (4, 6)), some (51, (5, 6))],
    ![none, some (51, (0, 1)), some (51, (6, 1)), some (51, (1, 1)), some (51, (2, 1)), some (51, (3, 1)), some (51, (4, 1)), some (51, (5, 1))],
    ![none, some (51, (0, 2)), some (51, (6, 2)), some (51, (1, 2)), some (51, (2, 2)), some (51, (3, 2)), some (51, (4, 2)), some (51, (5, 2))],
    ![none, some (51, (0, 3)), some (51, (6, 3)), some (51, (1, 3)), some (51, (2, 3)), some (51, (3, 3)), some (51, (4, 3)), some (51, (5, 3))],
    ![none, some (51, (0, 4)), some (51, (6, 4)), some (51, (1, 4)), some (51, (2, 4)), some (51, (3, 4)), some (51, (4, 4)), some (51, (5, 4))],
    ![none, some (51, (0, 5)), some (51, (6, 5)), some (51, (1, 5)), some (51, (2, 5)), some (51, (3, 5)), some (51, (4, 5)), some (51, (5, 5))]]
private def commPair_4_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (52, (0, 0)), some (52, (3, 0)), some (52, (4, 0)), some (52, (5, 0)), some (52, (6, 0)), some (52, (1, 0)), some (52, (2, 0))],
    ![none, some (52, (2, 6)), some (52, (6, 6)), some (52, (3, 6)), some (52, (0, 6)), some (52, (1, 6)), some (52, (5, 6)), some (52, (4, 6))],
    ![none, some (52, (3, 1)), some (52, (5, 1)), some (52, (1, 1)), some (52, (4, 1)), some (52, (0, 1)), some (52, (2, 1)), some (52, (6, 1))],
    ![none, some (52, (4, 2)), some (52, (1, 2)), some (52, (6, 2)), some (52, (2, 2)), some (52, (5, 2)), some (52, (0, 2)), some (52, (3, 2))],
    ![none, some (52, (5, 3)), some (52, (4, 3)), some (52, (2, 3)), some (52, (1, 3)), some (52, (3, 3)), some (52, (6, 3)), some (52, (0, 3))],
    ![none, some (52, (6, 4)), some (52, (0, 4)), some (52, (5, 4)), some (52, (3, 4)), some (52, (2, 4)), some (52, (4, 4)), some (52, (1, 4))],
    ![none, some (52, (1, 5)), some (52, (2, 5)), some (52, (0, 5)), some (52, (6, 5)), some (52, (4, 5)), some (52, (3, 5)), some (52, (5, 5))]]
private def commPair_4_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (53, (0, 0)), some (53, (1, 0)), some (53, (2, 0)), some (53, (3, 0)), some (53, (4, 0)), some (53, (5, 0)), some (53, (6, 0))],
    ![none, some (53, (1, 6)), some (53, (3, 6)), some (53, (5, 6)), some (53, (2, 6)), some (53, (0, 6)), some (53, (6, 6)), some (53, (4, 6))],
    ![none, some (53, (2, 1)), some (53, (5, 1)), some (53, (4, 1)), some (53, (6, 1)), some (53, (3, 1)), some (53, (0, 1)), some (53, (1, 1))],
    ![none, some (53, (3, 2)), some (53, (2, 2)), some (53, (6, 2)), some (53, (5, 2)), some (53, (1, 2)), some (53, (4, 2)), some (53, (0, 2))],
    ![none, some (53, (4, 3)), some (53, (0, 3)), some (53, (3, 3)), some (53, (1, 3)), some (53, (6, 3)), some (53, (2, 3)), some (53, (5, 3))],
    ![none, some (53, (5, 4)), some (53, (6, 4)), some (53, (0, 4)), some (53, (4, 4)), some (53, (2, 4)), some (53, (1, 4)), some (53, (3, 4))],
    ![none, some (53, (6, 5)), some (53, (4, 5)), some (53, (1, 5)), some (53, (0, 5)), some (53, (5, 5)), some (53, (3, 5)), some (53, (2, 5))]]
private def commPair_4_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (54, (0, 0)), some (54, (6, 0)), some (54, (1, 0)), some (54, (2, 0)), some (54, (3, 0)), some (54, (4, 0)), some (54, (5, 0))],
    ![none, some (54, (3, 6)), some (54, (0, 6)), some (54, (2, 6)), some (54, (6, 6)), some (54, (5, 6)), some (54, (1, 6)), some (54, (4, 6))],
    ![none, some (54, (4, 1)), some (54, (5, 1)), some (54, (0, 1)), some (54, (3, 1)), some (54, (1, 1)), some (54, (6, 1)), some (54, (2, 1))],
    ![none, some (54, (5, 2)), some (54, (3, 2)), some (54, (6, 2)), some (54, (0, 2)), some (54, (4, 2)), some (54, (2, 2)), some (54, (1, 2))],
    ![none, some (54, (6, 3)), some (54, (2, 3)), some (54, (4, 3)), some (54, (1, 3)), some (54, (0, 3)), some (54, (5, 3)), some (54, (3, 3))],
    ![none, some (54, (1, 4)), some (54, (4, 4)), some (54, (3, 4)), some (54, (5, 4)), some (54, (2, 4)), some (54, (0, 4)), some (54, (6, 4))],
    ![none, some (54, (2, 5)), some (54, (1, 5)), some (54, (5, 5)), some (54, (4, 5)), some (54, (6, 5)), some (54, (3, 5)), some (54, (0, 5))]]
private def commPair_4_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (55, (0, 0)), some (56, (0, 0)), some (57, (0, 0)), some (58, (0, 0)), some (59, (0, 0)), some (60, (0, 0)), some (61, (0, 0))],
    ![none, some (58, (0, 6)), some (57, (0, 6)), some (61, (0, 6)), some (60, (0, 6)), some (56, (0, 6)), some (59, (0, 6)), some (55, (0, 6))],
    ![none, some (59, (0, 1)), some (55, (0, 1)), some (58, (0, 1)), some (56, (0, 1)), some (61, (0, 1)), some (57, (0, 1)), some (60, (0, 1))],
    ![none, some (60, (0, 2)), some (61, (0, 2)), some (55, (0, 2)), some (59, (0, 2)), some (57, (0, 2)), some (56, (0, 2)), some (58, (0, 2))],
    ![none, some (61, (0, 3)), some (59, (0, 3)), some (56, (0, 3)), some (55, (0, 3)), some (60, (0, 3)), some (58, (0, 3)), some (57, (0, 3))],
    ![none, some (56, (0, 4)), some (58, (0, 4)), some (60, (0, 4)), some (57, (0, 4)), some (55, (0, 4)), some (61, (0, 4)), some (59, (0, 4))],
    ![none, some (57, (0, 5)), some (60, (0, 5)), some (59, (0, 5)), some (61, (0, 5)), some (58, (0, 5)), some (55, (0, 5)), some (56, (0, 5))]]
private def commPair_4_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (62, (0, 0)), some (62, (1, 0)), some (62, (2, 0)), some (62, (3, 0)), some (62, (4, 0)), some (62, (5, 0)), some (62, (6, 0))],
    ![none, some (62, (0, 6)), some (62, (1, 6)), some (62, (2, 6)), some (62, (3, 6)), some (62, (4, 6)), some (62, (5, 6)), some (62, (6, 6))],
    ![none, some (62, (0, 1)), some (62, (1, 1)), some (62, (2, 1)), some (62, (3, 1)), some (62, (4, 1)), some (62, (5, 1)), some (62, (6, 1))],
    ![none, some (62, (0, 2)), some (62, (1, 2)), some (62, (2, 2)), some (62, (3, 2)), some (62, (4, 2)), some (62, (5, 2)), some (62, (6, 2))],
    ![none, some (62, (0, 3)), some (62, (1, 3)), some (62, (2, 3)), some (62, (3, 3)), some (62, (4, 3)), some (62, (5, 3)), some (62, (6, 3))],
    ![none, some (62, (0, 4)), some (62, (1, 4)), some (62, (2, 4)), some (62, (3, 4)), some (62, (4, 4)), some (62, (5, 4)), some (62, (6, 4))],
    ![none, some (62, (0, 5)), some (62, (1, 5)), some (62, (2, 5)), some (62, (3, 5)), some (62, (4, 5)), some (62, (5, 5)), some (62, (6, 5))]]
private def commPair_5_6 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (63, (0, 0)), some (63, (6, 1)), some (63, (1, 2)), some (63, (2, 3)), some (63, (3, 4)), some (63, (4, 5)), some (63, (5, 6))],
    ![none, some (63, (0, 1)), some (63, (6, 3)), some (63, (1, 5)), some (63, (2, 2)), some (63, (3, 0)), some (63, (4, 6)), some (63, (5, 4))],
    ![none, some (63, (0, 2)), some (63, (6, 5)), some (63, (1, 4)), some (63, (2, 6)), some (63, (3, 3)), some (63, (4, 0)), some (63, (5, 1))],
    ![none, some (63, (0, 3)), some (63, (6, 2)), some (63, (1, 6)), some (63, (2, 5)), some (63, (3, 1)), some (63, (4, 4)), some (63, (5, 0))],
    ![none, some (63, (0, 4)), some (63, (6, 0)), some (63, (1, 3)), some (63, (2, 1)), some (63, (3, 6)), some (63, (4, 2)), some (63, (5, 5))],
    ![none, some (63, (0, 5)), some (63, (6, 6)), some (63, (1, 0)), some (63, (2, 4)), some (63, (3, 2)), some (63, (4, 1)), some (63, (5, 3))],
    ![none, some (63, (0, 6)), some (63, (6, 4)), some (63, (1, 1)), some (63, (2, 0)), some (63, (3, 5)), some (63, (4, 3)), some (63, (5, 2))]]
private def commPair_5_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (64, (0, 0)), some (64, (1, 2)), some (64, (2, 3)), some (64, (3, 4)), some (64, (4, 5)), some (64, (5, 6)), some (64, (6, 1))],
    ![none, some (64, (1, 5)), some (64, (3, 0)), some (64, (5, 4)), some (64, (2, 2)), some (64, (0, 1)), some (64, (6, 3)), some (64, (4, 6))],
    ![none, some (64, (2, 6)), some (64, (5, 1)), some (64, (4, 0)), some (64, (6, 5)), some (64, (3, 3)), some (64, (0, 2)), some (64, (1, 4))],
    ![none, some (64, (3, 1)), some (64, (2, 5)), some (64, (6, 2)), some (64, (5, 0)), some (64, (1, 6)), some (64, (4, 4)), some (64, (0, 3))],
    ![none, some (64, (4, 2)), some (64, (0, 4)), some (64, (3, 6)), some (64, (1, 3)), some (64, (6, 0)), some (64, (2, 1)), some (64, (5, 5))],
    ![none, some (64, (5, 3)), some (64, (6, 6)), some (64, (0, 5)), some (64, (4, 1)), some (64, (2, 4)), some (64, (1, 0)), some (64, (3, 2))],
    ![none, some (64, (6, 4)), some (64, (4, 3)), some (64, (1, 1)), some (64, (0, 6)), some (64, (5, 2)), some (64, (3, 5)), some (64, (2, 0))]]
private def commPair_5_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (65, (0, 0)), some (65, (4, 5)), some (65, (5, 6)), some (65, (6, 1)), some (65, (1, 2)), some (65, (2, 3)), some (65, (3, 4))],
    ![none, some (65, (5, 4)), some (65, (2, 2)), some (65, (1, 5)), some (65, (3, 0)), some (65, (6, 3)), some (65, (0, 1)), some (65, (4, 6))],
    ![none, some (65, (6, 5)), some (65, (5, 1)), some (65, (3, 3)), some (65, (2, 6)), some (65, (4, 0)), some (65, (1, 4)), some (65, (0, 2))],
    ![none, some (65, (1, 6)), some (65, (0, 3)), some (65, (6, 2)), some (65, (4, 4)), some (65, (3, 1)), some (65, (5, 0)), some (65, (2, 5))],
    ![none, some (65, (2, 1)), some (65, (3, 6)), some (65, (0, 4)), some (65, (1, 3)), some (65, (5, 5)), some (65, (4, 2)), some (65, (6, 0))],
    ![none, some (65, (3, 2)), some (65, (1, 0)), some (65, (4, 1)), some (65, (0, 5)), some (65, (2, 4)), some (65, (6, 6)), some (65, (5, 3))],
    ![none, some (65, (4, 3)), some (65, (6, 4)), some (65, (2, 0)), some (65, (5, 2)), some (65, (0, 6)), some (65, (3, 5)), some (65, (1, 1))]]
private def commPair_5_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (66, (0, 0)), some (66, (2, 3)), some (66, (3, 4)), some (66, (4, 5)), some (66, (5, 6)), some (66, (6, 1)), some (66, (1, 2))],
    ![none, some (66, (6, 3)), some (66, (1, 5)), some (66, (0, 1)), some (66, (5, 4)), some (66, (3, 0)), some (66, (2, 2)), some (66, (4, 6))],
    ![none, some (66, (1, 4)), some (66, (5, 1)), some (66, (2, 6)), some (66, (0, 2)), some (66, (6, 5)), some (66, (4, 0)), some (66, (3, 3))],
    ![none, some (66, (2, 5)), some (66, (4, 4)), some (66, (6, 2)), some (66, (3, 1)), some (66, (0, 3)), some (66, (1, 6)), some (66, (5, 0))],
    ![none, some (66, (3, 6)), some (66, (6, 0)), some (66, (5, 5)), some (66, (1, 3)), some (66, (4, 2)), some (66, (0, 4)), some (66, (2, 1))],
    ![none, some (66, (4, 1)), some (66, (3, 2)), some (66, (1, 0)), some (66, (6, 6)), some (66, (2, 4)), some (66, (5, 3)), some (66, (0, 5))],
    ![none, some (66, (5, 2)), some (66, (0, 6)), some (66, (4, 3)), some (66, (2, 0)), some (66, (1, 1)), some (66, (3, 5)), some (66, (6, 4))]]
private def commPair_5_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (67, (0, 0)), some (67, (6, 1)), some (67, (1, 2)), some (67, (2, 3)), some (67, (3, 4)), some (67, (4, 5)), some (67, (5, 6))],
    ![none, some (67, (3, 0)), some (67, (0, 1)), some (67, (2, 2)), some (67, (6, 3)), some (67, (5, 4)), some (67, (1, 5)), some (67, (4, 6))],
    ![none, some (67, (4, 0)), some (67, (5, 1)), some (67, (0, 2)), some (67, (3, 3)), some (67, (1, 4)), some (67, (6, 5)), some (67, (2, 6))],
    ![none, some (67, (5, 0)), some (67, (3, 1)), some (67, (6, 2)), some (67, (0, 3)), some (67, (4, 4)), some (67, (2, 5)), some (67, (1, 6))],
    ![none, some (67, (6, 0)), some (67, (2, 1)), some (67, (4, 2)), some (67, (1, 3)), some (67, (0, 4)), some (67, (5, 5)), some (67, (3, 6))],
    ![none, some (67, (1, 0)), some (67, (4, 1)), some (67, (3, 2)), some (67, (5, 3)), some (67, (2, 4)), some (67, (0, 5)), some (67, (6, 6))],
    ![none, some (67, (2, 0)), some (67, (1, 1)), some (67, (5, 2)), some (67, (4, 3)), some (67, (6, 4)), some (67, (3, 5)), some (67, (0, 6))]]
private def commPair_5_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (68, (0, 0)), some (68, (1, 2)), some (68, (2, 3)), some (68, (3, 4)), some (68, (4, 5)), some (68, (5, 6)), some (68, (6, 1))],
    ![none, some (68, (0, 1)), some (68, (1, 5)), some (68, (2, 2)), some (68, (3, 0)), some (68, (4, 6)), some (68, (5, 4)), some (68, (6, 3))],
    ![none, some (68, (0, 2)), some (68, (1, 4)), some (68, (2, 6)), some (68, (3, 3)), some (68, (4, 0)), some (68, (5, 1)), some (68, (6, 5))],
    ![none, some (68, (0, 3)), some (68, (1, 6)), some (68, (2, 5)), some (68, (3, 1)), some (68, (4, 4)), some (68, (5, 0)), some (68, (6, 2))],
    ![none, some (68, (0, 4)), some (68, (1, 3)), some (68, (2, 1)), some (68, (3, 6)), some (68, (4, 2)), some (68, (5, 5)), some (68, (6, 0))],
    ![none, some (68, (0, 5)), some (68, (1, 0)), some (68, (2, 4)), some (68, (3, 2)), some (68, (4, 1)), some (68, (5, 3)), some (68, (6, 6))],
    ![none, some (68, (0, 6)), some (68, (1, 1)), some (68, (2, 0)), some (68, (3, 5)), some (68, (4, 3)), some (68, (5, 2)), some (68, (6, 4))]]
private def commPair_6_7 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (69, (0, 0)), some (69, (0, 4)), some (69, (0, 5)), some (69, (0, 6)), some (69, (0, 1)), some (69, (0, 2)), some (69, (0, 3))],
    ![none, some (69, (6, 4)), some (69, (6, 6)), some (69, (6, 2)), some (69, (6, 5)), some (69, (6, 0)), some (69, (6, 3)), some (69, (6, 1))],
    ![none, some (69, (1, 5)), some (69, (1, 2)), some (69, (1, 1)), some (69, (1, 3)), some (69, (1, 6)), some (69, (1, 0)), some (69, (1, 4))],
    ![none, some (69, (2, 6)), some (69, (2, 5)), some (69, (2, 3)), some (69, (2, 2)), some (69, (2, 4)), some (69, (2, 1)), some (69, (2, 0))],
    ![none, some (69, (3, 1)), some (69, (3, 0)), some (69, (3, 6)), some (69, (3, 4)), some (69, (3, 3)), some (69, (3, 5)), some (69, (3, 2))],
    ![none, some (69, (4, 2)), some (69, (4, 3)), some (69, (4, 0)), some (69, (4, 1)), some (69, (4, 5)), some (69, (4, 4)), some (69, (4, 6))],
    ![none, some (69, (5, 3)), some (69, (5, 1)), some (69, (5, 4)), some (69, (5, 0)), some (69, (5, 2)), some (69, (5, 6)), some (69, (5, 5))]]
private def commPair_6_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (70, (0, 0)), some (70, (0, 3)), some (70, (0, 4)), some (70, (0, 5)), some (70, (0, 6)), some (70, (0, 1)), some (70, (0, 2))],
    ![none, some (70, (6, 5)), some (70, (6, 4)), some (70, (6, 2)), some (70, (6, 1)), some (70, (6, 3)), some (70, (6, 6)), some (70, (6, 0))],
    ![none, some (70, (1, 6)), some (70, (1, 0)), some (70, (1, 5)), some (70, (1, 3)), some (70, (1, 2)), some (70, (1, 4)), some (70, (1, 1))],
    ![none, some (70, (2, 1)), some (70, (2, 2)), some (70, (2, 0)), some (70, (2, 6)), some (70, (2, 4)), some (70, (2, 3)), some (70, (2, 5))],
    ![none, some (70, (3, 2)), some (70, (3, 6)), some (70, (3, 3)), some (70, (3, 0)), some (70, (3, 1)), some (70, (3, 5)), some (70, (3, 4))],
    ![none, some (70, (4, 3)), some (70, (4, 5)), some (70, (4, 1)), some (70, (4, 4)), some (70, (4, 0)), some (70, (4, 2)), some (70, (4, 6))],
    ![none, some (70, (5, 4)), some (70, (5, 1)), some (70, (5, 6)), some (70, (5, 2)), some (70, (5, 5)), some (70, (5, 0)), some (70, (5, 3))]]
private def commPair_6_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (71, (0, 0)), some (71, (0, 6)), some (71, (0, 1)), some (71, (0, 2)), some (71, (0, 3)), some (71, (0, 4)), some (71, (0, 5))],
    ![none, some (71, (6, 3)), some (71, (6, 0)), some (71, (6, 2)), some (71, (6, 6)), some (71, (6, 5)), some (71, (6, 1)), some (71, (6, 4))],
    ![none, some (71, (1, 4)), some (71, (1, 5)), some (71, (1, 0)), some (71, (1, 3)), some (71, (1, 1)), some (71, (1, 6)), some (71, (1, 2))],
    ![none, some (71, (2, 5)), some (71, (2, 3)), some (71, (2, 6)), some (71, (2, 0)), some (71, (2, 4)), some (71, (2, 2)), some (71, (2, 1))],
    ![none, some (71, (3, 6)), some (71, (3, 2)), some (71, (3, 4)), some (71, (3, 1)), some (71, (3, 0)), some (71, (3, 5)), some (71, (3, 3))],
    ![none, some (71, (4, 1)), some (71, (4, 4)), some (71, (4, 3)), some (71, (4, 5)), some (71, (4, 2)), some (71, (4, 0)), some (71, (4, 6))],
    ![none, some (71, (5, 2)), some (71, (5, 1)), some (71, (5, 5)), some (71, (5, 4)), some (71, (5, 6)), some (71, (5, 3)), some (71, (5, 0))]]
private def commPair_6_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (72, (0, 0)), some (72, (0, 1)), some (72, (0, 2)), some (72, (0, 3)), some (72, (0, 4)), some (72, (0, 5)), some (72, (0, 6))],
    ![none, some (72, (6, 0)), some (72, (6, 1)), some (72, (6, 2)), some (72, (6, 3)), some (72, (6, 4)), some (72, (6, 5)), some (72, (6, 6))],
    ![none, some (72, (1, 0)), some (72, (1, 1)), some (72, (1, 2)), some (72, (1, 3)), some (72, (1, 4)), some (72, (1, 5)), some (72, (1, 6))],
    ![none, some (72, (2, 0)), some (72, (2, 1)), some (72, (2, 2)), some (72, (2, 3)), some (72, (2, 4)), some (72, (2, 5)), some (72, (2, 6))],
    ![none, some (72, (3, 0)), some (72, (3, 1)), some (72, (3, 2)), some (72, (3, 3)), some (72, (3, 4)), some (72, (3, 5)), some (72, (3, 6))],
    ![none, some (72, (4, 0)), some (72, (4, 1)), some (72, (4, 2)), some (72, (4, 3)), some (72, (4, 4)), some (72, (4, 5)), some (72, (4, 6))],
    ![none, some (72, (5, 0)), some (72, (5, 1)), some (72, (5, 2)), some (72, (5, 3)), some (72, (5, 4)), some (72, (5, 5)), some (72, (5, 6))]]
private def commPair_6_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (73, (0, 0)), some (74, (0, 0)), some (75, (0, 0)), some (76, (0, 0)), some (77, (0, 0)), some (78, (0, 0)), some (79, (0, 0))],
    ![none, some (76, (6, 0)), some (75, (6, 0)), some (79, (6, 0)), some (78, (6, 0)), some (74, (6, 0)), some (77, (6, 0)), some (73, (6, 0))],
    ![none, some (77, (1, 0)), some (73, (1, 0)), some (76, (1, 0)), some (74, (1, 0)), some (79, (1, 0)), some (75, (1, 0)), some (78, (1, 0))],
    ![none, some (78, (2, 0)), some (79, (2, 0)), some (73, (2, 0)), some (77, (2, 0)), some (75, (2, 0)), some (74, (2, 0)), some (76, (2, 0))],
    ![none, some (79, (3, 0)), some (77, (3, 0)), some (74, (3, 0)), some (73, (3, 0)), some (78, (3, 0)), some (76, (3, 0)), some (75, (3, 0))],
    ![none, some (74, (4, 0)), some (76, (4, 0)), some (78, (4, 0)), some (75, (4, 0)), some (73, (4, 0)), some (79, (4, 0)), some (77, (4, 0))],
    ![none, some (75, (5, 0)), some (78, (5, 0)), some (77, (5, 0)), some (79, (5, 0)), some (76, (5, 0)), some (73, (5, 0)), some (74, (5, 0))]]
private def commPair_7_8 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (80, (0, 0)), some (80, (6, 4)), some (80, (1, 5)), some (80, (2, 6)), some (80, (3, 1)), some (80, (4, 2)), some (80, (5, 3))],
    ![none, some (80, (4, 3)), some (80, (5, 1)), some (80, (0, 4)), some (80, (3, 0)), some (80, (1, 2)), some (80, (6, 6)), some (80, (2, 5))],
    ![none, some (80, (5, 4)), some (80, (3, 6)), some (80, (6, 2)), some (80, (0, 5)), some (80, (4, 0)), some (80, (2, 3)), some (80, (1, 1))],
    ![none, some (80, (6, 5)), some (80, (2, 2)), some (80, (4, 1)), some (80, (1, 3)), some (80, (0, 6)), some (80, (5, 0)), some (80, (3, 4))],
    ![none, some (80, (1, 6)), some (80, (4, 5)), some (80, (3, 3)), some (80, (5, 2)), some (80, (2, 4)), some (80, (0, 1)), some (80, (6, 0))],
    ![none, some (80, (2, 1)), some (80, (1, 0)), some (80, (5, 6)), some (80, (4, 4)), some (80, (6, 3)), some (80, (3, 5)), some (80, (0, 2))],
    ![none, some (80, (3, 2)), some (80, (0, 3)), some (80, (2, 0)), some (80, (6, 1)), some (80, (5, 5)), some (80, (1, 4)), some (80, (4, 6))]]
private def commPair_7_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (81, (0, 0)), some (81, (1, 5)), some (81, (2, 6)), some (81, (3, 1)), some (81, (4, 2)), some (81, (5, 3)), some (81, (6, 4))],
    ![none, some (81, (2, 5)), some (81, (5, 1)), some (81, (4, 3)), some (81, (6, 6)), some (81, (3, 0)), some (81, (0, 4)), some (81, (1, 2))],
    ![none, some (81, (3, 6)), some (81, (2, 3)), some (81, (6, 2)), some (81, (5, 4)), some (81, (1, 1)), some (81, (4, 0)), some (81, (0, 5))],
    ![none, some (81, (4, 1)), some (81, (0, 6)), some (81, (3, 4)), some (81, (1, 3)), some (81, (6, 5)), some (81, (2, 2)), some (81, (5, 0))],
    ![none, some (81, (5, 2)), some (81, (6, 0)), some (81, (0, 1)), some (81, (4, 5)), some (81, (2, 4)), some (81, (1, 6)), some (81, (3, 3))],
    ![none, some (81, (6, 3)), some (81, (4, 4)), some (81, (1, 0)), some (81, (0, 2)), some (81, (5, 6)), some (81, (3, 5)), some (81, (2, 1))],
    ![none, some (81, (1, 4)), some (81, (3, 2)), some (81, (5, 5)), some (81, (2, 0)), some (81, (0, 3)), some (81, (6, 1)), some (81, (4, 6))]]
private def commPair_7_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (82, (0, 0)), some (82, (3, 1)), some (82, (4, 2)), some (82, (5, 3)), some (82, (6, 4)), some (82, (1, 5)), some (82, (2, 6))],
    ![none, some (82, (3, 0)), some (82, (5, 1)), some (82, (1, 2)), some (82, (4, 3)), some (82, (0, 4)), some (82, (2, 5)), some (82, (6, 6))],
    ![none, some (82, (4, 0)), some (82, (1, 1)), some (82, (6, 2)), some (82, (2, 3)), some (82, (5, 4)), some (82, (0, 5)), some (82, (3, 6))],
    ![none, some (82, (5, 0)), some (82, (4, 1)), some (82, (2, 2)), some (82, (1, 3)), some (82, (3, 4)), some (82, (6, 5)), some (82, (0, 6))],
    ![none, some (82, (6, 0)), some (82, (0, 1)), some (82, (5, 2)), some (82, (3, 3)), some (82, (2, 4)), some (82, (4, 5)), some (82, (1, 6))],
    ![none, some (82, (1, 0)), some (82, (2, 1)), some (82, (0, 2)), some (82, (6, 3)), some (82, (4, 4)), some (82, (3, 5)), some (82, (5, 6))],
    ![none, some (82, (2, 0)), some (82, (6, 1)), some (82, (3, 2)), some (82, (0, 3)), some (82, (1, 4)), some (82, (5, 5)), some (82, (4, 6))]]
private def commPair_7_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (83, (0, 0)), some (83, (1, 5)), some (83, (2, 6)), some (83, (3, 1)), some (83, (4, 2)), some (83, (5, 3)), some (83, (6, 4))],
    ![none, some (83, (0, 4)), some (83, (1, 2)), some (83, (2, 5)), some (83, (3, 0)), some (83, (4, 3)), some (83, (5, 1)), some (83, (6, 6))],
    ![none, some (83, (0, 5)), some (83, (1, 1)), some (83, (2, 3)), some (83, (3, 6)), some (83, (4, 0)), some (83, (5, 4)), some (83, (6, 2))],
    ![none, some (83, (0, 6)), some (83, (1, 3)), some (83, (2, 2)), some (83, (3, 4)), some (83, (4, 1)), some (83, (5, 0)), some (83, (6, 5))],
    ![none, some (83, (0, 1)), some (83, (1, 6)), some (83, (2, 4)), some (83, (3, 3)), some (83, (4, 5)), some (83, (5, 2)), some (83, (6, 0))],
    ![none, some (83, (0, 2)), some (83, (1, 0)), some (83, (2, 1)), some (83, (3, 5)), some (83, (4, 4)), some (83, (5, 6)), some (83, (6, 3))],
    ![none, some (83, (0, 3)), some (83, (1, 4)), some (83, (2, 0)), some (83, (3, 2)), some (83, (4, 6)), some (83, (5, 5)), some (83, (6, 1))]]
private def commPair_8_9 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (84, (0, 0)), some (84, (3, 2)), some (84, (4, 3)), some (84, (5, 4)), some (84, (6, 5)), some (84, (1, 6)), some (84, (2, 1))],
    ![none, some (84, (3, 6)), some (84, (5, 1)), some (84, (1, 0)), some (84, (4, 5)), some (84, (0, 3)), some (84, (2, 2)), some (84, (6, 4))],
    ![none, some (84, (4, 1)), some (84, (1, 5)), some (84, (6, 2)), some (84, (2, 0)), some (84, (5, 6)), some (84, (0, 4)), some (84, (3, 3))],
    ![none, some (84, (5, 2)), some (84, (4, 4)), some (84, (2, 6)), some (84, (1, 3)), some (84, (3, 0)), some (84, (6, 1)), some (84, (0, 5))],
    ![none, some (84, (6, 3)), some (84, (0, 6)), some (84, (5, 5)), some (84, (3, 1)), some (84, (2, 4)), some (84, (4, 0)), some (84, (1, 2))],
    ![none, some (84, (1, 4)), some (84, (2, 3)), some (84, (0, 1)), some (84, (6, 6)), some (84, (4, 2)), some (84, (3, 5)), some (84, (5, 0))],
    ![none, some (84, (2, 5)), some (84, (6, 0)), some (84, (3, 4)), some (84, (0, 2)), some (84, (1, 1)), some (84, (5, 3)), some (84, (4, 6))]]
private def commPair_8_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (85, (0, 0)), some (85, (2, 1)), some (85, (3, 2)), some (85, (4, 3)), some (85, (5, 4)), some (85, (6, 5)), some (85, (1, 6))],
    ![none, some (85, (1, 0)), some (85, (5, 1)), some (85, (2, 2)), some (85, (0, 3)), some (85, (6, 4)), some (85, (4, 5)), some (85, (3, 6))],
    ![none, some (85, (2, 0)), some (85, (4, 1)), some (85, (6, 2)), some (85, (3, 3)), some (85, (0, 4)), some (85, (1, 5)), some (85, (5, 6))],
    ![none, some (85, (3, 0)), some (85, (6, 1)), some (85, (5, 2)), some (85, (1, 3)), some (85, (4, 4)), some (85, (0, 5)), some (85, (2, 6))],
    ![none, some (85, (4, 0)), some (85, (3, 1)), some (85, (1, 2)), some (85, (6, 3)), some (85, (2, 4)), some (85, (5, 5)), some (85, (0, 6))],
    ![none, some (85, (5, 0)), some (85, (0, 1)), some (85, (4, 2)), some (85, (2, 3)), some (85, (1, 4)), some (85, (3, 5)), some (85, (6, 6))],
    ![none, some (85, (6, 0)), some (85, (1, 1)), some (85, (0, 2)), some (85, (5, 3)), some (85, (3, 4)), some (85, (2, 5)), some (85, (4, 6))]]
private def commPair_8_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (86, (0, 0)), some (86, (1, 6)), some (86, (2, 1)), some (86, (3, 2)), some (86, (4, 3)), some (86, (5, 4)), some (86, (6, 5))],
    ![none, some (86, (0, 3)), some (86, (1, 0)), some (86, (2, 2)), some (86, (3, 6)), some (86, (4, 5)), some (86, (5, 1)), some (86, (6, 4))],
    ![none, some (86, (0, 4)), some (86, (1, 5)), some (86, (2, 0)), some (86, (3, 3)), some (86, (4, 1)), some (86, (5, 6)), some (86, (6, 2))],
    ![none, some (86, (0, 5)), some (86, (1, 3)), some (86, (2, 6)), some (86, (3, 0)), some (86, (4, 4)), some (86, (5, 2)), some (86, (6, 1))],
    ![none, some (86, (0, 6)), some (86, (1, 2)), some (86, (2, 4)), some (86, (3, 1)), some (86, (4, 0)), some (86, (5, 5)), some (86, (6, 3))],
    ![none, some (86, (0, 1)), some (86, (1, 4)), some (86, (2, 3)), some (86, (3, 5)), some (86, (4, 2)), some (86, (5, 0)), some (86, (6, 6))],
    ![none, some (86, (0, 2)), some (86, (1, 1)), some (86, (2, 5)), some (86, (3, 4)), some (86, (4, 6)), some (86, (5, 3)), some (86, (6, 0))]]
private def commPair_9_10 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (87, (0, 0)), some (87, (4, 1)), some (87, (5, 2)), some (87, (6, 3)), some (87, (1, 4)), some (87, (2, 5)), some (87, (3, 6))],
    ![none, some (87, (6, 0)), some (87, (5, 1)), some (87, (3, 2)), some (87, (2, 3)), some (87, (4, 4)), some (87, (1, 5)), some (87, (0, 6))],
    ![none, some (87, (1, 0)), some (87, (0, 1)), some (87, (6, 2)), some (87, (4, 3)), some (87, (3, 4)), some (87, (5, 5)), some (87, (2, 6))],
    ![none, some (87, (2, 0)), some (87, (3, 1)), some (87, (0, 2)), some (87, (1, 3)), some (87, (5, 4)), some (87, (4, 5)), some (87, (6, 6))],
    ![none, some (87, (3, 0)), some (87, (1, 1)), some (87, (4, 2)), some (87, (0, 3)), some (87, (2, 4)), some (87, (6, 5)), some (87, (5, 6))],
    ![none, some (87, (4, 0)), some (87, (6, 1)), some (87, (2, 2)), some (87, (5, 3)), some (87, (0, 4)), some (87, (3, 5)), some (87, (1, 6))],
    ![none, some (87, (5, 0)), some (87, (2, 1)), some (87, (1, 2)), some (87, (3, 3)), some (87, (6, 4)), some (87, (0, 5)), some (87, (4, 6))]]
private def commPair_9_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (88, (0, 0)), some (88, (1, 4)), some (88, (2, 5)), some (88, (3, 6)), some (88, (4, 1)), some (88, (5, 2)), some (88, (6, 3))],
    ![none, some (88, (0, 6)), some (88, (1, 5)), some (88, (2, 3)), some (88, (3, 2)), some (88, (4, 4)), some (88, (5, 1)), some (88, (6, 0))],
    ![none, some (88, (0, 1)), some (88, (1, 0)), some (88, (2, 6)), some (88, (3, 4)), some (88, (4, 3)), some (88, (5, 5)), some (88, (6, 2))],
    ![none, some (88, (0, 2)), some (88, (1, 3)), some (88, (2, 0)), some (88, (3, 1)), some (88, (4, 5)), some (88, (5, 4)), some (88, (6, 6))],
    ![none, some (88, (0, 3)), some (88, (1, 1)), some (88, (2, 4)), some (88, (3, 0)), some (88, (4, 2)), some (88, (5, 6)), some (88, (6, 5))],
    ![none, some (88, (0, 4)), some (88, (1, 6)), some (88, (2, 2)), some (88, (3, 5)), some (88, (4, 0)), some (88, (5, 3)), some (88, (6, 1))],
    ![none, some (88, (0, 5)), some (88, (1, 2)), some (88, (2, 1)), some (88, (3, 3)), some (88, (4, 6)), some (88, (5, 0)), some (88, (6, 4))]]
private def commPair_10_11 : Fin 8 → Fin 8 → Option (Transport 90) :=
  ![![none, none, none, none, none, none, none, none],
    ![none, some (89, (0, 0)), some (89, (1, 0)), some (89, (2, 0)), some (89, (3, 0)), some (89, (4, 0)), some (89, (5, 0)), some (89, (6, 0))],
    ![none, some (89, (0, 1)), some (89, (1, 1)), some (89, (2, 1)), some (89, (3, 1)), some (89, (4, 1)), some (89, (5, 1)), some (89, (6, 1))],
    ![none, some (89, (0, 2)), some (89, (1, 2)), some (89, (2, 2)), some (89, (3, 2)), some (89, (4, 2)), some (89, (5, 2)), some (89, (6, 2))],
    ![none, some (89, (0, 3)), some (89, (1, 3)), some (89, (2, 3)), some (89, (3, 3)), some (89, (4, 3)), some (89, (5, 3)), some (89, (6, 3))],
    ![none, some (89, (0, 4)), some (89, (1, 4)), some (89, (2, 4)), some (89, (3, 4)), some (89, (4, 4)), some (89, (5, 4)), some (89, (6, 4))],
    ![none, some (89, (0, 5)), some (89, (1, 5)), some (89, (2, 5)), some (89, (3, 5)), some (89, (4, 5)), some (89, (5, 5)), some (89, (6, 5))],
    ![none, some (89, (0, 6)), some (89, (1, 6)), some (89, (2, 6)), some (89, (3, 6)), some (89, (4, 6)), some (89, (5, 6)), some (89, (6, 6))]]
def commutatorTransport (i j : Fin 12) (a b : Fin 8) : Option (Transport 90) :=
  match i.val, j.val with
  | 0, 1 => commPair_0_1 a b
  | 0, 2 => commPair_0_2 a b
  | 0, 3 => commPair_0_3 a b
  | 0, 4 => commPair_0_4 a b
  | 0, 5 => commPair_0_5 a b
  | 0, 6 => commPair_0_6 a b
  | 0, 7 => commPair_0_7 a b
  | 0, 8 => commPair_0_8 a b
  | 0, 9 => commPair_0_9 a b
  | 0, 10 => commPair_0_10 a b
  | 0, 11 => commPair_0_11 a b
  | 1, 2 => commPair_1_2 a b
  | 1, 3 => commPair_1_3 a b
  | 1, 4 => commPair_1_4 a b
  | 1, 5 => commPair_1_5 a b
  | 1, 6 => commPair_1_6 a b
  | 1, 7 => commPair_1_7 a b
  | 1, 8 => commPair_1_8 a b
  | 1, 9 => commPair_1_9 a b
  | 1, 10 => commPair_1_10 a b
  | 1, 11 => commPair_1_11 a b
  | 2, 3 => commPair_2_3 a b
  | 2, 4 => commPair_2_4 a b
  | 2, 5 => commPair_2_5 a b
  | 2, 6 => commPair_2_6 a b
  | 2, 7 => commPair_2_7 a b
  | 2, 8 => commPair_2_8 a b
  | 2, 9 => commPair_2_9 a b
  | 2, 10 => commPair_2_10 a b
  | 2, 11 => commPair_2_11 a b
  | 3, 4 => commPair_3_4 a b
  | 3, 5 => commPair_3_5 a b
  | 3, 6 => commPair_3_6 a b
  | 3, 7 => commPair_3_7 a b
  | 3, 8 => commPair_3_8 a b
  | 3, 9 => commPair_3_9 a b
  | 3, 10 => commPair_3_10 a b
  | 3, 11 => commPair_3_11 a b
  | 4, 5 => commPair_4_5 a b
  | 4, 6 => commPair_4_6 a b
  | 4, 7 => commPair_4_7 a b
  | 4, 8 => commPair_4_8 a b
  | 4, 9 => commPair_4_9 a b
  | 4, 10 => commPair_4_10 a b
  | 4, 11 => commPair_4_11 a b
  | 5, 6 => commPair_5_6 a b
  | 5, 7 => commPair_5_7 a b
  | 5, 8 => commPair_5_8 a b
  | 5, 9 => commPair_5_9 a b
  | 5, 10 => commPair_5_10 a b
  | 5, 11 => commPair_5_11 a b
  | 6, 7 => commPair_6_7 a b
  | 6, 8 => commPair_6_8 a b
  | 6, 9 => commPair_6_9 a b
  | 6, 10 => commPair_6_10 a b
  | 6, 11 => commPair_6_11 a b
  | 7, 8 => commPair_7_8 a b
  | 7, 9 => commPair_7_9 a b
  | 7, 10 => commPair_7_10 a b
  | 7, 11 => commPair_7_11 a b
  | 8, 9 => commPair_8_9 a b
  | 8, 10 => commPair_8_10 a b
  | 8, 11 => commPair_8_11 a b
  | 9, 10 => commPair_9_10 a b
  | 9, 11 => commPair_9_11 a b
  | 10, 11 => commPair_10_11 a b
  | _, _ => none

def productTransport : Fin 12 → Fin 8 → Fin 8 → Option (Transport 84) :=
  ![![![none, none, none, none, none, none, none, none],
      ![none, some (0, (0, 0)), some (1, (0, 0)), some (2, (0, 0)), some (3, (0, 0)), some (4, (0, 0)), some (5, (0, 0)), some (6, (0, 0))],
      ![none, some (4, (0, 4)), some (0, (0, 4)), some (3, (0, 4)), some (1, (0, 4)), some (6, (0, 4)), some (2, (0, 4)), some (5, (0, 4))],
      ![none, some (5, (0, 5)), some (6, (0, 5)), some (0, (0, 5)), some (4, (0, 5)), some (2, (0, 5)), some (1, (0, 5)), some (3, (0, 5))],
      ![none, some (6, (0, 6)), some (4, (0, 6)), some (1, (0, 6)), some (0, (0, 6)), some (5, (0, 6)), some (3, (0, 6)), some (2, (0, 6))],
      ![none, some (1, (0, 1)), some (3, (0, 1)), some (5, (0, 1)), some (2, (0, 1)), some (0, (0, 1)), some (6, (0, 1)), some (4, (0, 1))],
      ![none, some (2, (0, 2)), some (5, (0, 2)), some (4, (0, 2)), some (6, (0, 2)), some (3, (0, 2)), some (0, (0, 2)), some (1, (0, 2))],
      ![none, some (3, (0, 3)), some (2, (0, 3)), some (6, (0, 3)), some (5, (0, 3)), some (1, (0, 3)), some (4, (0, 3)), some (0, (0, 3))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (7, (0, 0)), some (8, (0, 0)), some (9, (0, 0)), some (10, (0, 0)), some (11, (0, 0)), some (12, (0, 0)), some (13, (0, 0))],
      ![none, some (11, (0, 2)), some (7, (0, 2)), some (10, (0, 2)), some (8, (0, 2)), some (13, (0, 2)), some (9, (0, 2)), some (12, (0, 2))],
      ![none, some (12, (0, 3)), some (13, (0, 3)), some (7, (0, 3)), some (11, (0, 3)), some (9, (0, 3)), some (8, (0, 3)), some (10, (0, 3))],
      ![none, some (13, (0, 4)), some (11, (0, 4)), some (8, (0, 4)), some (7, (0, 4)), some (12, (0, 4)), some (10, (0, 4)), some (9, (0, 4))],
      ![none, some (8, (0, 5)), some (10, (0, 5)), some (12, (0, 5)), some (9, (0, 5)), some (7, (0, 5)), some (13, (0, 5)), some (11, (0, 5))],
      ![none, some (9, (0, 6)), some (12, (0, 6)), some (11, (0, 6)), some (13, (0, 6)), some (10, (0, 6)), some (7, (0, 6)), some (8, (0, 6))],
      ![none, some (10, (0, 1)), some (9, (0, 1)), some (13, (0, 1)), some (12, (0, 1)), some (8, (0, 1)), some (11, (0, 1)), some (7, (0, 1))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (14, (0, 0)), some (15, (0, 0)), some (16, (0, 0)), some (17, (0, 0)), some (18, (0, 0)), some (19, (0, 0)), some (20, (0, 0))],
      ![none, some (18, (0, 3)), some (14, (0, 3)), some (17, (0, 3)), some (15, (0, 3)), some (20, (0, 3)), some (16, (0, 3)), some (19, (0, 3))],
      ![none, some (19, (0, 4)), some (20, (0, 4)), some (14, (0, 4)), some (18, (0, 4)), some (16, (0, 4)), some (15, (0, 4)), some (17, (0, 4))],
      ![none, some (20, (0, 5)), some (18, (0, 5)), some (15, (0, 5)), some (14, (0, 5)), some (19, (0, 5)), some (17, (0, 5)), some (16, (0, 5))],
      ![none, some (15, (0, 6)), some (17, (0, 6)), some (19, (0, 6)), some (16, (0, 6)), some (14, (0, 6)), some (20, (0, 6)), some (18, (0, 6))],
      ![none, some (16, (0, 1)), some (19, (0, 1)), some (18, (0, 1)), some (20, (0, 1)), some (17, (0, 1)), some (14, (0, 1)), some (15, (0, 1))],
      ![none, some (17, (0, 2)), some (16, (0, 2)), some (20, (0, 2)), some (19, (0, 2)), some (15, (0, 2)), some (18, (0, 2)), some (14, (0, 2))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (21, (0, 0)), some (22, (0, 0)), some (23, (0, 0)), some (24, (0, 0)), some (25, (0, 0)), some (26, (0, 0)), some (27, (0, 0))],
      ![none, some (25, (0, 3)), some (21, (0, 3)), some (24, (0, 3)), some (22, (0, 3)), some (27, (0, 3)), some (23, (0, 3)), some (26, (0, 3))],
      ![none, some (26, (0, 4)), some (27, (0, 4)), some (21, (0, 4)), some (25, (0, 4)), some (23, (0, 4)), some (22, (0, 4)), some (24, (0, 4))],
      ![none, some (27, (0, 5)), some (25, (0, 5)), some (22, (0, 5)), some (21, (0, 5)), some (26, (0, 5)), some (24, (0, 5)), some (23, (0, 5))],
      ![none, some (22, (0, 6)), some (24, (0, 6)), some (26, (0, 6)), some (23, (0, 6)), some (21, (0, 6)), some (27, (0, 6)), some (25, (0, 6))],
      ![none, some (23, (0, 1)), some (26, (0, 1)), some (25, (0, 1)), some (27, (0, 1)), some (24, (0, 1)), some (21, (0, 1)), some (22, (0, 1))],
      ![none, some (24, (0, 2)), some (23, (0, 2)), some (27, (0, 2)), some (26, (0, 2)), some (22, (0, 2)), some (25, (0, 2)), some (21, (0, 2))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (28, (0, 0)), some (29, (0, 0)), some (30, (0, 0)), some (31, (0, 0)), some (32, (0, 0)), some (33, (0, 0)), some (34, (0, 0))],
      ![none, some (32, (0, 6)), some (28, (0, 6)), some (31, (0, 6)), some (29, (0, 6)), some (34, (0, 6)), some (30, (0, 6)), some (33, (0, 6))],
      ![none, some (33, (0, 1)), some (34, (0, 1)), some (28, (0, 1)), some (32, (0, 1)), some (30, (0, 1)), some (29, (0, 1)), some (31, (0, 1))],
      ![none, some (34, (0, 2)), some (32, (0, 2)), some (29, (0, 2)), some (28, (0, 2)), some (33, (0, 2)), some (31, (0, 2)), some (30, (0, 2))],
      ![none, some (29, (0, 3)), some (31, (0, 3)), some (33, (0, 3)), some (30, (0, 3)), some (28, (0, 3)), some (34, (0, 3)), some (32, (0, 3))],
      ![none, some (30, (0, 4)), some (33, (0, 4)), some (32, (0, 4)), some (34, (0, 4)), some (31, (0, 4)), some (28, (0, 4)), some (29, (0, 4))],
      ![none, some (31, (0, 5)), some (30, (0, 5)), some (34, (0, 5)), some (33, (0, 5)), some (29, (0, 5)), some (32, (0, 5)), some (28, (0, 5))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (35, (0, 0)), some (36, (0, 0)), some (37, (0, 0)), some (38, (0, 0)), some (39, (0, 0)), some (40, (0, 0)), some (41, (0, 0))],
      ![none, some (39, (0, 1)), some (35, (0, 1)), some (38, (0, 1)), some (36, (0, 1)), some (41, (0, 1)), some (37, (0, 1)), some (40, (0, 1))],
      ![none, some (40, (0, 2)), some (41, (0, 2)), some (35, (0, 2)), some (39, (0, 2)), some (37, (0, 2)), some (36, (0, 2)), some (38, (0, 2))],
      ![none, some (41, (0, 3)), some (39, (0, 3)), some (36, (0, 3)), some (35, (0, 3)), some (40, (0, 3)), some (38, (0, 3)), some (37, (0, 3))],
      ![none, some (36, (0, 4)), some (38, (0, 4)), some (40, (0, 4)), some (37, (0, 4)), some (35, (0, 4)), some (41, (0, 4)), some (39, (0, 4))],
      ![none, some (37, (0, 5)), some (40, (0, 5)), some (39, (0, 5)), some (41, (0, 5)), some (38, (0, 5)), some (35, (0, 5)), some (36, (0, 5))],
      ![none, some (38, (0, 6)), some (37, (0, 6)), some (41, (0, 6)), some (40, (0, 6)), some (36, (0, 6)), some (39, (0, 6)), some (35, (0, 6))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (42, (0, 0)), some (43, (0, 0)), some (44, (0, 0)), some (45, (0, 0)), some (46, (0, 0)), some (47, (0, 0)), some (48, (0, 0))],
      ![none, some (46, (6, 0)), some (42, (6, 0)), some (45, (6, 0)), some (43, (6, 0)), some (48, (6, 0)), some (44, (6, 0)), some (47, (6, 0))],
      ![none, some (47, (1, 0)), some (48, (1, 0)), some (42, (1, 0)), some (46, (1, 0)), some (44, (1, 0)), some (43, (1, 0)), some (45, (1, 0))],
      ![none, some (48, (2, 0)), some (46, (2, 0)), some (43, (2, 0)), some (42, (2, 0)), some (47, (2, 0)), some (45, (2, 0)), some (44, (2, 0))],
      ![none, some (43, (3, 0)), some (45, (3, 0)), some (47, (3, 0)), some (44, (3, 0)), some (42, (3, 0)), some (48, (3, 0)), some (46, (3, 0))],
      ![none, some (44, (4, 0)), some (47, (4, 0)), some (46, (4, 0)), some (48, (4, 0)), some (45, (4, 0)), some (42, (4, 0)), some (43, (4, 0))],
      ![none, some (45, (5, 0)), some (44, (5, 0)), some (48, (5, 0)), some (47, (5, 0)), some (43, (5, 0)), some (46, (5, 0)), some (42, (5, 0))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (49, (0, 0)), some (50, (0, 0)), some (51, (0, 0)), some (52, (0, 0)), some (53, (0, 0)), some (54, (0, 0)), some (55, (0, 0))],
      ![none, some (53, (0, 4)), some (49, (0, 4)), some (52, (0, 4)), some (50, (0, 4)), some (55, (0, 4)), some (51, (0, 4)), some (54, (0, 4))],
      ![none, some (54, (0, 5)), some (55, (0, 5)), some (49, (0, 5)), some (53, (0, 5)), some (51, (0, 5)), some (50, (0, 5)), some (52, (0, 5))],
      ![none, some (55, (0, 6)), some (53, (0, 6)), some (50, (0, 6)), some (49, (0, 6)), some (54, (0, 6)), some (52, (0, 6)), some (51, (0, 6))],
      ![none, some (50, (0, 1)), some (52, (0, 1)), some (54, (0, 1)), some (51, (0, 1)), some (49, (0, 1)), some (55, (0, 1)), some (53, (0, 1))],
      ![none, some (51, (0, 2)), some (54, (0, 2)), some (53, (0, 2)), some (55, (0, 2)), some (52, (0, 2)), some (49, (0, 2)), some (50, (0, 2))],
      ![none, some (52, (0, 3)), some (51, (0, 3)), some (55, (0, 3)), some (54, (0, 3)), some (50, (0, 3)), some (53, (0, 3)), some (49, (0, 3))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (56, (0, 0)), some (57, (0, 0)), some (58, (0, 0)), some (59, (0, 0)), some (60, (0, 0)), some (61, (0, 0)), some (62, (0, 0))],
      ![none, some (60, (0, 3)), some (56, (0, 3)), some (59, (0, 3)), some (57, (0, 3)), some (62, (0, 3)), some (58, (0, 3)), some (61, (0, 3))],
      ![none, some (61, (0, 4)), some (62, (0, 4)), some (56, (0, 4)), some (60, (0, 4)), some (58, (0, 4)), some (57, (0, 4)), some (59, (0, 4))],
      ![none, some (62, (0, 5)), some (60, (0, 5)), some (57, (0, 5)), some (56, (0, 5)), some (61, (0, 5)), some (59, (0, 5)), some (58, (0, 5))],
      ![none, some (57, (0, 6)), some (59, (0, 6)), some (61, (0, 6)), some (58, (0, 6)), some (56, (0, 6)), some (62, (0, 6)), some (60, (0, 6))],
      ![none, some (58, (0, 1)), some (61, (0, 1)), some (60, (0, 1)), some (62, (0, 1)), some (59, (0, 1)), some (56, (0, 1)), some (57, (0, 1))],
      ![none, some (59, (0, 2)), some (58, (0, 2)), some (62, (0, 2)), some (61, (0, 2)), some (57, (0, 2)), some (60, (0, 2)), some (56, (0, 2))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (63, (0, 0)), some (64, (0, 0)), some (65, (0, 0)), some (66, (0, 0)), some (67, (0, 0)), some (68, (0, 0)), some (69, (0, 0))],
      ![none, some (67, (0, 6)), some (63, (0, 6)), some (66, (0, 6)), some (64, (0, 6)), some (69, (0, 6)), some (65, (0, 6)), some (68, (0, 6))],
      ![none, some (68, (0, 1)), some (69, (0, 1)), some (63, (0, 1)), some (67, (0, 1)), some (65, (0, 1)), some (64, (0, 1)), some (66, (0, 1))],
      ![none, some (69, (0, 2)), some (67, (0, 2)), some (64, (0, 2)), some (63, (0, 2)), some (68, (0, 2)), some (66, (0, 2)), some (65, (0, 2))],
      ![none, some (64, (0, 3)), some (66, (0, 3)), some (68, (0, 3)), some (65, (0, 3)), some (63, (0, 3)), some (69, (0, 3)), some (67, (0, 3))],
      ![none, some (65, (0, 4)), some (68, (0, 4)), some (67, (0, 4)), some (69, (0, 4)), some (66, (0, 4)), some (63, (0, 4)), some (64, (0, 4))],
      ![none, some (66, (0, 5)), some (65, (0, 5)), some (69, (0, 5)), some (68, (0, 5)), some (64, (0, 5)), some (67, (0, 5)), some (63, (0, 5))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (70, (0, 0)), some (71, (0, 0)), some (72, (0, 0)), some (73, (0, 0)), some (74, (0, 0)), some (75, (0, 0)), some (76, (0, 0))],
      ![none, some (74, (0, 1)), some (70, (0, 1)), some (73, (0, 1)), some (71, (0, 1)), some (76, (0, 1)), some (72, (0, 1)), some (75, (0, 1))],
      ![none, some (75, (0, 2)), some (76, (0, 2)), some (70, (0, 2)), some (74, (0, 2)), some (72, (0, 2)), some (71, (0, 2)), some (73, (0, 2))],
      ![none, some (76, (0, 3)), some (74, (0, 3)), some (71, (0, 3)), some (70, (0, 3)), some (75, (0, 3)), some (73, (0, 3)), some (72, (0, 3))],
      ![none, some (71, (0, 4)), some (73, (0, 4)), some (75, (0, 4)), some (72, (0, 4)), some (70, (0, 4)), some (76, (0, 4)), some (74, (0, 4))],
      ![none, some (72, (0, 5)), some (75, (0, 5)), some (74, (0, 5)), some (76, (0, 5)), some (73, (0, 5)), some (70, (0, 5)), some (71, (0, 5))],
      ![none, some (73, (0, 6)), some (72, (0, 6)), some (76, (0, 6)), some (75, (0, 6)), some (71, (0, 6)), some (74, (0, 6)), some (70, (0, 6))]],
    ![![none, none, none, none, none, none, none, none],
      ![none, some (77, (0, 0)), some (78, (0, 0)), some (79, (0, 0)), some (80, (0, 0)), some (81, (0, 0)), some (82, (0, 0)), some (83, (0, 0))],
      ![none, some (81, (1, 0)), some (77, (1, 0)), some (80, (1, 0)), some (78, (1, 0)), some (83, (1, 0)), some (79, (1, 0)), some (82, (1, 0))],
      ![none, some (82, (2, 0)), some (83, (2, 0)), some (77, (2, 0)), some (81, (2, 0)), some (79, (2, 0)), some (78, (2, 0)), some (80, (2, 0))],
      ![none, some (83, (3, 0)), some (81, (3, 0)), some (78, (3, 0)), some (77, (3, 0)), some (82, (3, 0)), some (80, (3, 0)), some (79, (3, 0))],
      ![none, some (78, (4, 0)), some (80, (4, 0)), some (82, (4, 0)), some (79, (4, 0)), some (77, (4, 0)), some (83, (4, 0)), some (81, (4, 0))],
      ![none, some (79, (5, 0)), some (82, (5, 0)), some (81, (5, 0)), some (83, (5, 0)), some (80, (5, 0)), some (77, (5, 0)), some (78, (5, 0))],
      ![none, some (80, (6, 0)), some (79, (6, 0)), some (83, (6, 0)), some (82, (6, 0)), some (78, (6, 0)), some (81, (6, 0)), some (77, (6, 0))]]]

def inverseTransport : Fin 12 → Fin 8 → Option (Transport 12) :=
  ![![none, some (0, (0, 0)), some (0, (0, 4)), some (0, (0, 5)), some (0, (0, 6)), some (0, (0, 1)), some (0, (0, 2)), some (0, (0, 3))],
    ![none, some (1, (0, 0)), some (1, (0, 2)), some (1, (0, 3)), some (1, (0, 4)), some (1, (0, 5)), some (1, (0, 6)), some (1, (0, 1))],
    ![none, some (2, (0, 0)), some (2, (0, 3)), some (2, (0, 4)), some (2, (0, 5)), some (2, (0, 6)), some (2, (0, 1)), some (2, (0, 2))],
    ![none, some (3, (0, 0)), some (3, (0, 3)), some (3, (0, 4)), some (3, (0, 5)), some (3, (0, 6)), some (3, (0, 1)), some (3, (0, 2))],
    ![none, some (4, (0, 0)), some (4, (0, 6)), some (4, (0, 1)), some (4, (0, 2)), some (4, (0, 3)), some (4, (0, 4)), some (4, (0, 5))],
    ![none, some (5, (0, 0)), some (5, (0, 1)), some (5, (0, 2)), some (5, (0, 3)), some (5, (0, 4)), some (5, (0, 5)), some (5, (0, 6))],
    ![none, some (6, (0, 0)), some (6, (6, 0)), some (6, (1, 0)), some (6, (2, 0)), some (6, (3, 0)), some (6, (4, 0)), some (6, (5, 0))],
    ![none, some (7, (0, 0)), some (7, (0, 4)), some (7, (0, 5)), some (7, (0, 6)), some (7, (0, 1)), some (7, (0, 2)), some (7, (0, 3))],
    ![none, some (8, (0, 0)), some (8, (0, 3)), some (8, (0, 4)), some (8, (0, 5)), some (8, (0, 6)), some (8, (0, 1)), some (8, (0, 2))],
    ![none, some (9, (0, 0)), some (9, (0, 6)), some (9, (0, 1)), some (9, (0, 2)), some (9, (0, 3)), some (9, (0, 4)), some (9, (0, 5))],
    ![none, some (10, (0, 0)), some (10, (0, 1)), some (10, (0, 2)), some (10, (0, 3)), some (10, (0, 4)), some (10, (0, 5)), some (10, (0, 6))],
    ![none, some (11, (0, 0)), some (11, (1, 0)), some (11, (2, 0)), some (11, (3, 0)), some (11, (4, 0)), some (11, (5, 0)), some (11, (6, 0))]]

end Kourovka.Problem2153.WilsonModel.RootData.Relations

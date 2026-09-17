import Kourovka.Problem2153.RankOne.Words
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000
namespace Kourovka.Problem2153.RootSystem.RankOne
open WilsonModel Field8 F8
def rInput : Fin 63 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (4, 5), (4, 6), (4, 7), (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5), (5, 6), (5, 7), (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5), (6, 6), (6, 7), (7, 0), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 7)]

def rLeft : Fin 63 → Fin 8 × Fin 8 :=
  ![(1, 1), (6, 5), (7, 6), (2, 7), (3, 2), (4, 3), (5, 4), (1, 0), (0, 1), (6, 7), (4, 1), (2, 3), (6, 1), (4, 5), (2, 1), (5, 0), (1, 7), (2, 4), (1, 4), (2, 2), (3, 1), (3, 4), (0, 4), (6, 0), (2, 5), (0, 5), (7, 4), (2, 6), (7, 5), (5, 5), (5, 7), (7, 0), (1, 3), (5, 6), (0, 6), (4, 6), (1, 6), (4, 4), (5, 1), (2, 0), (4, 7), (7, 7), (7, 3), (0, 7), (3, 6), (4, 2), (3, 7), (3, 0), (1, 5), (6, 6), (7, 1), (7, 2), (0, 2), (6, 2), (1, 2), (4, 0), (6, 3), (6, 4), (5, 3), (3, 3), (3, 5), (0, 3), (5, 2)]

def rRight : Fin 63 → Fin 8 × Fin 8 :=
  ![(1, 0), (6, 0), (7, 0), (2, 0), (3, 0), (4, 0), (5, 0), (0, 1), (1, 1), (4, 2), (6, 2), (6, 4), (2, 4), (2, 6), (4, 6), (0, 4), (3, 6), (3, 3), (2, 5), (1, 5), (2, 3), (1, 6), (5, 4), (0, 5), (7, 2), (6, 5), (2, 2), (5, 1), (5, 3), (2, 1), (7, 3), (0, 6), (5, 2), (1, 2), (7, 6), (5, 5), (4, 7), (1, 7), (4, 5), (0, 7), (3, 4), (4, 1), (3, 5), (2, 7), (4, 4), (7, 1), (7, 5), (0, 2), (7, 4), (1, 3), (6, 7), (1, 4), (3, 2), (7, 7), (6, 3), (0, 3), (5, 6), (3, 1), (3, 7), (6, 1), (5, 7), (4, 3), (6, 6)]

def rTorus : Fin 63 → Fin 7 × Fin 7 :=
  ![(0, 0), (0, 5), (0, 6), (0, 1), (0, 2), (0, 3), (0, 4), (0, 0), (0, 0), (0, 4), (0, 4), (0, 6), (0, 6), (0, 2), (0, 2), (0, 4), (0, 5), (0, 6), (0, 3), (0, 3), (0, 6), (0, 5), (0, 4), (0, 5), (0, 3), (0, 5), (0, 3), (0, 2), (0, 0), (0, 2), (0, 0), (0, 6), (0, 1), (0, 1), (0, 6), (0, 2), (0, 5), (0, 5), (0, 2), (0, 1), (0, 5), (0, 4), (0, 0), (0, 1), (0, 5), (0, 4), (0, 0), (0, 2), (0, 3), (0, 1), (0, 4), (0, 3), (0, 2), (0, 4), (0, 1), (0, 3), (0, 1), (0, 6), (0, 0), (0, 6), (0, 0), (0, 3), (0, 1)]

def r_lhs : Fin 63 → List Atom :=
  ![[Atom.rho, Atom.root 1 0, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 0, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 1, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 2, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 3, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 4, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 5, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 6, Atom.root 3 7, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 0, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 1, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 2, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 3, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 4, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 5, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 6, Atom.rho],
    [Atom.rho, Atom.root 1 7, Atom.root 3 7, Atom.rho]]

def r_rhs : Fin 63 → List Atom :=
  ![[Atom.root 1 1, Atom.root 3 1, Atom.torus 0 0, Atom.rho, Atom.root 1 1, Atom.root 3 0],
    [Atom.root 1 6, Atom.root 3 5, Atom.torus 0 5, Atom.rho, Atom.root 1 6, Atom.root 3 0],
    [Atom.root 1 7, Atom.root 3 6, Atom.torus 0 6, Atom.rho, Atom.root 1 7, Atom.root 3 0],
    [Atom.root 1 2, Atom.root 3 7, Atom.torus 0 1, Atom.rho, Atom.root 1 2, Atom.root 3 0],
    [Atom.root 1 3, Atom.root 3 2, Atom.torus 0 2, Atom.rho, Atom.root 1 3, Atom.root 3 0],
    [Atom.root 1 4, Atom.root 3 3, Atom.torus 0 3, Atom.rho, Atom.root 1 4, Atom.root 3 0],
    [Atom.root 1 5, Atom.root 3 4, Atom.torus 0 4, Atom.rho, Atom.root 1 5, Atom.root 3 0],
    [Atom.root 1 1, Atom.root 3 0, Atom.torus 0 0, Atom.rho, Atom.root 1 0, Atom.root 3 1],
    [Atom.root 1 0, Atom.root 3 1, Atom.torus 0 0, Atom.rho, Atom.root 1 1, Atom.root 3 1],
    [Atom.root 1 6, Atom.root 3 7, Atom.torus 0 4, Atom.rho, Atom.root 1 4, Atom.root 3 2],
    [Atom.root 1 4, Atom.root 3 1, Atom.torus 0 4, Atom.rho, Atom.root 1 6, Atom.root 3 2],
    [Atom.root 1 2, Atom.root 3 3, Atom.torus 0 6, Atom.rho, Atom.root 1 6, Atom.root 3 4],
    [Atom.root 1 6, Atom.root 3 1, Atom.torus 0 6, Atom.rho, Atom.root 1 2, Atom.root 3 4],
    [Atom.root 1 4, Atom.root 3 5, Atom.torus 0 2, Atom.rho, Atom.root 1 2, Atom.root 3 6],
    [Atom.root 1 2, Atom.root 3 1, Atom.torus 0 2, Atom.rho, Atom.root 1 4, Atom.root 3 6],
    [Atom.root 1 5, Atom.root 3 0, Atom.torus 0 4, Atom.rho, Atom.root 1 0, Atom.root 3 4],
    [Atom.root 1 1, Atom.root 3 7, Atom.torus 0 5, Atom.rho, Atom.root 1 3, Atom.root 3 6],
    [Atom.root 1 2, Atom.root 3 4, Atom.torus 0 6, Atom.rho, Atom.root 1 3, Atom.root 3 3],
    [Atom.root 1 1, Atom.root 3 4, Atom.torus 0 3, Atom.rho, Atom.root 1 2, Atom.root 3 5],
    [Atom.root 1 2, Atom.root 3 2, Atom.torus 0 3, Atom.rho, Atom.root 1 1, Atom.root 3 5],
    [Atom.root 1 3, Atom.root 3 1, Atom.torus 0 6, Atom.rho, Atom.root 1 2, Atom.root 3 3],
    [Atom.root 1 3, Atom.root 3 4, Atom.torus 0 5, Atom.rho, Atom.root 1 1, Atom.root 3 6],
    [Atom.root 1 0, Atom.root 3 4, Atom.torus 0 4, Atom.rho, Atom.root 1 5, Atom.root 3 4],
    [Atom.root 1 6, Atom.root 3 0, Atom.torus 0 5, Atom.rho, Atom.root 1 0, Atom.root 3 5],
    [Atom.root 1 2, Atom.root 3 5, Atom.torus 0 3, Atom.rho, Atom.root 1 7, Atom.root 3 2],
    [Atom.root 1 0, Atom.root 3 5, Atom.torus 0 5, Atom.rho, Atom.root 1 6, Atom.root 3 5],
    [Atom.root 1 7, Atom.root 3 4, Atom.torus 0 3, Atom.rho, Atom.root 1 2, Atom.root 3 2],
    [Atom.root 1 2, Atom.root 3 6, Atom.torus 0 2, Atom.rho, Atom.root 1 5, Atom.root 3 1],
    [Atom.root 1 7, Atom.root 3 5, Atom.torus 0 0, Atom.rho, Atom.root 1 5, Atom.root 3 3],
    [Atom.root 1 5, Atom.root 3 5, Atom.torus 0 2, Atom.rho, Atom.root 1 2, Atom.root 3 1],
    [Atom.root 1 5, Atom.root 3 7, Atom.torus 0 0, Atom.rho, Atom.root 1 7, Atom.root 3 3],
    [Atom.root 1 7, Atom.root 3 0, Atom.torus 0 6, Atom.rho, Atom.root 1 0, Atom.root 3 6],
    [Atom.root 1 1, Atom.root 3 3, Atom.torus 0 1, Atom.rho, Atom.root 1 5, Atom.root 3 2],
    [Atom.root 1 5, Atom.root 3 6, Atom.torus 0 1, Atom.rho, Atom.root 1 1, Atom.root 3 2],
    [Atom.root 1 0, Atom.root 3 6, Atom.torus 0 6, Atom.rho, Atom.root 1 7, Atom.root 3 6],
    [Atom.root 1 4, Atom.root 3 6, Atom.torus 0 2, Atom.rho, Atom.root 1 5, Atom.root 3 5],
    [Atom.root 1 1, Atom.root 3 6, Atom.torus 0 5, Atom.rho, Atom.root 1 4, Atom.root 3 7],
    [Atom.root 1 4, Atom.root 3 4, Atom.torus 0 5, Atom.rho, Atom.root 1 1, Atom.root 3 7],
    [Atom.root 1 5, Atom.root 3 1, Atom.torus 0 2, Atom.rho, Atom.root 1 4, Atom.root 3 5],
    [Atom.root 1 2, Atom.root 3 0, Atom.torus 0 1, Atom.rho, Atom.root 1 0, Atom.root 3 7],
    [Atom.root 1 4, Atom.root 3 7, Atom.torus 0 5, Atom.rho, Atom.root 1 3, Atom.root 3 4],
    [Atom.root 1 7, Atom.root 3 7, Atom.torus 0 4, Atom.rho, Atom.root 1 4, Atom.root 3 1],
    [Atom.root 1 7, Atom.root 3 3, Atom.torus 0 0, Atom.rho, Atom.root 1 3, Atom.root 3 5],
    [Atom.root 1 0, Atom.root 3 7, Atom.torus 0 1, Atom.rho, Atom.root 1 2, Atom.root 3 7],
    [Atom.root 1 3, Atom.root 3 6, Atom.torus 0 5, Atom.rho, Atom.root 1 4, Atom.root 3 4],
    [Atom.root 1 4, Atom.root 3 2, Atom.torus 0 4, Atom.rho, Atom.root 1 7, Atom.root 3 1],
    [Atom.root 1 3, Atom.root 3 7, Atom.torus 0 0, Atom.rho, Atom.root 1 7, Atom.root 3 5],
    [Atom.root 1 3, Atom.root 3 0, Atom.torus 0 2, Atom.rho, Atom.root 1 0, Atom.root 3 2],
    [Atom.root 1 1, Atom.root 3 5, Atom.torus 0 3, Atom.rho, Atom.root 1 7, Atom.root 3 4],
    [Atom.root 1 6, Atom.root 3 6, Atom.torus 0 1, Atom.rho, Atom.root 1 1, Atom.root 3 3],
    [Atom.root 1 7, Atom.root 3 1, Atom.torus 0 4, Atom.rho, Atom.root 1 6, Atom.root 3 7],
    [Atom.root 1 7, Atom.root 3 2, Atom.torus 0 3, Atom.rho, Atom.root 1 1, Atom.root 3 4],
    [Atom.root 1 0, Atom.root 3 2, Atom.torus 0 2, Atom.rho, Atom.root 1 3, Atom.root 3 2],
    [Atom.root 1 6, Atom.root 3 2, Atom.torus 0 4, Atom.rho, Atom.root 1 7, Atom.root 3 7],
    [Atom.root 1 1, Atom.root 3 2, Atom.torus 0 1, Atom.rho, Atom.root 1 6, Atom.root 3 3],
    [Atom.root 1 4, Atom.root 3 0, Atom.torus 0 3, Atom.rho, Atom.root 1 0, Atom.root 3 3],
    [Atom.root 1 6, Atom.root 3 3, Atom.torus 0 1, Atom.rho, Atom.root 1 5, Atom.root 3 6],
    [Atom.root 1 6, Atom.root 3 4, Atom.torus 0 6, Atom.rho, Atom.root 1 3, Atom.root 3 1],
    [Atom.root 1 5, Atom.root 3 3, Atom.torus 0 0, Atom.rho, Atom.root 1 3, Atom.root 3 7],
    [Atom.root 1 3, Atom.root 3 3, Atom.torus 0 6, Atom.rho, Atom.root 1 6, Atom.root 3 1],
    [Atom.root 1 3, Atom.root 3 5, Atom.torus 0 0, Atom.rho, Atom.root 1 5, Atom.root 3 7],
    [Atom.root 1 0, Atom.root 3 3, Atom.torus 0 3, Atom.rho, Atom.root 1 4, Atom.root 3 3],
    [Atom.root 1 5, Atom.root 3 2, Atom.torus 0 1, Atom.rho, Atom.root 1 6, Atom.root 3 6]]

def sInput : Fin 7 → Fin 8 :=
  ![1, 2, 3, 4, 5, 6, 7]

def sLeft : Fin 7 → Fin 8 :=
  ![1, 5, 6, 7, 2, 3, 4]

def sRight : Fin 7 → Fin 8 :=
  ![1, 5, 6, 7, 2, 3, 4]

def sTorus : Fin 7 → Fin 7 × Fin 7 :=
  ![(0, 0), (1, 4), (2, 5), (3, 6), (4, 1), (5, 2), (6, 3)]

def s_lhs : Fin 7 → List Atom :=
  ![[Atom.sigma, Atom.root 0 1, Atom.sigma],
    [Atom.sigma, Atom.root 0 2, Atom.sigma],
    [Atom.sigma, Atom.root 0 3, Atom.sigma],
    [Atom.sigma, Atom.root 0 4, Atom.sigma],
    [Atom.sigma, Atom.root 0 5, Atom.sigma],
    [Atom.sigma, Atom.root 0 6, Atom.sigma],
    [Atom.sigma, Atom.root 0 7, Atom.sigma]]

def s_rhs : Fin 7 → List Atom :=
  ![[Atom.root 0 1, Atom.torus 0 0, Atom.sigma, Atom.root 0 1],
    [Atom.root 0 5, Atom.torus 1 4, Atom.sigma, Atom.root 0 5],
    [Atom.root 0 6, Atom.torus 2 5, Atom.sigma, Atom.root 0 6],
    [Atom.root 0 7, Atom.torus 3 6, Atom.sigma, Atom.root 0 7],
    [Atom.root 0 2, Atom.torus 4 1, Atom.sigma, Atom.root 0 2],
    [Atom.root 0 3, Atom.torus 5 2, Atom.sigma, Atom.root 0 3],
    [Atom.root 0 4, Atom.torus 6 3, Atom.sigma, Atom.root 0 4]]

end Kourovka.Problem2153.RootSystem.RankOne

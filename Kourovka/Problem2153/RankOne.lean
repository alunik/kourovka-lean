import Kourovka.Problem2153.RankOne.CellIdentities
import Kourovka.Problem2153.RankOne.Radicals
import Kourovka.Problem2153.RankOne.Orientation
import Kourovka.Problem2153.RankOne.Nondegenerate

/-!
Concrete rank-one inputs for the Wilson matrix group's BN-pair:

* all 70 nonidentity rank-one cells, checked as sparse matrix word identities;
* the full-parameter simple Weyl action, deduced from 21 checked base identities;
* preservation of the two positive radicals by their simple reflections;
* both Bruhat orientations for all 16 actual Weyl representatives.

The subgroup-cover premises in `r_rankOne_of_coverage` and
`s_rankOne_of_coverage` are supplied separately by `RootCollection`.
-/

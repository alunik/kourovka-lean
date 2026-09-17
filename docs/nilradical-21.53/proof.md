> Publication note, 17 September 2026: this report is preserved at its review-time scope. Later technical and human gates passed; see [the current record](README.md). Machine-local path prefixes are removed in this public copy.

# A constructive matrix route for Kourovka 21.53

*Status snapshot: 16 September 2026, updated after the concrete BN-pair and final theorem compiled. The formal mathematical endpoint is closed; independent semantic review is in progress.*

The object under study is an explicitly generated finite matrix group. The local matrix identities, finite rank-one identities, unipotent factorizations, concrete BN-pair and Bruhat coverage, projective-frame argument, normal generation, perfectness, simplicity, and whole-class transposition have all been assembled. The final source contains unconditional theorems `whole_class_counterexample` and `not_statement : ¬ Statement.{0}`. Their reported axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. This supplement explains the mathematics for independent review; a successful formal build does not by itself settle whether the formal statement matches the intended informal problem.

The route does not require recognition of the generated group as a named Ree group, an exact formula for its order, or a classification theorem. The point is to prove the properties needed for the counterexample directly for one finite subgroup of a standard general linear group.

## 1. The carrier and the finite certificates

Let

\[
 F=\mathbf F_2[\omega]/(\omega^3+\omega+1).
\]

The implementation constructs this as a genuine eight-element field, with elements encoded by the binary coefficients of $1,\omega,\omega^2$. Thus code $2$ denotes $\omega$; a code is not an exponent of $\omega$. Let $V=F^{26}$, with row vectors acting on the right, and use the convention

\[
 a^g=g^{-1}ag,\qquad [a,b]=a^{-1}b^{-1}ab.
\]

Take the explicit matrices $t,x,r,s,h(\alpha,\beta)$, where $r=\rho$, $s=\sigma$ and $\alpha,\beta\in F^\times$, transcribed in the recorded ordered basis. Define

\[
 G=\langle t,x,r,s,h(\alpha,\beta):\alpha,\beta\in F^\times\rangle
 \leqslant \operatorname{GL}_{26}(F).
\]

All these are actual units of the matrix algebra: their inverse certificates are proved, and $G$ is the ordinary subgroup closure. Its finiteness follows immediately from finiteness of $F$ and the dimension. There is no assumed embedding or assumed abstract group model.

The source of the matrices is Robert A. Wilson's *A simple construction of the Ree groups of type ${}^2F_4$*, author draft dated 5 June 2009, especially the coordinate permutations and root generators on pages 3, 6 and 7. The draft is available from [Wilson's site](https://webspace.maths.qmul.ac.uk/r.a.wilson/pubs_files/ReeF4alg.pdf); the published article is J. Algebra 323 (2010), 1468–1481, [DOI 10.1016/j.jalgebra.2009.11.015](https://doi.org/10.1016/j.jalgebra.2009.11.015). The present verification uses his matrices, not his simplicity theorem as an axiom. Wilson credits K. Coolsaet's earlier description in *Algebraic structure of the perfect Ree–Tits generalized octagons*, Innovations in Incidence Geometry 1 (2005), 67–131, [DOI 10.2140/iig.2005.1.67](https://doi.org/10.2140/iig.2005.1.67), including explicit root elements and parabolic generators. The underlying Ree construction and simplicity results are prior mathematics; this campaign's proposed new mathematical contribution concerns Problem 21.53.

Python computations produced candidate certificate data. Lean proves a generic sparse-row multiplication checker sound with respect to ordinary matrix multiplication, checks each finite certificate by kernel reduction, and transfers its equality through the injective map from the actual subgroup to matrices. In particular, a Python equality or a JSON record is never itself a proof premise.

The key foundational checks give

\[
 |t|=|r|=|s|=2,\quad |x|=4,\quad |ts|=3.
\]

Every generator has determinant one. For the generators of order $2$ or $4$, this follows because their determinants have orders dividing both that order and $|F^\times|=7$. The 49 diagonal torus determinants are checked directly. Consequently every element of $G$ has determinant one. The order-two and order-three elements show that 2 and 3 divide $|G|$, so they are its two smallest prime divisors. No exact computation of $|G|$ is needed.

## 2. Root collection and the finite rank-one structure

Define twelve parameterized root curves $R_i(a)$, with $R_i(0)=1$, by torus conjugation of the following bases. The characters are taken modulo 7.

| $i$ | $R_i(1)$ | Torus character $(p_i,q_i)$ |
|---:|---|---:|
|0|$t$|$1,6$|
|1|$x$|$4,5$|
|2|$x^s$|$5,4$|
|3|$x^2$|$6,4$|
|4|$x^{sr}$|$0,3$|
|5|$t^r$|$4,1$|
|6|$x^{srs}$|$3,0$|
|7|$(x^2)^s$|$4,6$|
|8|$t^{rs}$|$1,4$|
|9|$t^{rsr}$|$3,3$|
|10|$(x^2)^{sr}$|$0,1$|
|11|$(x^2)^{srs}$|$1,0$|

These are definitions in $G$, using the recorded canonical torus section for each nonzero parameter. All 96 resulting matrices are proved equal to the separately stored sparse matrices. The full covariance theorem is

\[
 R_i(a)^{h(\alpha,\beta)}
   =R_i(\alpha^{p_i}\beta^{q_i}a).
\]

Its proof uses twelve checked kernel-generator commutations, the torus multiplication law, and finite scalar identities. It does not require 4704 independent matrix multiplications.

Put $U=\langle R_i(a):0\leq i<12,\ a\in F\rangle$. The collection relations have the following precise shape:

* $R_i(a)^{-1}$ and $R_i(a)R_i(b)$ are ordered products of curves with indices at least $i$.
* For $i<j$, $[R_i(a),R_j(b)]$ is an ordered product with indices strictly greater than $j$.

A curve need not be a subgroup by itself; the later-coordinate corrections in the first clause matter. The complete families have 96 inverse, 768 same-curve product, and 4224 commutator parameter cases. Torus transport reduces their nontrivial certificate workload to 12, 84 and 90 representatives respectively. All 186 representative identities are proved in the actual group; the finite selectors and torus covariance expand them to the full relations. An additional 21 checked positive simple-Weyl identities expand to 168 parameter cases. Thus the reduced collection/Weyl workload is 207 group identities, plus the twelve kernel commutations.

The generic ordered-collection theorem turns these support conditions into an existence statement

\[
 U=\{R_0(a_0)R_1(a_1)\cdots R_{11}(a_{11}):a_i\in F\}.
\]

The final route does not need this full twelve-coordinate coverage statement as a separate theorem: the two unipotent factorizations below have a shorter direct proof. In either approach, uniqueness of coordinates and enumeration of all $8^{12}$ tuples are unnecessary.

Let

\[
 H=\langle h(\alpha,\beta)\rangle,\quad W=\langle r,s\rangle,
 \quad B=U H,\quad N=H W.
\]

Here $B,N$ are formally defined as subgroup joins; the displayed product descriptions are proved consequences. The torus has 49 representatives. Its conjugation laws are

\[
 h(\alpha,\beta)^r=h(\alpha,\alpha^4/\beta),\qquad
 h(\alpha,\beta)^s=h(\beta,\alpha).
\]

The 16 recorded Weyl words are proved to enumerate the actual subgroup $W$, using 32 generator transitions and distinctness checks. The root matrices are lower unitriangular, the torus is diagonal, and only the identity Weyl representative is lower triangular. It follows that $B\cap N=H$. Also $B,N$ generate $G$, because they contain every defining generator. These intersection, factorization and generation facts are already proved.

For the two rank-one factors put

\[
 R_r=\{R_1(a)R_3(b):a,b\in F\},\qquad
 R_s=\{R_0(a):a\in F\}.
\]

Their subgroup-closure definitions are proved to have exactly these parameter covers. Let $V_r$ be generated by the curves other than 1 and 3, and $V_s$ by the curves other than 0. The proved unipotent factorizations are

\[
 U=R_rV_r=R_sV_s.
\]

The direct proof checks that coordinates 0, 1 and 3 vanish in each of the 90 commutator representatives, then transports this fact to all distinct-root commutators. Thus conjugation by the rank-one generators preserves the corresponding radical. Because each conjugating element has finite order, stability in one direction also gives stability under inverse conjugation. Consequently $R_r$ normalizes $V_r$, and $R_s$ normalizes $V_s$. Every root generator belongs to the appropriate rank-one factor or radical, so $U=R_r\vee V_r=R_s\vee V_s$; the usual product description of a join with a normalizing factor gives the displayed factorizations. This is an actual proof in `UnipotentFactorization.lean`, not an assumed radical normality statement. Torus normalization and conjugation of the radical by its corresponding simple reflection are separately proved.

There are 63 nonzero parameter pairs for $R_r$ and seven nonzero parameters for $R_s$. All 70 identities of the form

\[
 n u n=u_1 h n u_2\qquad(n=r\text{ or }s)
\]

are checked on the full 26-dimensional matrices. The auxiliary small blocks used to discover them have no role in the proof of equality. The actual group identities imply the required rank-one two-cell formula after conjugating the torus factor across $n$.

For each of the 16 Weyl representatives and each of $r,s$, a proved orientation choice gives either

\[
 wR_nw^{-1}\subseteq U
 \quad\text{or}\quad
 (wn)R_n(wn)^{-1}\subseteq U.
\]

The Lean proof uses 32 orientation choices and 48 finite root-index paths, with every path step backed by a proved root-conjugation identity. It does not replay the exploratory 1152 full-matrix orientation images. Torus normalization extends the choices from $w$ to arbitrary representatives in $N=HW$.

## 3. The concrete BN-pair and Bruhat coverage

The finite ingredients above supply the Tits multiplication axiom

\[
 (BwB)(BnB)\subseteq BwnB\ \cup\ BwB,
 \qquad n\in\{r,s\}.
\]

The generic proof factors a middle Borel element using $U=R_nV_n$, moves the radical past $n$, applies the rank-one formula, and uses the orientation alternative to absorb a positive root factor. An inversion lemma gives the corresponding left-multiplication convention. Two explicit nonzero entries above the diagonal prove that $r x r^{-1}\notin B$ and $s t s^{-1}\notin B$, which supplies nondegeneracy.

The abstract BN-pair definition and Bruhat theorem are reused from [TauCetiProject/TauCeti at commit ede1468fb951c5117f1462008216ceb13214e29f](https://github.com/TauCetiProject/TauCeti/tree/ede1468fb951c5117f1462008216ceb13214e29f/TauCeti/GroupTheory/TitsSystem), under Apache-2.0. The vendored `External/TitsSystem/PROVENANCE.json` records the exact upstream paths and original/local SHA256 values. The dependency has been compiled against this campaign's pinned Lean/mathlib versions. It proves an abstract theorem; it supplies none of the concrete matrix-group hypotheses automatically.

The construction `BNPair.concrete` supplies every field of an actual `TauCeti.TitsSystem G`: generation, normality of $B\cap N$ in $N$, generation of $N/(B\cap N)$ by the images of $r,s$, their involution representatives, multiplication, and nondegeneracy. The quotient-generation and simple-representative interfaces discharge their respective fields. The public construction passes the proved `U_factor_r` and `U_factor_s` into the generic construction; there is no assumed coverage field.

Tau Ceti's theorem therefore gives $G=BNB$. The proved $B=UH=HU$, $N=HW$, and Weyl normalization of $H$ then give the exact form used below:

\[
 \boxed{\quad g=u h w v\quad(u,v\in U,\ h\in H,\ w\in W)\quad}
\tag{BC}
\]

The local theorem `bruhatCoverage_of_titsSystem` performs this last conversion. The concrete theorem `BNPair.uhwu_coverage` now proves (BC), and `BNPair.coverage` gives the equivalent $BWB$ form used for simplicity.

## 4. A direct simplicity argument

Set $Z=\langle R_{11}(a):a\in F\rangle$ and $P=\langle B,r\rangle$. The root relations already prove that $Z$ is abelian and that $U$ centralizes $Z$. Torus covariance normalizes $Z$, and $r$ centralizes it. Therefore $P$ normalizes $Z$.

The group $P$ stabilizes the line $F e_0$, whereas $s$ moves this line. Hence $P<G$. No equality with the full line stabilizer is required.

The normal core of $P$ is already proved trivial. The certificate provides 27 actual vectors in the orbit of $e_0$: 26 form a basis, and the last has every coordinate nonzero in that basis. Membership in the orbit is proved by 27 words of length 48, through 1296 sparse vector transitions. Two inverse-matrix identities verify the basis matrix, and a further coordinate identity verifies the last vector.

An element of the normal core fixes every orbit line, hence these 27 lines. In the first 26 lines it is diagonal in the certified basis. Fixing the last line, whose coordinates are all nonzero, forces all diagonal entries equal. Thus it is a scalar $\lambda I$. Its determinant is one, so $\lambda^{26}=1$; also $\lambda^7=1$. Since $\gcd(26,7)=1$, it is the identity.

Maximality of $P$ follows from (BC). If $P<J\leq G$, coverage extracts a Weyl representative $w\in J\setminus P$. Fourteen finite Weyl words, one for each $w\notin\{1,r\}$, show that the longest element $w_0=(rs)^4$ lies in $\langle r,w\rangle$. The checked identity

\[
 t\,t^{w_0}\,t=s
\]

puts $s$ in $J$; as $B,r,s$ generate $G$, we obtain $J=G$. This is the content of `P_isCoatom_of_coverage`, now applied to the proved `BNPair.coverage`.

Normal generation and perfectness are already unconditional theorems about the actual $G$. Any normal subgroup containing $z=R_{11}(1)$ contains $x^2$ and its conjugates. Checked words of lengths 5, 10 and 23 in three such conjugates recover $r,h(1,\omega),x$. The identity

\[
 [x,x^{sr}]=t^r
\]

then supplies $t$, and $t\,t^s\,t=s$ supplies $s$. Conjugating $h(1,\omega)$ by $s$ supplies $h(\omega,1)$. The two torus generators give all 49 torus elements. Hence the normal closure of $Z$ is $G$.

Finally the checked commutator

\[
 [R_{11}(c),h(\omega,1)]=R_{11}(1),
 \qquad c=\omega+\omega^2\quad\text{(field code 6)},
\]

puts $z$ in the derived subgroup. Its normal generation gives $G'=G$.

The Iwasawa argument completing simplicity is elementary. If a normal subgroup $K$ lies in $P$, it lies in the trivial normal core. Otherwise maximality gives $KP=G$. Since $P$ normalizes $Z$, the subgroup $KZ$ is then normal in $G$; normal generation of $Z$ forces $KZ=G$. Thus $G/K$ is an image of the abelian group $Z$, and perfectness forces $K=G$. This generic argument is proved in `isSimpleGroup_of_iwasawa_subgroups`. The instance `RootSystem.ambient_isSimpleGroup` in `Simple.lean` applies it with the proved concrete inputs and has no remaining mathematical premise.

## 5. Whole-class tests and the transposition

Take

\[
 X=z=R_{11}(1),\qquad
 Y=z^{h(\omega,1)}=R_{11}(\omega),\qquad
 A=z^{srsrsrs}.
\]

The matrices certify that these are distinct where required, all have order two, belong to the same actual $G$-conjugacy class, and satisfy

\[
 |AX|=5,\qquad |AY|=7.
\]

The whole-class argument has two finite inputs, both now proved in the actual group.

First, for every nonzero parameter $a$, torus element $h$, and Weyl representative $w$, the commutation predicates for $R_{11}(a)$ and $X$ against $hw$ coincide. Since the last root has character $(1,0)$, the second torus parameter drops out. There are 784 checked Boolean cases: seven nonzero root parameters, seven first torus parameters, and sixteen Weyl representatives. The soundness proof identifies these Boolean matrix tests with group commutation.

Second, none of the products

\[
 X\,R_{11}(a)^w\qquad(a\ne0,\ w\in W)
\]

has order three. The 112 cases reduce to 56 under left multiplication of $w$ by $r$, which centralizes $R_{11}(a)$. Sparse addition-chain certificates prove that each product has a power equal to one with exponent in $\{1,2,4,5,7,13\}$. Therefore its order is not divisible by 3. These are certified exponent bounds; exact orders in all 112 cases are unnecessary. The exploratory Python distribution $1:2,2:68,4:28,5:2,7:6,13:6$ is not being promoted here to an additional Lean exact-order theorem. Torus covariance extends the proved no-three result to every $hw$.

Using the proved (BC), these tests extend to the whole group. Because $U$ centralizes $X,Y$, writing $g=u h w v$ gives

\[
 [X,g]=1\iff [X,hw]=1,
 \qquad [Y,g]=1\iff [Y,hw]=1.
\]

Thus $C_G(X)=C_G(Y)$. Likewise, for $d,e\in Z$,

\[
 |d\,e^{u h w v}|=|d\,e^{hw}|,
\]

by conjugating the product and using the two $U$-centrality identities. Simultaneously conjugating an arbitrary pair in the class of $X$ reduces its first member to $X$. Hence no product of two class members has order three. The generic results `same_centralizer_of_bruhat_tests` and `no_class_product_order_of_root_tests` prove precisely these extensions; their explicit coverage hypotheses are discharged in the concrete endpoint.

Let $\mathcal C=X^G$. Exchange $X,Y$ and fix every other member of $\mathcal C$. For distinct involutions, product order two is equivalent to commutation, so equal centralizers make this permutation preserve the order-two relation. It preserves the order-three relation because that relation is empty. But it sends the pair $(A,X)$ to $(A,Y)$, changing product order from 5 to 7. The generic whole-class swap theorem is already proved. The concrete coverage and simplicity applications, finiteness and the proved smallest prime divisors $2,3$ make it a counterexample to the stated universal assertion. This is the unconditional theorem `Kourovka.Problem2153.not_statement`.

## 6. Completion boundary and reproducibility

The concrete field, actual GL units, root alignment, reduced relations and transport, torus action, Weyl enumeration, 70 rank-one identities, orientation, nondegeneracy, frame/core argument, normal generation, perfectness, centralizer tests and product-power tests are closed components. The generic collection, BN-pair/Bruhat conversion, Iwasawa and whole-class swap arguments are also proved. The concrete unipotent factorizations, Tits-system assembly, whole-group coverage, and final composition are now closed as well. Full ordered twelve-coordinate coverage is not a dependency of the final endpoint.

The key source interfaces are `RootRelations.lean`, `RootCollection.lean`, `UnipotentFactorization.lean`, `Borel.lean`, `BNPair.lean`, `RankOne.lean`, `Parabolic.lean`, `ParabolicMaximal.lean`, `NormalGeneration.lean`, `NormalGeneration/RootSubgroup.lean`, `AmbientFacts/Frame.lean`, `WilsonModel/ClassTests.lean`, `BruhatReduction.lean`, `Simple.lean`, `Endpoint.lean` and `Final.lean` under `kourovka-lean/Kourovka/Problem2153/`. The generator basis and original finite data are in `lean/structural/`; exact build receipts and source hashes for the owned matrix certificates are in `lean/implementation/field8-wilson-receipt.md` and `field8-wilson-auckland/`.

The pin is Lean 4.34.0-rc2 with mathlib `87f6d5ec4c780581c9a78b06a9c5f1cf86dc5a70`. Audited matrix and class-test declarations use only `propext`, `Classical.choice` and `Quot.sound`. There are no admitted proofs, native-decision axioms or unproved matrix-equality assumptions in those modules. A fresh review should examine the actual formal statement, the original problem, the generated group and whole conjugacy-class carrier, every Tits-system field, and the finite-certificate soundness bridges. The remaining acceptance gates are separate independent mathematical and semantic reviews, a refreshed novelty assessment, protected integrity verification, and the two human decisions on the final statements and bounded novelty/contribution wording. No assumed group-theoretic premise remains to be discharged.

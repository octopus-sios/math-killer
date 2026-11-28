# Willems's Brauer degree inequality at the prime 3

**Theorem.** For every finite group $G$,

$$
\sum_{\varphi\in\operatorname{IBr}_3(G)}\varphi(1)^2\ \ge\ |G|_{3'}.
$$

This settles the prime 3 in [Kourovka Notebook 21.91](https://arxiv.org/pdf/1401.0300v50#page=192). We also verify the projective version for **all covers of finite simple groups of Lie type at all primes**, completing the defining-characteristic part. We do not claim the global inequality for $p\ge5$, or a characterization of equality.

## The reduction and the two remaining cases

Work over an algebraically closed field $k$ of characteristic $p$. Identify irreducible Brauer characters with simple modules and their degrees with dimensions. For a central $p'$-subgroup $Z$ of $X$ and a linear character $\theta$ of $Z$, write $s(X,\theta)$ for the sum of squared degrees of the simples on which $Z$ acts by $\theta$. For $Z=1$ write $s(X)$.

[Tong-Viet, Proposition 1.1](https://doi.org/10.1016/j.jalgebra.2020.01.008) reduces the global inequality at a fixed prime to showing

$$
s(X,\theta)\ \ge\ |X/Z(X)|_{p'}
\tag{1}
$$

for every quasisimple $X$ with $p'$-center and every faithful $\theta$ of its center. Here “faithful” concerns $\theta$ on $Z(X)$, including the character of the trivial center. For a general central $k$-character of a quasisimple cover, divide out its kernel (which contains the central $p$-part). The resulting quasisimple group has the same simple quotient and faithful induced central character, and inflation identifies the two sectors. When $p$ does not divide the group order the sector algebra is semisimple of dimension $|X:Z(X)|$, so (1) is automatic. The restriction to a prescribed central character matters: knowing the inequality for the simple quotient alone does not prove (1).

[Tong-Viet, Proposition 2.1](https://doi.org/10.1016/j.jalgebra.2020.01.008) handles sporadic covers and the exceptional Schur multiplier cases of Lie type. [Malle, §§3–4 and Theorem 4.3](https://arxiv.org/pdf/2012.08765) handles all Lie-type cases in non-defining characteristic and many in defining characteristic. His Theorem 2 gives the global result at $p=2$. In defining characteristic the centerless case for the standard groups of Lie type already follows from the Steinberg module, as in [Willems (2005)](https://doi.org/10.1090/S0002-9947-04-03561-5). We complete (1) for Lie type and then treat the ordinary and spin sectors for alternating groups at $p=3$.

## Putting a large degree in the required central sector

All modules below are finite dimensional. Let $S$ be a simple $kX$-module trivial on $Z$, and let $V\ne0$ be **any** module on which $Z$ acts by $\theta$. Choose a simple quotient $W$ of $S\otimes V$. It has central character $\theta$. Currying the quotient map gives a nonzero equivariant map $S\to\operatorname{Hom}_k(V,W)$, with the conjugation action on the target. Its kernel is zero by simplicity of $S$. Thus

$$
\dim W\ \ge\ \frac{\dim S}{\dim V}.
\tag{2}
$$

In particular $S\otimes V$ need not be semisimple. Take $S$ to be the Steinberg module inflated from the simple quotient. For the remaining standard covers it suffices to work on the simply connected finite group: pull back the specified central character from $X$; the central kernel of the map to $X$ acts trivially on $S\otimes V$, so the resulting $W$ factors through $X$.

By Malle's Propositions 3.2–3.4 we only need the following cases for $q$ a power of an **odd** prime. Some field sizes and ranks in these families were already treated by Malle's Lemma 3.5 and Proposition 3.6; the argument below is uniform. The order estimates are for the simply connected group, before division by its center, so an estimate using that order suffices.

* For $\mathrm{SL}_5(q)$ and $\mathrm{SU}_5(q)$, every nontrivial scalar-center character occurs on an exterior power of the natural module, of dimension at most 10. The Steinberg degree is $q^{10}$ and the $p'$-order is at most $q^{14}$. For the unitary order, pair the factors of indices $(2,3)$ and $(4,5)$, using $(q^i-1)(q^{i+1}+1)<q^{2i+1}$. Since $q^6\ge 100$, (2) suffices.
* For $\mathrm{Sp}(2r,q)$ and $\mathrm{Spin}(2r+1,q)$, $r\ge3$, the nontrivial character of the center occurs on the natural symplectic module of dimension $2r$, respectively the spin module of dimension $2^r$. In both cases $\dim V\le 2^r$. The Steinberg degree is $q^{r^2}$, and the $p'$-order is $\prod_{i=1}^r(q^{2i}-1)<q^{r(r+1)}$. The margin $q^{r(r-1)}\ge4^r$ pays for $(\dim V)^2$.
* For $\mathrm{Spin}^{\pm}(2r,q)$, $r\ge4$, use the natural module and the two algebraic half-spin modules. Their central characters are the classes of $\omega_1,\omega_{r-1},\omega_r$ in the weight lattice modulo the root lattice: these are exactly the three nonzero classes (the group is cyclic of order four for odd $r$, elementary abelian of order four for even $r$). The center of the finite simply connected spin group is the fixed subgroup of this algebraic center on $k$-points. Restriction of characters to that subgroup is onto, since $k^\times$ contains all roots of unity of order dividing four. The center acts on the entire fundamental module by the character of its highest weight, since all its weights are congruent modulo the root lattice. Thus restricting these modules to finite fixed points realizes every required nontrivial character, also for the twisted form and for central quotients. No descent of a half-spin module to a particular finite ground field is needed. Here $\dim V\le\max(2r,2^{r-1})=2^{r-1}$. The Steinberg degree is $q^{r(r-1)}$; the $p'$-order is $(q^r\mp1)\prod_{i=1}^{r-1}(q^{2i}-1)<2q^{r^2}$. Now $q^{r(r-2)}\ge2\cdot4^{r-1}$, as required.

These small modules are the defining-characteristic fundamental modules; compare [Malle–Navarro–Späth, proof of Theorem 2.5, Table 2](https://agag-malle.math.rptu.de/~malle/download/breakfast.pdf). In type $D$ one can explicitly use the root lattice of integral vectors with even coordinate sum: $e_1$ and the two half-sums $(e_1+\cdots+e_{r-1}\pm e_r)/2$ give the asserted classes. This proves (1) in all the remaining standard Lie-type cases.

For clarity, the small derived group $T={}^2F_4(2)'$ does not need a simply connected realization. Its [ATLAS order and multiplier](https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/) are $2^{11}3^3 5^2 13$ and $1$. For $p=2,3,5,13$ respectively take the ordinary degrees $2048,1728,1300,1300$ from the [character table](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/2F4%282%29%27.html). Each degree has full $p$-part (hence gives a simple modular degree), and its square exceeds $|T|_{p'}$.

## Transferring degree sums between ranks

If $Z\le H\le X$ and $Z$ is as above, then

$$
s(H,\theta)\ \le\ s(X,\theta)\ \le\ [X:H]^2s(H,\theta).
\tag{3}
$$

For the first inequality let $e$ be the central idempotent for $\theta$ and map $e kH$ into $e kX/J(e kX)$. The kernel is a nilpotent ideal, since it lies in $J(e kX)$, and hence is contained in $J(e kH)$. The image therefore surjects onto $e kH/J(e kH)$. Its dimension is at most that of $e kX/J(e kX)$, and the dimensions of the two semisimple quotients are the two degree sums. For the second inequality assign each simple $X$-module $T$ in the sector to an isomorphism class $U$ of simple submodules of its restriction to $H$. By Frobenius reciprocity $T$ is a quotient of $\operatorname{Ind}_H^X U$. For fixed $U$, the distinct assigned simples all occur in the semisimple head, so their dimensions **sum** to at most $[X:H]\dim U$. Their squared dimensions sum to at most the square of this bound. Sum over $U$. This argument makes no multiplicity-free restriction assumption.

Fix a compatible tower of Schur double covers $\widehat S_n$ (the preimage of a point stabilizer gives the smaller cover). Write $s_0(n)=s(S_n)$ and $s_1(n)$ for the genuine spin sector of $\widehat S_n$. For $p=3$ it is enough to prove

$$
s_j(n)\ge (n!)_{3'}\qquad (j=0,1;\ n\ge5).
\tag{4}
$$

Indeed passing to $A_n$ or its preimage $\widehat A_n$ divides both sides by 2. For the sums this is index-two Clifford theory: an orbit of two distinct simples of dimension $d$ induces one simple of dimension $2d$; an invariant simple has two extensions of dimension $d$ (scale an intertwiner over $k$ and use $\operatorname{char}k\ne2$). The central sign is unchanged. The multiplier of $A_n$ is of order 2, except for $n=6,7$ where it is cyclic of order 6; its $3'$-part still has order 2.

For a strict partition $\lambda$ of $m$, of length $l$, the shifted hook-length formula gives one spin degree

$$
D(\lambda)=2^{\lfloor(m-l)/2\rfloor}\frac{m!}{\prod_i\lambda_i!}
          \prod_{i<j}\frac{\lambda_i-\lambda_j}{\lambda_i+\lambda_j}.
\tag{5}
$$

There are two associates of this degree if $m-l$ is odd, one otherwise. We use the ordinary hook-length formula in the ordinary sector. The standard bar-core, degree and block facts used here are set out in [Olsson, *Combinatorics and representations of finite groups*, §§7, 11, 13](https://web.math.ku.dk/~olsson/manus/comb_rep_all.pdf).

## Two staircases and an effective infinite tail

Use the following partitions, one in each sector:

| sector | parts (decreasing) | size $m_l$ |
|---|---|---|
| ordinary | $2l,2l-2,\ldots,2$ | $l(l+1)$ |
| spin | $3l-2,3l-5,\ldots,1$ | $l(3l-1)/2$ |

Their degrees $D_l$ give **simple modular** degrees. For the ordinary staircase, the hooks in its row of length $2i$ are the numbers $3j-2,3j-1$ for $1\le j\le i$. For the spin staircase, put $u_i=3i-2$ in increasing order. In (5), $u_i+u_j$ is prime to 3 and the product $\prod_{j<i}(u_i-u_j)=3^{i-1}(i-1)!$ has the same 3-part as $u_i!$. In both cases $D_l$ therefore contains the entire 3-part of $m_l!$: the ordinary character has defect zero and remains irreducible.

Write $m=m_l$, $t=m_{l+1}-m$ and $M=m_{l+1}-1$. By (3), $D_l^2\ge(M!)_{3'}$ proves (4) for the **whole interval** $m\le n\le M$. Put $R_l=D_l^2/m_l!$. We first prove, for either staircase,

$$
R_{l+1}\ \ge\ R_l(2/3)^t\qquad(l\ge64).
\tag{6}
$$

We use $a!\le(2a/5)^a$ for integers $a\ge64$. The base is the integer inequality $5^{64}64!\le128^{64}$. For induction, $(1+1/a)^a\ge5/2$ follows by retaining binomial terms of orders 0 through 3 (for $a\ge64$).

For the ordinary staircase put $b=l+1$, so $t=2b$ and $m=b(b-1)$. The hook product increases by the factor $\prod_{j=1}^b(3j-1)(3j-2)\le 3^{2b}(b!)^2$. Consequently

$$
\frac{R_{l+1}}{R_l}
\ \ge\ \frac{(m+1)^{2b}}{3^{4b}(b!)^4}
\ \ge\ \left(\frac{25(m+1)}{36b^2}\right)^{2b}
\ \ge\ (2/3)^t .
$$

The last inequality is $25(b^2-b+1)\ge24b^2$, true for $b\ge65$.

For the spin staircase $t=3l+1$ is the new largest part. In the degree ratio (5), the extra pair product is at least

$$
\prod_{j=1}^l\frac{3(l+1-j)}{3(l+j)}
=\binom{2l}{l}^{-1}\ge4^{-l}.
$$

The square of the power-of-two factor gains at least $2^{t-2}$, including the effect of the floor. Hence

$$
\frac{R_{l+1}}{R_l}
\ \ge\ 2^{t-2}16^{-l}\frac{(m+1)^t}{(t!)^2}
\ \ge\ 2^{-l-1}\left(\frac{25(m+1)}{4t^2}\right)^t
\ \ge\ (2/3)^t .
$$

Here $25(m+1)-4t^2=(3l^2-73l+42)/2\ge0$ and $2^{-l-1}\ge(2/3)^{3l+1}$.

At $l=64$ the hook formulas give $R_{64}\ge(2/3)^{m_{64}}$ in both sectors (exact check below). Thus $R_l\ge(2/3)^m$ for $l\ge64$. To show it suffices for every $l\ge256$, let $P(M)$ be the 3-part of $M!$. The base-3 digit sum of $M$ is at most $2(1+\lfloor\log_3 M\rfloor)$; Legendre's formula $v_3(M!)=(M-s_3(M))/2$, with $s_3$ the digit sum, gives $P(M)\ge3^{M/2}/(3M)$. Using $M!/m!\le M^{M-m}$, $M\ge m$ and $3M\le M^2$, we get

$$
\frac{D_l^2}{(M!)_{3'}}
=\frac{R_l P(M)}{M!/m!}
\ \ge\ \frac{(2/\sqrt3)^m}{M^{M-m+2}}.
$$

For both size polynomials, $M\le2(l+2)^2$ and $5m-2l(M-m+2)$ equals $l(l-1)$ in the ordinary case and $l(3l-13)/2$ in the spin case, both nonnegative for $l\ge256$. Also $(8/7)^{2l}\ge(2(l+2)^2)^5$ on this range: check $l=256$, and note that $(8/7)^2\ge(259/258)^{10}\ge((l+3)/(l+2))^{10}$. Raising to the power $m/(2l)$ gives $(8/7)^m\ge M^{M-m+2}$. Since $2/\sqrt3>8/7$, the infinite tail follows.

## The finite intervals and small ranks

The accompanying [integer verifier](verify.py) does the following finite calculations. It needs only Python's standard library. Write $f(n)=n!/P(n)$ for the prime-to-3 part of $n!$.

1. Start the staircase interval tests at $L=43$ in the ordinary sector and $L=27$ in the spin sector. For $L\le l<64$ check $D_l^2\ge f(M)$ directly. For $64\le l<256$ retain the stronger starting value in (6): check
   $D_{64}^2 \cdot 2^{m-m_{64}}P(M)\ge m_{64}! \cdot 3^{m-m_{64}}(M!/m!)$. This uses the hook formula only at the base, not an extrapolation from numerical ratios.
2. The remaining ranks are $5\le n\le1891$ (ordinary) and $5\le n\le1079$ (spin). Gather core partitions in ranks $4\le m\le n_{\max}+7$. Ordinary candidates come from flush three-runner abaci: take runner heights $(a+h,b+h,-a-b+h)$ with $h=-\min(a,b,-a-b)$, $|a|,|b|\le\lfloor\sqrt{n_{\max}+7}\rfloor+3$, and read the beta-set. Spin candidates have parts $r,r+3,\ldots,r+3(l-1)$ for $r=1,2$. Check full 3-defect zero by division on each degree. Completeness of the candidate list is **not** required.
3. At ranks $m\le64$ also add partitions obtained from a core by **one** 3-hook or 3-bar. In the ordinary abacus this moves one bead forward by three into a vacancy. For bars, increase a part by three into a vacancy, append a new part 3, or append absent parts 1 and 2. These are the inverses of single bar removals. The verifier also checks that $v_3(m!)-v_3(D)=1$ for each such label of degree $D$. This independently certifies weight one: the difference is the sum of the 3-adic valuations of the hook lengths (bar lengths for spin, since the power of two does not matter), and the weight counts those divisible by 3 ([Olsson, §§3–4](https://web.math.ku.dk/~olsson/manus/comb_rep_all.pdf)). By the weight–defect correspondence the resulting blocks have a cyclic defect group of order 3 ([Olsson, Propositions 11.3 and 13.3](https://web.math.ku.dk/~olsson/manus/comb_rep_all.pdf)). For a cyclic-defect block $B$ with defect group $D$, $\dim B\le |D|\sum_{\varphi\in\operatorname{IBr}(B)}\varphi(1)^2$ ([Kiyota–Wada, Proposition 4.7, as used by Malle, Lemma 2.2](https://arxiv.org/pdf/2012.08765)). The central idempotent for the sector is a sum of block idempotents ($p=3$ and the covering kernel has order two). Hence each such block contributes at least **one third of the sum of the ordinary squared degrees selected from that block**, since its dimension is the sum over *all* ordinary characters in it. This argument does not assert that weight-one characters remain irreducible.
4. Let $B_m$ be three times the sum of these lower bounds in the chosen sector: count a defect-zero squared degree three times and a weight-one squared degree once. Each defect-zero character gives a distinct one-character block. Keep each partition label once, with both spin associates counted when appropriate. Thus $B_m\le3s_j(m)$. For each target rank $n$, test whether some $m\le n$ gives $B_m\ge3 f(n)$, or some $n<m\le n+7$ gives $B_m\ge3 f(n)(m!/n!)^2$. Either is sufficient by (3). The only uncovered cases are these:

| group and sector on the alternating side | 3-modular degrees in sector | sum of squares | $\lvert A_n\rvert_{3'}$ |
|---|---|---:|---:|
| $A_7$ | $1,6,10,10,13,15$ | 631 | 280 |
| $\widehat A_8$, spin | $8,24,24,48$ | 3520 | 2240 |
| $\widehat A_9$, spin | $8,48,104$ | 13184 | 2240 |

The rows come from the GAP Character Table Library ([A7](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/A7.html), [2.A8](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/2.A8.html), [2.A9](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/2.A9.html)). They can be recovered with the following commands, using CTblLib 1.3.11:

~~~gap
for name in ["A7","2.A8","2.A9"] do
  t := CharacterTable(name) mod 3;
  rows := Irr(t);
  if name <> "A7" then
    z := Positions(SizesConjugacyClasses(t),1)[2];
    rows := Filtered(rows, x -> x[z] = -x[1]);
  fi;
  Print(name, " ", SortedList(List(rows,DegreeOfCharacter)), "\n");
od;
~~~

These checks finish both alternating sectors. The classification of finite simple groups and Tong-Viet's reduction now give the stated inequality for every finite group at $p=3$.

**Verification scope.** Run `python3 -I verify.py` for the finite degree and interval certificates, the numerical bases of the infinite estimates, and negative controls that reject a non-defect-zero partition and an insufficient spin row. The Lean companion `WillemsBrauerCharacterSquares.tensor_quotient_degree` proves the representation-theoretic dimension bound (2) for a nonzero intertwiner from a tensor product. The reduction, classification, block theory, and global theorem are mathematical proofs using the cited literature, not claims of full Lean formalization.

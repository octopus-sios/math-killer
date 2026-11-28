# Unimodality away from the boundary of the stable second hypersimplices

Let $P_{n,r}$ be the convex hull of the vectors $e_i+e_j$ for pairs at circular distance at least $r$ in the $n$-gon, and write $h(x)=h^*(P_{n,r};x)=\sum_i h_i x^i$. Put $d=n-2r$ (separation from the extremal parameter, **not** the dimension). [Solus's Conjecture 3.4.5](https://uknowledge.uky.edu/math_etds/32/), also [Braun–Solus, Conjecture 4.22](https://doi.org/10.1016/j.jcta.2018.03.002), asks for unimodality for every admissible pair. This is the ordinary edge polytope, not the symmetric edge polytope.

**Theorem.**

1. If $n\ge 3r-2$, then $h(x)$ has log-concave coefficients, hence is unimodal.
2. If $n\ge24$ and $d\ge 2+8\sqrt{n\log n}$, then $h(x)$ is unimodal. In particular, for **every** $\epsilon>0$ the conjecture holds for all sufficiently large $n$, uniformly over $r\le(1/2-\epsilon)n$.
3. On the line $n=2r+4$, the polynomial has $n/2$ distinct negative real roots.

We give a finite binomial formula valid for **all** the polynomials. It does not prove unimodality for all parameters. In particular the estimates do not control the middle degrees uniformly when $d$ is of order $\sqrt n$ or smaller. Braun and Solus had already given a formula by a shelling, and proved special cases including the outermost nontrivial level $r=\lfloor n/2\rfloor-1$; part 3 concerns the **next** even level.

## 1. Count opposite semicircles

Write $L(t)=|tP_{n,r}\cap\mathbb Z^n|$. An integer vector of nonnegative gaps $g_1,\ldots,g_n$ of sum $2t$ is counted iff every $r$ cyclically consecutive gaps have sum at most $t$. Necessity holds at each vertex and hence throughout the dilate. For sufficiency list $2t$ tokens in circular order, $g_i$ at site $i$. Pair token $j$ with token $j+t$ for $1\le j\le t$. If a directed arc between paired tokens traverses fewer than $r$ site-edges, an $r$-window contains at least $t+1$ tokens, including both endpoints. This also rules out a coincident pair. The pairs thus give $t$ allowed vertices summing to the vector. By rational dilation and closure the same inequalities describe the polytope over the reals, as in [Hibi–Solus, Theorem 2.1](https://arxiv.org/abs/1408.5932) in its facet range. For $d>0$, the vector with every coordinate $2/n$ is strict in all the inequalities, so the dimension is $n-1$. When $d=0$, only the antipodal pairs occur. Their disjoint supports identify the polytope, with its affine lattice, with a standard unimodular simplex; $h(x)=1$. Henceforth $d>0$.

For $t>0$ place $n$ beads at integer positions on a circle of circumference $2t$, the successive gaps being $g_1,\ldots,g_n$ (ties allowed). The window condition is equivalent to **every** semicircle of bins $(a,a+t]$ containing at least $r$ beads, hence between $r$ and $n-r$ by complementation. Indeed, starting at the last occurrence of a bead at $a$, its $r$-th successor must lie at or before $a+t$; at an empty bin use the last bead preceding it. Conversely this condition at occupied bins suffices, including for earlier occurrences tied in the same bin.

Let $A(t)$ count the occupancy vectors of the $2t$ **labeled** bins satisfying this condition. Then $2tL(t)=nA(t)$. To see the factors even with ties or rotational symmetry, choose the initial bin for the labeled gap sequence; conversely choose the starting bead occurrence of an occupancy vector, ordering occurrences in each bin from arrival to departure. The positive circumference specifies the first occurrence of each occupied bin in the cyclic gap list, even if all beads share a bin.

Track the semicircle count for $t$ slides by one bin. It ends at the reflection of its starting value, since the last semicircle is complementary to the first. If a slide drops $a$ beads and adds $b$, the generating function at fixed displacement $k=b-a$ is $z^{|k|}/(1-z^2)$ by total $a+b$. On the states $r,\ldots,n-r$, let $J$ reverse their order, and set

$$
M_{ij}(z)=\frac{z^{|i-j|}}{1-z^2}.
$$

Then $A(t)=[z^n]\operatorname{tr}(J M(z)^t)$. Indeed all antipodal bin pairs are filled by the slides. Conversely, for a path starting at $h$ and ending at $n-h$, selecting total degree $n$ forces the total removed to equal $h$ and the total added to equal $n-h$. Thus the path's initial count is the actual one, not an extra choice. The constraints for the remaining $t$ slides follow by complementation.

## 2. Fold the transfer matrix

The inverse $Q=M^{-1}$ has end diagonals $1$, inner diagonals $1+z^2$, and both off-diagonals $-z$, as direct multiplication shows. All these matrices commute with $J$. Subscripts $+$ and $-$ on determinants refer to restriction to the symmetric and antisymmetric spaces of $J$. The formal identity $-\log\det(I-xM)=\sum_{t\ge1}x^t\operatorname{tr}(M^t)/t$, applied on the two spaces and subtracted, sums the Ehrhart series.

Here are details of the normalization. Substitute $z=(1-x)w$ and let $D_\pm(w,x)$ be the two determinants of $(Q((1-x)w)-xI)/(1-x)$. This tridiagonal matrix has end diagonals $1$, inner diagonals $p=1+(1-x)w^2$, and off-diagonals $-w$. Put $F=\log(D_-/D_+)$. Since $\det(I-xM)=\det(Q-xI)/\det Q$, multiplication of the Ehrhart series by $(1-x)^n$ gives

$$
h(x)=(1-x)^n+\frac n2[w^n]\big(F(w,x)-F((1-x)w,0)\big).
$$

Constant factors in $w$ do not affect the extraction. To evaluate $F$, define the end continuants $f_0=f_1=1$ and $f_{k+1}=p f_k-w^2 f_{k-1}$ for $k\ge1$. Expansion along the last row gives these determinants. Folding the path of $d+1$ sites gives

$$
\frac{D_-}{D_+}=
\begin{cases}
f_s/(f_{s+1}-w^2f_{s-1}) & d=2s,\\[2pt]
(f_{s+1}+w f_s)/(f_{s+1}-w f_s) & d=2s+1 .
\end{cases}
$$

In the first case the antisymmetric center vanishes; in the symmetric case its two neighbors give twice the usual $-w^2 f_{s-1}$ term in the last continuant step. In the second case reflection at the middle edge adds $+w$ or $-w$ to the last diagonal. At $x=0$ all $f_k=1$, so $F(w,0)$ is respectively $-\log(1-w^2)$ or $\log((1+w)/(1-w))$. Since $n$ and $d$ have the same parity, $(n/2)[w^n]F(w,0)=1$ in both cases. Thus

$$
h(x)=\frac n2[w^n]F(w,x).
\tag{1}
$$

## 3. A binomial formula

Adopt $\binom ab=0$ for $b<0$ or $b>a$ with $a\ge0$. For $0\le i\le\lfloor n/2\rfloor$ put $B_i=\binom n{2i}$. For each **positive odd** $j$ with $j(d+2)\le n$, put $a=(n-j(d+2))/2$, $A=a+2j-1$, $B=a+jd-1$. Then

$$
h_i=B_i-\sum_j\frac n j
\left(\binom A{i+j-1}\binom B{i-j}
      -\binom A{i+j}\binom B{i-j-1}\right).
\tag{2}
$$

There are no higher nonzero coefficients. We derive the formula to keep track of the signs and the finite boundaries.

Let $\lambda,\mu$ be the roots of $y^2-py+w^2$, ordered by $\lambda(0)=1$, and write $\Delta=\lambda-\mu$, $v=w/\lambda$. The continuant is

$$
f_k=\frac{(1-\mu)\lambda^k-(1-\lambda)\mu^k}{\Delta}.
$$

In the folded quotients the finite-length factor is $(1-T)/(1+T)$ in **both** parities, where $T=((1-\lambda)/(1-\mu))v^d$. In fact, for even $d$, $f_{s+1}-w^2 f_{s-1}=(1-\mu)\lambda^s+(1-\lambda)\mu^s$, leaving prefactor $1/\Delta$. For odd $d$ use $(\mu\pm w)/(\lambda\pm w)=\pm v$, leaving prefactor $(1+v)/(1-v)$. The log of either prefactor contributes exactly $B_i$ in (1). For even $d$ factor $\Delta^2=(1-(1+\sqrt{x})^2w^2)(1-(1-\sqrt{x})^2w^2)$; for odd $d$ use $((1+v)/(1-v))^2=(p+2w)/(p-2w)$ and $p\pm2w=(1\pm(1+\sqrt{x})w)(1\pm(1-\sqrt{x})w)$. The extracted polynomial is the even part of $(1+\sqrt{x})^n$.

Set $u=w/(1-\mu)$ and $Y=uv$. Since $(1-\lambda)(1-\mu)=xw^2$ and $\mu=wv$, one has $u=w(1+Y)$, $v=w(1+xY)$, and $Y=w^2(1+Y)(1+xY)$. Hence $T=xw^{d+2}(1+Y)^2(1+xY)^d$. Expanding $\log((1-T)/(1+T))=-2\sum_{j\ {\rm odd}}T^j/j$ explains the range in (2). In particular each subtracted polynomial has nonnegative coefficients. With $y=w^2$, formal series reversion gives

$$
[y^a]\,(1+Y)^{2j}(1+xY)^{jd}
=[b^a]\,(1-xb^2)(1+b)^{a+2j-1}(1+xb)^{a+jd-1}.
$$

Indeed substitute $y=b/((1+b)(1+xb))$ in the coefficient residue; the logarithmic Jacobian is $(1-xb^2)/((1+b)(1+xb))$. Extracting $x^{i-j}$ gives (2). Each correction has degree at most $a+j=(n-jd)/2\le r$; thus $h_i=B_i$ for $i>r$.

## 4. Log-concavity for $n\ge 3r-2$

Here $3(d+2)>n$, so only $j=1$ occurs. Define $H_i$ by the resulting expression

$$
H_i=B_i-n\left(\binom ri\binom{n-r-2}{i-1}
              -\binom r{i+1}\binom{n-r-2}{i-2}\right),
\qquad R_i=1-H_i/B_i .
\tag{3}
$$

We prove $H_i^2\ge H_{i-1}H_{i+1}$. The following two *finite polynomial sign checks* are part of the proof; the routine `cone_certificate` in [verify.py](verify.py) carries them out over the integers. We specify the degrees, translations and test so that the checks do not depend on any symbolic inequality solver.

For $1\le i\le10$, the Turán difference $H_i^2-H_{i-1}H_{i+1}$ has total degree at most $4i$ in $n,r$ (the lower indices in (3) are fixed). Check it on the orthant $r=11+v$, $n=3r-2+u$. For each $1\le r\le10$, check it on the ray $n=\max(3r-2,2r+1,2i+2)+u$. These are all the relevant parameters: $i+1$ must lie in the coefficient range and $d>0$. In each check all mixed forward differences at the origin through degree $4i$ in each variable are nonnegative.

For the tail, we show $R_i-2R_{i+1}+R_{i+2}\ge0$ whenever $i\ge10$ and $i+2\le\lfloor n/2\rfloor$. For $r\le i$ it follows from $R_i\ge0$ and the vanishing beyond $r$. Otherwise (3) simplifies by canceling factorials to $R_{k+1}/R_k=N_k/E_k$ at $k=i,i+1$, where

$$
\begin{aligned}
 N_k&=2(k+1)(2k+1)(r-k)(n-r-k)\big(n+(k+1)(d-2)\big),\\
 E_k&=k(k+2)(n-2k)(n-2k-1)\big(n+k(d-2)\big).
\end{aligned}
$$

The denominators and $R_i,R_{i+1}$ are positive here (the deficit before division by $B_k$ equals $n\binom rk\binom{n-r-1}{k-1}(n+k(d-2))/((k+1)(n-r-1))$ for $1\le k\le r$). Substitute $i=10+z$, $r=i+1+v$, $n=3r-2+u$ in

$$
E_i E_{i+1}-2 N_i E_{i+1}+N_i N_{i+1}.
$$

This polynomial has degree at most $12$. All mixed forward differences at the origin through degree 12 in each variable are nonnegative. This is the second sign certificate. In both checks the justification is the Newton expansion: a polynomial of degree at most $b$ in each variable on a nonnegative integer orthant is the sum of its mixed differences at zero times the corresponding products of binomial coefficients. The values on $\{0,\ldots,b\}$ in each coordinate suffice. This proves inequalities for unbounded parameters, not just at the grid points.

Thus $1-R_i$ is concave on the tail starting at 10. It is nonnegative (it is $h_i/B_i$), hence log-concave there by the arithmetic-geometric mean inequality. The sequence $B_i$ is log-concave by its consecutive-term ratios; multiplying preserves log-concavity. This covers every central index $i\ge11$, and the first certificate covers $1\le i\le10$. There are no internal zeros: this also follows directly from the monomer and flat-step constructions below (the case $d=1$ gives $h=1$ by (1)). This proves part 1.

## 5. A uniform increasing prefix

We need a lower bound on successive coefficients independent of the band width. Let $D_b(y)$ enumerate Dyck paths of height at most $b$ by semilength ($y$) and number of peaks ($x$). Paths use up and down steps and start and end at height zero without going below it. $D_0=1$. Decomposition into first-return pieces gives $D_b=1/(1-y(x+D_{b-1}-1))$: an empty path inside a piece produces one peak. At $y=w^2$, the continuant recurrence gives $D_b=f_b/f_{b+1}$.

**Odd $n$, $d=2s+1\ge3$.** By (1) the polynomial is $n[w^n]\sum_{k\ {\rm odd}}(wD_s)^k/k$. This counts circular walks with $n$ labeled step positions, flat steps allowed only at ground level, and Dyck paths of height at most $s$ between successive flats, weighted by number of peaks. Indeed $k$ flats cut out $k$ ordered paths after a choice of starting flat; there are $n$ possible positions for that start and $k$ choices per walk. The parity of $n$ forces $k$ odd. In particular $(UD)^i$ followed by $n-2i$ flats is allowed for every $0\le i\le\lfloor n/2\rfloor$.

Regard each matched up/down pair in a Dyck path as a node of an ordered forest; its children are the immediately enclosed pairs. Leaves are peaks. In a forest with $i$ leaves there are at most $i$ nodes with at least two children (sum the numbers of children). A node with exactly one child, encoded $U\,C\,D$ for a single subtree $C$, can be changed to $UD\,C$. It becomes a leaf, its former child becomes its next sibling, and the height bound is preserved. Alternatively, two consecutive flats can be turned into $UD$. Both moves add one peak at fixed length. With $k$ flats there are at least $(n-k)/2-2i$ unary nodes and at least $k-i$ ordered starts of consecutive flats: each flat followed by a nonflat starts a nonempty forest containing a leaf. The two lower bounds remain valid if negative. Given a result with a distinguished new leaf, reversing the unary move has at most one choice (absorb the next sibling); reversing the flat move also has at most one. These statements concern labeled cyclic positions, not rotation classes. Double counting gives

$$
2(i+1)h_{i+1}\ \ge\ (n/2-3i)h_i .
$$

**Even $n=2m$, $d=2s\ge2$.** The even folded denominator divided by $f_s$ is $1-y(1+x+2(D_{s-1}-1))$. Thus (1) counts circular tilings of $m$ labeled positions, again by the marked-start argument for the logarithm. A tile is an unmarked monomer, a marked monomer (weight $x$), or a tile of length $1+k$ carrying a nonempty Dyck path of semilength $k$, height at most $s-1$, and one of two colors. The statistic is marks plus leaves. The monomers alone give every degree from 0 to $m$.

Marking an unmarked monomer or converting a unary node as above increases the statistic by one. If there are $t$ tiles, $l$ leaves and $b$ marks, there are at least $t-l-b$ unmarked monomers and $m-t-2l$ unary nodes. The new mark or new leaf determines its inverse, if it exists. Hence $(i+1)h_{i+1}\ge(m-3i)h_i$, where $i=b+l$.

In both parities, if $n\ge24$ and $i<n/12$, these inequalities give $h_{i+1}\ge h_i$. The excluded width $d=1$ is the constant-polynomial case.

## 6. Outside the boundary strip

Assume $n\ge24$, $d\ge 2+8\sqrt{n\log n}$, and $i\ge n/12$. The subtracted terms in (2) are nonnegative by their series derivation. For each $j$ bound the difference of products above by the first product. Since $A+B=n-2$, this product divided by $\binom{n-2}{2i-1}$ is a hypergeometric point probability. In a sample of $\ell=2i-1$ without replacement from $n-2$ objects, $A$ of them special, the number of specials is required to be $i+j-1$. The population fraction is $1/2-j(d-2)/(2(n-2))$. Thus the required fraction exceeds the population fraction by at least $j(d-2)/(2(n-2))$. An out-of-range requirement has probability zero.

For clarity, the probability that the sample fraction exceeds its mean $p_0$ by $v$ is at most $\exp(-2\ell v^2)$. For $\theta>0$ its count has exponential moment at most $(1-p_0+p_0e^\theta)^\ell$: the average of products of $\ell$ distinct population values (each $1$ or $e^\theta$) is at most their arithmetic mean raised to the power $\ell$ by Maclaurin's inequality. The second derivative of $\log(1-p_0+p_0e^\theta)$ is at most $1/4$, and its first derivative at zero is $p_0$. Exponential Markov with $\theta=4v$ gives the bound.

Now $\ell\ge n/8$, so the point probability is at most $\exp(-j^2(d-2)^2/(16n))\le n^{-4}$. Also $n\binom{n-2}{2i-1}/B_i=2i(n-2i)/(n-1)\le n$. There are at most $n$ terms; consequently

$$
(1-n^{-2})B_i\le h_i\le B_i \qquad (i\ge n/12).
$$

For adjacent *unequal* $B_i,B_{i+1}$ their difference divided by the larger is greater than $1/n$: the ratio is $(n-2i)(n-2i-1)/((2i+2)(2i+1))$, and the difference of its numerator and denominator is $(n+1)(n-4i-2)$. Thus the direction of every strict comparison between adjacent binomials in this range is unchanged. The binomials increase and then decrease, with at most one equal pair at the maximum. Either comparison within that pair is compatible with unimodality. Joining this range to the increasing prefix proves part 2.

## 7. A real-rooted boundary family

For $n=2m$ and $r=m-2$ the even folded numerator is $f_2=1-xy$, and its denominator is $f_3-y f_1=1-(1+2x)y-x(1-x)y^2$, with $y=w^2$. By (1),

$$
h(x)=a^m+b^m-x^m,\qquad
a,b=\frac{1+2x\pm\sqrt{1+8x}}2 .
$$

This polynomial has degree $m$ with leading coefficient 1 (also immediate from (2) since $m>r$). For $x<-1/8$, take $a=\rho e^{\mathrm i\theta}$ in the upper half plane, $b=\overline a$. Then $\rho^2=x(x-1)>x^2$. As $x$ runs from $-1/8$ to $-\infty$, the argument varies continuously from $0$ to $\pi$ in the limit. At each $\theta=k\pi/m$ for $0\le k<m$, the term $2\rho^m\cos(m\theta)$ strictly dominates $x^m$ in absolute value and has sign $(-1)^k$. The initial sign also holds at $-1/8$. Use the points in first-hitting order and finally use the leading sign $(-1)^m$ at a sufficiently negative argument. The $m$ intervening intervals each contain a distinct zero, exhausting the degree. Newton's inequalities give log-concavity. This proves part 3.

## Exact checks and scope

Run `python3 -I verify.py` in this directory. Besides the integer polynomial certificates in Section 4, the verifier reconstructs Ehrhart numerators independently from sets of sums of the actual vertices for $3\le n\le10$. It compares the boundary recurrence with (2), rejects a changed coefficient, and checks log-concavity for every admissible pair through $n=320$. One useful cross-check is $(n,r)=(9,3)$: $h_2=27$, agreeing with the cycle independence polynomial in Braun–Solus, Theorem 4.14, but not the displayed $r=3$ coefficient in their Corollary 4.21 (which gives 43 here). This is a coefficient discrepancy, not a failure of unimodality. The finite sweep excludes counterexamples in that range only; parts 1–3 are infinite-family results.

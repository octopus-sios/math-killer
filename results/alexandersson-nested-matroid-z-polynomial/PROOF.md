# A common Legendre interlacer for wide Schubert matroids

**Theorem.** Let $\lambda_1\ge\cdots\ge\lambda_r>0$, with $r\ge2$. If $\lambda_r\ge 30(r-1)$, the Schubert matroid of Ferrers shape $\lambda$ has a $Z$-polynomial with $r$ simple negative zeros. More precisely, the following polynomial strictly interlaces it:

$$
D_{r-1}(t)=\sum_{j=0}^{r-1}\binom{r-1}{j}^{\!2}t^j.
$$

There is no bound on the other parts. In the canonical strictly increasing upper-bound convention for bases, $q_i=i+\lambda_{r+1-i}$, so the hypothesis is $q_1\ge 30(r-1)+1$. The same interlacer works for a connected skew shape $\lambda/\mu$ with $r$ rows if **every pair of consecutive rows overlap in at least $30(r-1)$ columns**. Those overlaps need not occur in the same columns. Consequently, at fixed rank, every nonzero finite nonnegative linear combination of these $Z$-polynomials also has simple negative zeros.

This is a partial result on [Alexandersson's nested-matroid conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjNestedMatroidZ). It gives one linear threshold simultaneously in the rank and for all shapes, rather than eventual real-rootedness along an individual stretching ray. The [author's research thread](https://github.com/PerAlexandersson/RealRooted/issues/2650) also reports finite-rank results and several all-rank families using a Narayana interlacer. Our interlacer is different. The unrestricted nested question remains open; the constant 30 is sufficient, not asserted optimal. [Xie–Zhang, Theorem 1.1](https://arxiv.org/abs/2609.07636) covers sparse paving matroids, in particular uniform matroids. [Eberhardt, Theorem 6.1](https://arxiv.org/abs/2609.20903) disproves real-rootedness for arbitrary matroids using the extended binary Golay matroid; its cyclic flats do not form a chain, so it is not nested.

## 1. The expansion at returns to zero

We use as input [Alexandersson's Motzkin-path and rook-placement formula](https://www.symmetricfunctions.com/schubertMatroidZ.htm) (unpublished, with a proof sketch via the snake subdivision). Write $m=r-1$ and $B$ for the board of top-left corners of $2\times2$ squares. Row $i$ of $B$ consists of the integer columns $\mu_i<c<\lambda_{i+1}$; take $\mu=0$ for an ordinary Ferrers shape. Both the left and the right endpoints decrease weakly down the board. Let $R(E)$ count placements in rows from $E\subseteq[m]$, including the empty placement, with strictly decreasing columns as the occupied rows increase.

In the cited formula a path starts and ends at zero, never goes below zero and takes $r$ steps of size $+1,0,-1$. Its weight is $t^u(1+t)^{r-2u}$ times $R(E)$, where $u$ counts up-steps and $E$ comprises the internal times at which the height is positive. Summing gives $Z(t)$.

Set $x=(1+t)/(1-t)$, so $-1<x<1$ corresponds increasingly to $-\infty<t<0$. Dividing a path weight by $(1-t)^r$ gives a factor $x$ per level step and $(x^2-1)/4$ per up-down pair. Let $a_j(x)$ be the sum of these normalized weights for paths of length $j$ with no internal visit to zero, without rooks. For a composition $\ell_1+\cdots+\ell_b=r$ into positive parts, let $T$ be its set of proper partial sums. Cutting a path at **all** its internal visits to zero gives

$$
H(x):=\frac{Z(t)}{R([m])(1-t)^r}
=\sum_{\ell_1+\cdots+\ell_b=r}
p(T)\prod_{i=1}^b a_{\ell_i}(x),
\qquad p(T)=\frac{R([m]\setminus T)}{R([m])}.
$$

The sum includes every length $b\ge1$. The one-part term is exactly $a_r$. We will show that all other terms together have smaller absolute value at the zeros of the ordinary Legendre polynomial $L_m$ normalized by $L_m(1)=1$.

## 2. How much does forbidding a row cost?

Suppose every row of the board contains at least $W$ columns, with $W+1\ge30m$. Then

$$
p(T)\le q^{|T|},\qquad q=\frac{m}{W+1}.
$$

To see this, fix $E$ of size $e$ and a row $i\in E$. From any placement in $E\setminus\{i\}$ of size $s$, select an unused column in row $i$ (at least $W-s$ choices). Add the row and column, then sort the chosen columns into decreasing order on the chosen rows. The result is legal: if two rows in increasing order have their columns in increasing order instead, exchanging the two columns stays inside both row intervals, by monotonicity of both endpoints. Sorting simply repeats such exchanges.

For any output using row $i$, the inserted column determines the input: remove that column and row $i$ and sort the rest. Thus the multiplicity is at most $s+1\le e$. Since $W-s\ge W-e+1$, at least $(W-e+1)R(E\setminus\{i\})/e$ placements use row $i$. Adding those that skip it gives $R(E)\ge (W+1)R(E\setminus\{i\})/e$. Delete the rows of $T$ one at a time. The width hypothesis holds with $W=\min_i(\lambda_{i+1}-\mu_i-1)$ by the overlap assumption.

## 3. Bounds on a single excursion

Use $x=\cos\theta$, $s=\sin\theta$ with $0<\theta<\pi$. We need three estimates:

$$
\begin{aligned}
\sum_{j\ge1}|a_j(x)|&\le 2,\\
|a_j(x)|&\le \frac{3\sqrt{s}}{4j^{3/2}}\quad(j\ge2),\\
|a_r(x)|&\ge\frac{\sqrt{s}}{2\sqrt{2}\,r^{3/2}}
   \quad\text{if }L_{r-1}(x)=0.
\end{aligned}
$$

**Generating function.** Write $A(z)=\sum_{j\ge1}a_j(x)z^j$. An excursion is either a single level step or an up-step and a down-step enclosing an arbitrary sequence of excursions. Thus $A=xz+(x^2-1)z^2/(4(1-A))$, or

$$
A(z)=\frac{1+xz-\sqrt{1-2xz+z^2}}{2}.
$$

The square root factors as $(1-e^{i\theta}z)^{1/2}(1-e^{-i\theta}z)^{1/2}$. Each factor has coefficient absolute sum 2: the nonconstant coefficients of $(1-z)^{1/2}$ are negative and their absolute values sum to 1 by the binomial series at $z\uparrow1$. The product has coefficient absolute sum at most 4 and begins $1-xz$. Since $a_1=x$, the first bound follows: $|x|+(4-1-|x|)/2\le2$.

Differentiate $A$ in $x$ and use the Legendre generating function $(1-2xz+z^2)^{-1/2}$. This gives $a_j'=L_{j-1}/2$ for $j\ge2$. As $a_j(1)=0$, the Legendre equation yields

$$
a_{k+1}(x)=\frac{(x^2-1)L_k^{\prime}(x)}{2k(k+1)},\qquad k\ge1.
$$

**Energy bounds.** Put $f(\theta)=\sqrt{s}\,L_k(\cos\theta)$ and $Q=(k+1/2)^2+1/(4s^2)$. Direct substitution in the Legendre equation gives $f''+Qf=0$. On $(0,\pi/2]$ the function $Q$ is decreasing. The two energies
$S=f^2+(f')^2/Q$ and $J=(f')^2+Qf^2$ satisfy $S'=-Q'(f')^2/Q^2\ge0$ and $J'=Q'f^2\le0$. Parity gives the same comparison with the center on the other half of the interval. In particular,

$$
S(\theta)\le S(\pi/2)\le\frac1{k+1},
\qquad J(\theta)\ge J(\pi/2)\ge\frac{k}{2}.
$$

Here are the constants in this step. For $v_h=4^{-h}\binom{2h}{h}$, one has $1/(4h+1)\le v_h^2\le1/(2h+1)$ by induction with $v_{h+1}/v_h=(2h+1)/(2h+2)$. For $k=2h$, the central absolute values of $(f,f')$ are $(v_h,0)$; for $k=2h+1$ they are $(0,kv_h)$. These follow from the Legendre generating function at $x=0$ and its derivative. Substitution, using $Q(\pi/2)=k(k+1)+1/2$, gives the displayed bounds.

By Cauchy–Schwarz and the definition of $S$,

$$
s^2|L_k^{\prime}(x)|=\sqrt{s}\,\left|f'-\tfrac12\cot\theta\, f\right|
\le\sqrt{s}\sqrt{S\bigl(Q+\tfrac14\cot^2\theta\bigr)}.
$$

If $ks\ge1$, then $Q+\cot^2\theta/4=k(k+1)+1/(2s^2)$, so the right side is at most $\sqrt{s}\sqrt{3k/2}$. For $k\ge2$ this gives the second bound since $\sqrt{3(k+1)/(2k)}/2\le3/4$. For $k=1$ use $a_2=-s^2/4$ directly.

For $ks<1$, use $|L_k^{\prime}|\le k(k+1)/2$. Indeed $|L_j|\le1$ on $[-1,1]$ by the [Laplace integral](https://dlmf.nist.gov/18.10#ii); telescoping $L_{j+1}^{\prime}-L_{j-1}^{\prime}=(2j+1)L_j$ gives the derivative bound. Hence $|a_{k+1}|\le s^2/4\le\sqrt{s}/(4k^{3/2})$, also sufficient since $(1+1/k)^{3/2}\le2^{3/2}<3$.

Finally at a zero of $L_k$ we have $f=0$ and $|f'|=\sqrt{J}\ge\sqrt{k/2}$. The formula for $a_{k+1}$ gives the third bound with $r=k+1$. We will also use $s\ge1/r$ at these nodes: since $|L_k(\pm1)|=1$, the derivative bound implies $1-|x|\ge 2/(k(k+1))$, and $s^2\ge1-|x|$.

## 4. The sign at every Legendre zero

Fix a zero $x$ of $L_{r-1}$. For each $2\le b\le r$ we claim

$$
\sum_{\substack{\ell_1+\cdots+\ell_b=r\\\ell_i\ge1}}
\left|\prod_i a_{\ell_i}(x)\right|
\le |a_r(x)|\,\frac{3}{\sqrt{2}}\, b^{5/2}\,2^{b-1}.
$$

If $b<r$, mark a largest part. It is at least $r/b$ and at least 2. By Section 3 its absolute contribution is at most $|a_r|(3/\sqrt{2})b^{3/2}$. There are at most $b$ choices of its position. Once the other parts are chosen, its length is determined, so summing the absolute weights of the other parts costs at most $2^{b-1}$. If $b=r$, the sole composition has weight $x^r$. Here $1/|a_r|\le2\sqrt2\,r^2$ by $s\ge1/r$, which is within the claimed bound.

Since $|T|=b-1$, the absolute error relative to $a_r$ is bounded by the sum of $(3/\sqrt2)b^{5/2}(2q)^{b-1}$ over $2\le b\le r$. The first term is $24q$, and the ratio of successive bounds is at most $2q(3/2)^{5/2}<6q$. The finite sum is therefore strictly less than $24q/(1-6q)\le1$ when $0<q\le1/30$. In particular $H$ has the sign of $a_r$ at every node.

The $r-1$ Legendre nodes are simple and in $(-1,1)$ by orthogonality. At them $a_r$ has sign opposite to $L_{r-1}^{\prime}$, so the signs alternate and the rightmost is negative. At $x=1$ and $x=-1$ only the composition into singletons survives; hence $H(1)=1/R([m])$ and $H(-1)=(-1)^r/R([m])$. There is a sign change in every one of the $r$ intervals cut out by the nodes and the endpoints. The transformed polynomial has degree at most $r$, so every root is simple, and the inverse substitution puts them all in $(-\infty,0)$. Rodrigues' formula gives $(1-t)^m L_m((1+t)/(1-t))=D_m(t)$, proving the asserted strict interlacing. All signs are independent of the shape, which proves the assertion on mixtures as well.

## Source of the path model

For clarity, one can recover the unweighted input in Section 1 from the snake subdivision as follows. The internal-face bijection in [Aydin et al., §4.1, (3)](https://arxiv.org/abs/2611.32845) indexes faces by a connected snake and a subset of its low valleys. Each chosen valley adds a component. By [valuativity of the Z-polynomial](https://doi.org/10.1112/jlms.12984) and multiplicativity under direct sums, the face contributes the product of the component polynomials with one minus sign per chosen valley.

In north/east step notation, the two paths of a connected snake are $NpE$ and $EpN$ for one word $p$. Write $d_j$ for the number of east steps before north step $j$ of $p$, and $d_0=0$. The east offsets of the north steps of the upper snake path are $0,d_1,\ldots,d_{r-1}$ and those of the lower path are $1+d_1,\ldots,1+d_{r-1},\lambda_1$. Comparing with the containing shape, the weakly decreasing sequence $\eta_i=d_{r-i}$ satisfies $\mu_i\le\eta_i<\lambda_{i+1}$ for $1\le i<r$, with $\eta_r=0$. Conversely these constraints specify exactly the possible words $p$.

There is a valley just before north step $j$ of $p$ if $d_j>d_{j-1}$. It is low precisely if this north step of the upper snake path can move one position earlier within the parent shape, i.e. $d_j>\mu_{r-j}$. Thus the low valleys correspond to the corners $(i,\eta_i)$ with $\eta_i>\max(\eta_{i+1},\mu_i)$. They give a placement on $B$, and this is bijective: scanning from bottom to top, at an unoccupied row set $\eta_i=\max(\eta_{i+1},\mu_i)$, and at an occupied row set it to the chosen column. Flipping the lower path at the valley indexed by $j$ makes the two paths meet at rank $j$.

A connected snake of rank $a$ has the Narayana polynomial of degree $a$ for its $Z$, by the [ribbon theorem and deletion proof](https://github.com/ProgramComputer/open-math-research/blob/d27bf1897bff2f426d57bea5efdbc9fca6f17d4f/topics/ribbon-matroids/proof.md). This is the unrestricted marked Motzkin enumerator of length $a$: its gamma coefficient at $k$ is the number $\binom{a}{2k}\binom{2k}{k}/(k+1)$ of ways to insert a Dyck path of semilength $k$ among the level steps. The product for a set of chosen valleys therefore counts paths returning to zero at all the corresponding ranks. Inclusion–exclusion over that set leaves paths *positive* at every low valley of the snake. Reversing the path and exchanging up and down steps preserves its weight and turns a cut $j$ into $i=r-j$. Summing over snakes gives exactly the rook restriction in Section 1.

## Boundary and verification

This particular interlacer cannot simply be used at all widths. The circuit $U_{4,5}$ has empty board, and its normalized polynomial is $L_5^{\prime}(x)/15$ by the excursion generating function (or the Narayana formula). At the largest zero $x=\sqrt{3/5}$ of $L_3$, it is $1/50>0$ instead of negative. The circuit itself is real-rooted.

The theorem above uses inequalities for every rank, not a finite computation. `verify.py` checks the rook/path input against an independent flat-lattice recursion on small straight and skew shapes and checks the interlacer by exact signed polynomial remainders on larger examples. Run `python3 -I verify.py`. No floating-point roots are used.

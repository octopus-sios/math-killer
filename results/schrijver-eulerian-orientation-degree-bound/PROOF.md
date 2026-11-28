# Schrijver’s Eulerian orientation bound through degree six

**Theorem.** Let $G$ be a finite simple graph with all degrees even and at most six. Write $n_j$ for the number of vertices of degree $j$ and $\varepsilon(G)$ for the number of orientations in which the indegree equals the outdegree at every vertex. Then

$$
\varepsilon(G)\ \le\ 2^{n_2/3}\,24^{n_4/5}\,2640^{n_6/7}.
$$

Equality holds exactly for disjoint unions of $K_1,K_3,K_5,K_7$. In particular, a simple 6-regular graph on $n$ vertices has at most $2640^{n/7}$ Eulerian orientations, with equality exactly for unions of $K_7$.

This proves [Schrijver’s Eq. (22)](https://ir.cwi.nl/pub/10053/10053D.pdf) for maximum degree six, including mixed degrees. The degree-four regular case follows from [Bartzos–Samaris](https://arxiv.org/abs/2609.06701); [Srimani–Verstraëte–Yang, Theorem 1.5 and §7](https://arxiv.org/abs/2611.29726), handle maximum degree four by a multigraph induction and ask for the 6-regular case. The argument below uses simple graphs only; it does not assert the conjecture in higher degrees.

## 1. Four colors that detect balance

Expand one factor $z_v/z_w+z_w/z_v$ for each edge $vw$. Each monomial specifies an orientation, and the exponent of $z_v$ is its signed imbalance at $v$. Average each $z_v$ independently over $\exp(\pi i j/4)$, $j=0,1,2,3$. Every exponent is even and between $-6$ and $6$. The average of an even power in this range is zero except at exponent zero, where it is one. Thus, with $m=|E(G)|$, $n=|V(G)|$, and $C=\{0,1,2,3\}$,

$$
4^n\varepsilon(G)=2^m\sum_{\sigma:V(G)\to C}
\prod_{vw\in E(G)}\cos\!\left(\frac{\pi}{4}(\sigma(v)-\sigma(w))\right).
$$

This finite sum plays the role of the [usual Fourier integral for Eulerian orientations](https://arxiv.org/html/2409.04989v2). Take absolute values term by term. On a clique of odd order this loses nothing: opposite colors (difference two) give a zero factor, so any nonzero term uses only one color or two cyclically adjacent colors. For the pair $0,3$ the crossing edges have negative cosines, but their number is $t(s-t)$, even when the clique order $s$ is odd. All other nonzero factors are positive.

We use integer weights. Set $D_0=D_2=\sqrt{2}$, $D_1=D_3=1$, and rescale the absolute cosine matrix by $D_i D_j$:

$$
M=\begin{pmatrix}2&1&0&1\\1&1&1&0\\0&1&2&1\\1&0&1&1\end{pmatrix},
\qquad L_r=(1,2^{r/2},1,2^{r/2}).
$$

For a vertex of original degree $r$, $L_r(i)D_i^r=2^{r/2}$. The vertex factors therefore restore precisely the $2^m$ in the sum. For a graph $J$ and a vector $u_v$ of four nonnegative weights at each vertex, write

$$
Z(J;u)=\sum_{\sigma:V(J)\to C}\prod_{v}u_v(\sigma(v))
                          \prod_{vw\in E(J)}M_{\sigma(v),\sigma(w)} .
$$

With $u_v=L_{d_v}$ we have $4^n\varepsilon(G)\le Z(G;u)$, with equality on every odd clique of order at most seven. Write $h_s(u)=Z(K_s;u)$ when all vertices have the same vector. It suffices to prove

$$
Z(G;L)\ \le\ \prod_{v} h_{d_v+1}(L_{d_v})^{1/(d_v+1)}.
$$

## 2. A certificate preserved by vertex deletion

Fixing a vertex to color $x$ and deleting it multiplies its neighbors’ weight vectors by row $M_x$, entry by entry. Call this operation *pinning*, and write $u M_x$ for its result. At residual degree $k$, the possible nonzero vectors, up to positive scale, form a finite family $\mathcal F_k$. Start by putting $L_r$ in $\mathcal F_r$ for $r=0,2,4,6$. In descending order of $k$, put each nonzero $u M_x$ from $\mathcal F_k$ in $\mathcal F_{k-1}$, dividing its entries by their greatest common divisor. Repeated vectors need be kept only once. A zero vector makes the entire partition sum zero.

We assign each vector a nonnegative potential $P_k(u)$, homogeneous of degree one. Ordinarily it is the per-vertex partition sum of a clique:

$$
P_k(u)=h_{k+1}(u)^{1/(k+1)}.
$$

There is just one exception type: the support of $u$ consists of **two opposite colors**. This happens only after pinning neighbors of both colors of the other parity, so $k\le4$, and the two surviving weights are equal, say $t$. Indeed, a pin of a surviving color would kill its opposite, and all cross-parity entries of $M$ are one. If $i$ is either surviving color, use

$$
P_k(u)=tD_i^k\,2^{\beta_k},
\qquad
(\beta_0,\beta_1,\beta_2,\beta_3,\beta_4)
=\left(1,\frac34,\frac12,\frac13,\frac15\right).
$$

Set $P_k(0)=0$. In particular $P_0(u)=\sum_i u(i)$. The exception has a purpose. If the two ends of an edge have lists $(1,0,1,0)$ and $(0,1,0,1)$, all four choices across the edge have weight one. The ordinary clique potentials give a product of only $2\sqrt{2}$; the corrected ones give four. The initial full-support lists never receive a correction.

**Finite lemma.** For $1\le b\le a\le6$, $u\in\mathcal F_a$ and $v\in\mathcal F_b$,

$$
\sum_{x\in C} u(x)P_{b-1}(vM_x)^a
    \ \le\ P_a(u)\,P_b(v)^a. \tag{1}
$$

This also holds for positive multiples of the vectors. Two strict cases are needed:

1. $a,b\in\{2,4,6\}$, $a>b$, $u=L_a$, $v=L_b$.
2. $a\in\{2,4,6\}$, $b=a-1$, $u=L_a$, $v=L_a M_y$, for every $y\in C$.

The exact verification of the lemma is given in §4.

**Induction.** We claim $Z(J;u)\le\prod_v P_{k_v}(u_v)$ for every residual simple graph with admissible lists, where $k_v$ is the degree in $J$. This deletion argument adapts the local Hölder step of [Sah–Sawhney–Stoner–Zhao, §5](https://arxiv.org/abs/1809.09462). We use (1), not their positive-semidefinite target theorem.

Edgeless graphs give equality by the formula for $P_0$. Otherwise delete a vertex $w$ of maximum degree $a$. For each fixed color $x$ at $w$ the induction hypothesis applies to the new lists; every neighbor’s degree drops by exactly one, since the graph is simple. The factors for vertices outside the closed neighborhood are unchanged. The remaining sum to bound is

$$
\sum_x u_w(x)\prod_{v\sim w}P_{k_v-1}(u_v M_x)
\ \le\ \prod_{v\sim w}
 \left(\sum_x u_w(x)P_{k_v-1}(u_v M_x)^a\right)^{1/a}.
$$

This is Hölder’s inequality for the $a$ neighbors with common measure $u_w(x)$. Apply (1) in each factor, with $b=k_v\le a$. The result is $P_a(u_w)\prod_{v\sim w}P_{k_v}(u_v)$, as required. Substituting the initial lists gives the desired product of clique bounds. At no stage is there a restriction on the order of $G$.

## 3. Equality

Work componentwise. In a connected graph of nonconstant degrees, some vertex of maximum degree borders a vertex of smaller degree. Delete that maximum-degree vertex first. All initial lists are positive and strict case 1 applies on the edge in question, so the bound is strict.

In a connected regular nonclique choose an induced path $w,v,z$ of length two. Delete $w$ first. In every resulting color branch, $z$ still has the maximum degree $a$, while $v$ has degree $a-1$ and list $L_aM_y$ for the color $y$ at $w$. Delete $z$ next. Strict case 2 applies on $zv$; all residual vertex potentials are positive since each list is nonzero. Hence the first deletion sums strictly smaller bounds. A connected degree-zero graph is $K_1$. Conversely, the Fourier bound and the clique product are both exact for each of the four listed cliques, and counts multiply over components.

## 4. Exact verification

[verify.py](verify.py) checks the finite lemma and the clique constants with standard-library integer and rational arithmetic. Run from this directory:

~~~sh
python3 -I verify.py
~~~

* **Coverage.** The numbers of distinct primitive nonzero lists for $k=0,\ldots,6$ are $39,34,27,22,11,4,1$. For each $a,b$ in (1) the checker takes the full Cartesian product $\mathcal F_a\times\mathcal F_b$: **6,154 inequalities** (5,971 strict, 183 equal), not a sample of graphs. It separately requires strict signs for the two families in the lemma.
* **Clique sums.** Sum the monochromatic terms, then the two-color terms over the four unordered cyclically adjacent pairs. If $i$ is used $t$ times, its within-color contribution is $u(i)^t M_{ii}^{\binom{t}{2}}$; all cross factors for adjacent colors are one. The multiplicity of a two-color term on $s$ vertices is $\binom{s}{t}$ for $1\le t<s$.
* **Comparison.** Each potential is a positive integer root of a nonnegative integer, meaning it has the form $A^{1/j}$ with integer $j\ge1$. Take a common multiple $m'$ of the root indices in (1). Divide by the positive right-hand side: the left side becomes a sum of four roots $(N_x/B)^{1/m'}$ with integer numerators and denominator. The checker brackets each root between consecutive multiples of $2^{-24}$ by integer powering and binary search. If the resulting sum interval contains one, it extracts and checks exact rational roots of the reduced fractions; an unresolved comparison is an error, never a pass. As a mutation test it replaces $\beta_3=1/3$ by $1/4$; this **reverses** (1) for $a=4$, $u=L_4$, $b=3$, $v=(1,0,1,0)$.
* **Clique benchmarks.** Independently of the spin model, the verifier counts labeled tournaments: choose the outneighbors of the first vertex and recurse on the remaining required outdegrees. It obtains $\varepsilon(K_1),\varepsilon(K_3),\varepsilon(K_5),\varepsilon(K_7)=1,2,24,2640$, respectively, and checks $h_s(L_{s-1})=4^s\varepsilon(K_s)$ in each case.

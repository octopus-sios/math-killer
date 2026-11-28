# Schrijver’s Eulerian orientation bound through degree eight

**Theorem 1 (mixed degrees).** Let $G$ be a finite simple graph with all degrees even and at most eight. Write $n_j$ for its number of vertices of degree $j$ and $\varepsilon(G)$ for the number of balanced orientations. Then

$$
\varepsilon(G)\le 2^{n_2/3}\,24^{n_4/5}\,2640^{n_6/7}\,3230080^{n_8/9}.
$$

Equality holds exactly for disjoint unions of $K_1,K_3,K_5,K_7,K_9$.

**Theorem 2 (regular degrees eight and ten).** Let $G$ be a finite simple $d$-regular graph on $n$ vertices. Write $\varepsilon(G)$ for the number of edge orientations with equal indegree and outdegree at every vertex. Then

$$
\begin{aligned}
d=8:\quad &\varepsilon(G)\le 3230080^{n/9},\\
d=10:\quad &\varepsilon(G)\le 48251508480^{n/11}.
\end{aligned}
$$

In each case equality holds exactly for disjoint unions of complete graphs on $d+1$ vertices.

**Theorem 3.** For a finite simple **triangle-free** graph with all degrees even and at most ten,

$$
\varepsilon(G)\le\prod_{v\in V(G)} c_{d_v},
\qquad c_j=\varepsilon(K_{j+1})^{1/(j+1)}.
$$

The inequality is strict if $G$ has an edge. A degree-ten corollary allowing triangles follows at the end.

These are cases of [Schrijver’s Eq. (22)](https://ir.cwi.nl/pub/10053/10053D.pdf), also [Conjecture B of Srimani–Verstraëte–Yang](https://arxiv.org/html/2611.29726v1). The unrestricted mixed-degree bound through ten and the all-degrees conjecture are not claimed. Unlike the [degree-six argument](../schrijver-eulerian-orientation-degree-bound/PROOF.md), the spin bound here is **not** exact on cliques. The point is to remove clique components first and recover the loss on every other component by choosing the order of vertex deletions.

## 1. An integer upper bound from five phases

Put $C=\{0,1,2,3,4\}$. Expand one factor $z_u/z_v+z_v/z_u$ per edge. Each choice of terms gives an orientation, and the exponent at each vertex is its signed imbalance. All exponents are even. As in the [Fourier integral for Eulerian orientations](https://arxiv.org/abs/2309.15473), the desired count is the constant term. Independently average each $z_v$ over the five values $\exp(\pi i x/5)$, $x\in C$. An even power averages to one if its exponent is divisible by ten, and to zero otherwise. Thus the average counts orientations whose imbalances are all multiples of ten. This equals $\varepsilon(G)$ at degree eight and is an **upper** bound at degree ten: imbalances $\pm10$ introduce extra orientations, not negative terms.

The factor for a pair of phases is $2\cos(\pi(x-y)/5)$. Taking its absolute value gives one of $2,\phi,\phi-1$, where $\phi=(1+\sqrt5)/2$. Write $B=987$. Since $1597^2-1597B-B^2=1$, we have $\phi<1597/B$ and $\phi-1<610/B$. Use the symmetric circulant integer matrix $M$ with first row $(2B,1597,610,610,1597)$. For a graph $J$ and fields $u_v:C\to\mathbb R_{\ge0}$ define

$$
Z(J;u)=\sum_{\sigma:V(J)\to C}\prod_v u_v(\sigma(v))
                     \prod_{vw\in E(J)} M_{\sigma(v),\sigma(w)}.
$$

In particular, for a $d$-regular graph,

$$
\varepsilon(G)\le \frac{Z(G;\mathbf1)}{5^n B^{dn/2}}. \tag{1}
$$

The loss is real even before rational rounding. On each odd clique of order $s\ge3$, phases $0,2,4$ with multiplicities $s-2,1,1$ produce a negative term. For $s=5,7,9$, the unnormalized **absolute** sums for the unrounded kernel are respectively

$$
59240+13600\phi,\quad
172254640+23418080\phi,\quad
5494352186240+515005501440\phi.
$$

The corresponding signed sums are $5^s\varepsilon(K_s)$. The verifier computes both by summing over the five color multiplicities with multinomial weights.

## 2. A local inequality with a one-percent saving

Fix one of $d=8,10$. When deleting a vertex whose color is fixed to $x$, each remaining neighbor acquires a factor $M_{ix}$ at color $i$. At residual degree $k$ record the multiplicities $s=(s_0,\ldots,s_4)$ of its deleted neighbors’ colors. The possible records are contained in
$\mathcal F_k=\{s\in\mathbb Z_{\ge0}^5:\sum_i s_i=d-k\}$.
The field is $u_s(i)=\prod_j M_{ij}^{s_j}$. Pinning to $x$ changes $s$ to $s+e_x$, where $e_x$ is the coordinate vector. In particular $s=0$ at residual degree $d$.

**Finite lemma.** There are positive integer potentials $P(s)$ (separate systems for the two values of $d$) such that:

1. For $t\in\mathcal F_0$, $P(t)=\sum_x u_t(x)$.
2. For $1\le b\le a\le d$, $s\in\mathcal F_a$ and $t\in\mathcal F_b$,

$$
\sum_x u_s(x)P(t+e_x)^a \ \le\ P(s)P(t)^a. \tag{2}
$$

   If $a=d$ and $b<d$, the right hand side can be multiplied by $(99/100)^d$.
3. At the initial record, $P(0)\le(1001/1000)\,5 B^{d/2} c_d$.

**Exact verification.** [verify.py](verify.py) constructs the integers and checks these three conditions directly. Here is how to reproduce the construction. Let $H_k(s)$ be the partition sum of $K_{k+1}$ with field $u_s$ at every vertex; fixing one color gives

$$
H_0(s)=\sum_x u_s(x),\qquad H_k(s)=\sum_x u_s(x)H_{k-1}(s+e_x).
$$

Use the provisional lower weights $L(s)=\lfloor H_k(s)^{1/(k+1)}\rfloor$. Set $P=L$ in layer zero. Build layers $b=1,\ldots,d$ in increasing order. For a target $t\in\mathcal F_b$, and each source $s\in\mathcal F_a$, $a\ge b$, put $A=\sum_x u_s(x)P(t+e_x)^a$. Take $P(t)$ to be the maximum of $L(t)$ and the following integers over those sources:

* If $a=b$ and $s,t$ are in the same orbit of rotations and reflections of the five colors, use $\lceil A^{1/(a+1)}\rceil$.
* Otherwise use $\lceil (A/L(s))^{1/a}\rceil$.

All children in $A$ are already constructed; the first case uses the invariance $P(s)=P(t)$, and the second uses $P(s)\ge L(s)$. The verifier constructs one target per orbit, then **tests all ordered pairs of records** without quotienting:

| $d$ | $P(0)$ | tests of (2) | stronger tests at $a=d$, $b<d$ |
|---:|---:|---:|---:|
| 8 | 25106708970413 | 401258 | 791 |
| 10 | 43874067142008295 | 2469753 | 2001 |

The initial bound is tested by raising positive quantities to $d+1$. The tournament counts are obtained independently: choose the outneighbors of the first vertex and recurse on the remaining target outdegrees. As a mutation control, replacing $99/100$ by $97/100$ **reverses** the strengthened inequality for $a=d$, $b=d-1$ and $t=e_0$ in both systems. Run all checks with:

~~~sh
python3 -I verify.py
~~~

## 3. Deleting an independent set pays for the initial excess

Take a fixed maximum-residual-degree deletion order, choosing ties as desired. At a step deleting $w$ of degree $a>0$, let $s$ be its record and let $t_v$ be the current record of neighbor $v$. If each remaining branch is bounded by the product of its potentials, the only factors to compare at this step are bounded by Hölder as

$$
\sum_x u_s(x)\prod_{v\sim w} P(t_v+e_x)
 \le \prod_{v\sim w}\left(\sum_x u_s(x)P(t_v+e_x)^a\right)^{1/a}.
$$

Inequality (2) bounds the product by $P(s)\prod_{v\sim w}P(t_v)$. Each incidence with $a=d$ and neighbor of residual degree less than $d$ contributes a further factor $99/100$. These stronger comparisons hold for **every** record at those degrees. Their number depends on the order, not on the chosen colors. Edgeless residual graphs are exact by part 1 of the lemma. Backward induction along the order therefore gives

$$
Z(G;\mathbf1)\le P(0)^n(99/100)^T, \tag{3}
$$

where $T$ counts the indicated incidences. This max-degree Hölder step adapts the deletion argument of [Sah–Sawhney–Stoner–Zhao, §5](https://arxiv.org/abs/1809.09462); it does not require $M$ to be positive semidefinite.

Now suppose $G$ is connected and is not $K_{d+1}$. By [Brooks’s theorem](https://doi.org/10.1017/S030500410002168X) it is $d$-colorable. Extend a largest color class to a maximal independent set $I$. We have $|I|\ge n/d$. Delete the vertices of $I$ first. Each is still of degree $d$ when deleted, so this is a valid initial segment of the order. It sends $d|I|$ pins to the $n-|I|$ outside vertices. Every outside vertex receives a first pin, by maximality; every subsequent pin there is to a vertex of residual degree less than $d$. Hence

$$
T\ \ge\ d|I|-(n-|I|)\ \ge\ n/d.
$$

Combining (1) and (3) gives the explicit gap

$$
\varepsilon(G)\le c_d^n\left[(1001/1000)^d(99/100)\right]^{n/d}
<c_d^n,
$$

since $99\cdot1001^d<100\cdot1000^d$ for $d=8,10$. The clique itself gives equality by the definition of $c_d$, without using (1). Counts multiply across components. This proves Theorem 2.

## 4. Different grids at low and high vertices

We now prove the full degree-sequence bound through eight. The regular argument indicates what a mixed certificate must do: allow a small excess **only at degree eight**, and save a fixed factor when an independent set of degree-eight vertices is deleted. Five phases everywhere would not even give the right initial constants at low cliques.

Use type $h=4$ at vertices of original degrees $0,2,4,6$, and type $h=5$ at original degree eight, with angles $\pi i/h$ for $0\le i<h$. The signed average now counts balanced orientations exactly: at each vertex no nonzero possible imbalance survives its own filter. Set $D=10^{12}$, $S_{4,i}=\sqrt2$ for odd $i$, and all other $S_{h,i}=1$. Use nonnegative integer edge matrices satisfying

$$
M^{ht}_{ij}\ \ge\ \frac{2D|\cos(\pi i/h-\pi j/t)|}{S_{h,i}S_{t,j}}.
$$

Here $M^{44}=D N$ with $N$ as in §5, and $M^{55}$ has circulant first row $(2D,p,p-D,p-D,p)$, where $p=1618033988750$. For $h=4,t=5$ the entry depends only on the distance $k$ from $5i-4j$ to the nearest multiple of $20$. The entries for $k=0,\ldots,10$ are

~~~text
2000000000000 1396802246668 1902113032591 1260073510671 1618033988750
1000000000000 1175570504585 642039521921 618033988750 221231742083 0
~~~

Use the transpose in the reverse direction. The checker generates the entries by integer square-root enclosures: start with the values $2\cos(k\pi/5)$ in $\mathbb Z[\phi]$, then use the half-angle formula twice, changing the sign of $2\cos(k\pi/10)$ for $k>5$. The square of the divisor $S_{4,i}$ is two exactly when $k$ is odd. The initial field at original degree $r$ is $L(i)=S_{h,i}^r$. Thus it is $(1,2^{r/2},1,2^{r/2})$ at type four and $\mathbf1$ at type five. Multiplying the edge majorants and restoring the $S$ factors gives

$$
\varepsilon(G)\le\frac{Z(G;L)}{D^{|E(G)|}\prod_v h_v}, \tag{4}
$$

where the partition sum uses the indicated edge types.

**Mixed finite lemma.** At residual degree $b$ and type $t$, form the finite set of primitive nonzero fields as follows. Begin with all initial fields at their original degrees. When a deleted neighbor of type $h$ has color $x$, multiply $v$ coordinatewise by the row $M_x^{ht}$, pass to layer $b-1$, and divide by the gcd of the entries. A zero field gives partition sum zero. Retain two flags: whether a field can be obtained using only four-color pins from a type-four initial field, and whether it can be obtained from any initial field using only five-color pins (including no pins). Union the flags when primitive fields coincide.

There are positive homogeneous potentials $P_b(v)$ on these fields and their positive multiples satisfying:

* $P_0(v)=\sum_i v_i$. For $1\le b\le a\le8$, any source field $u$ of type $h$ and residual degree $a$, and any target field $v$ of type $t$ and degree $b$,

$$
\sum_x u_x P_{b-1}(v M_x^{ht})^a \le P_a(u)P_b(v)^a. \tag{5}
$$

  Here $v M_x^{ht}$ denotes the **unnormalized** coordinatewise product; the zero-field potential is zero. When $a=8$, $b<8$ and the target has the five-color-only flag, the right hand side may be multiplied by $(987/1000)^8$.
* Initially, $P_r(L)=D^{r/2}\,4c_r$ for $r=0,2,4,6$, and $P_8(\mathbf1)\le D^4\,5c_8(626/625)$.

**How the finite witness is checked.** The stored quantity is the dimensionless weight $p_b(v)=P_b(v)/(D^{b/2}\max_i v_i)$. The base layer uses the exact sum. On a four-color-only type-four field, $P_b(v)/D^{b/2}$ is the [degree-six potential](../schrijver-eulerian-orientation-degree-bound/PROOF.md): the $(b+1)$-st root of the homogeneous $(b+1)$-clique sum for $N$ and $v$, except on support $\{i,i+2\}$ (indices modulo four). There the two weights are equal and the formula is $v_i N_{ii}^{b/2}2^{\beta_b}$, with $\beta=(1,3/4,1/2,1/3,1/5)$. The initial type-five $p_8$ is $5c_8(626/625)$ rounded **down** to a multiple of $2^{-58}$. All other $p_b(v)$ are positive multiples of $2^{-58}$ given by [the integer table](data/mixed-potentials.json). Each array lists numerators for the remaining fields at its degree and type, in lexicographic order of the smaller of the primitive vector and its reflection $i\mapsto-i$. Reflection preserves both grids and all matrices.

[verify.py](verify.py) regenerates the field sets from the initial vectors. If $v M_x^{ht}=g w$ with $w$ primitive, the child term in the normalized (5) is $g\max(w)p_{b-1}(w)/(D\max(v))$. Thus the test is just a sum of at most five powers, weighted by $u_x/\max(u)$, against $p_a(u)p_b(v)^a$ (including the saving when indicated). All inputs are rationals or integer roots divided by integers. The fast test uses **upper** rational enclosures on the left and **lower** ones on the right with denominator $2^{78}$. An inconclusive enclosure never passes: divide by the right side, clear the root indices and certify the individual rational roots by powering back before summing exactly. There are **3,869** free table weights and **20,537,116** local tests (587 with the stronger factor), taking one representative under reflection for the target and **every** source. Exactly 103 comparisons require the rational-root fallback. The integer table was found by fitting the inequalities in log potentials; the fit is not used in verification. Halving the table weight for a once-pinned type-five field reverses its self-comparison at residual degree seven.

**From the local lemma to all graphs.** Work componentwise. Components without a degree-eight vertex satisfy the [mixed degree-six theorem](../schrijver-eulerian-orientation-degree-bound/PROOF.md), including its equality criterion. A component $K_9$ attains equality by definition. In any other connected component with $n_8>0$ degree-eight vertices, the graph they induce is 8-colorable: each component of this induced graph either has maximum degree below eight (use greedy coloring), or satisfies Brooks’s theorem. A $K_9$ in it would already be an entire component of the original graph.

Take an independent set $I$ of at least $n_8/8$ degree-eight vertices from a largest color class. Delete all of $I$ first; they retain residual degree eight until deletion. Every neighbor field encountered has the five-color-only flag, since the only deleted vertices so far were of type five. Of the $8|I|$ incidences, the **only** ones not giving the saving in (5) are first pins at other degree-eight vertices. There are at most $n_8-|I|$ of these. In particular even a **first** pin at a low-degree vertex earns the saving. After these deletions continue in maximum-residual-degree order. Exactly the Hölder induction of §3, now using (5), bounds $Z$ by the product of initial potentials times $(987/1000)^{9|I|-n_8}$. Equation (4) gives

$$
\varepsilon(G)\le
\left(\prod_v c_{d_v}\right)
\left[(626/625)^8(987/1000)\right]^{n_8/8}
<\prod_v c_{d_v},
$$

since $987\cdot626^8<1000\cdot625^8$. This proves the mixed bound and strictness in every connected degree-eight case except $K_9$. Together with the degree-six equality criterion, the extremizers are exactly the unions of $K_1,K_3,K_5,K_7,K_9$.

## 5. Mixed degrees on triangle-free graphs

Use **four** phases $\exp(\pi i x/4)$ with uniform probability. The signed average counts orientations with imbalances divisible by eight, which again majorizes $\varepsilon(G)$. Let $W(x,y)=|2\cos(\pi(x-y)/4)|$ and let $A(J)$ be the expected product of $W$ over the edges under independent uniformly chosen phases. Then $\varepsilon(G)\le A(G)$. Remove isolated vertices; they contribute one to both sides.

For triangle-free $G$ the weighted reverse Sidorenko inequality of [Sah–Sawhney–Stoner–Zhao, Theorem 1.12](https://arxiv.org/pdf/1809.09462) gives

$$
A(G)\le \prod_{vw\in E(G)} A(K_{d_v,d_w})^{1/(d_vd_w)}.
$$

It remains to check $A(K_{a,b})<c_a^b c_b^a$ for the 15 unordered pairs of positive even degrees at most ten. Indeed, after taking the $1/(ab)$ power, the endpoint factors are $c_a^{1/a}$ and $c_b^{1/b}$; each vertex receives exactly its degree many factors.

For the integer check write $W_{ij}=S_i N_{ij} S_j$, where $S=(1,\sqrt2,1,\sqrt2)$, $N$ has diagonal $(2,1,2,1)$, cyclically adjacent entries one and opposite entries zero. Then $L_k(i)=S_i^k$ is integral for even $k$. Counting color multiplicities $t$ on the side of size $a$ gives

$$
4^{a+b} A(K_{a,b})=\sum_{\sum_i t_i=a}\binom{a}{t_0,t_1,t_2,t_3}
\prod_i L_b(i)^{t_i}
\left(\sum_j L_a(j)\prod_i N_{ij}^{t_i}\right)^b .
$$

The checker raises the comparison to $(a+1)(b+1)$ and finds strict inequality in every case. This proves Theorem 3.

**A mixed-degree corollary allowing triangles.** Suppose all degrees are even and at most ten, and the edges between the degree-ten vertices and the others form a matching. The conjectured product bound holds, with equality exactly for disjoint unions of the corresponding odd cliques. Indeed, partition into the two degree classes $U=\{v:d_v=10\}$ and $V(G)\setminus U$. For an assignment of directions $z$ to the crossing edges let $f(z),g(z)$ count the completions on the respective sides. By Cauchy–Schwarz,

$$
\varepsilon(G)^2=\left(\sum_z f(z)g(z)\right)^2\le
                 \left(\sum_z f(z)^2\right)\left(\sum_z g(z)^2\right).
$$

Each sum of squares is the orientation count on two copies of that side joined at corresponding crossing-edge endpoints: reverse all orientations in the second completion. This is a bijection, since the joining edges record $z$. The matching hypothesis makes both doubled graphs simple, with original degrees unchanged. Use Theorem 2 on the degree-ten double and Theorem 1 on the other. If there is a joining edge on the degree-ten double, it belongs to no triangle, so its component is not $K_{11}$ and the bound is strict. If there are no crossing edges, use the two componentwise equality classifications.

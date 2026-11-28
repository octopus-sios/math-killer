# Schrijver’s Eulerian orientation bound for 8- and 10-regular graphs

**Theorem 1.** Let $G$ be a finite simple $d$-regular graph on $n$ vertices. Write $\varepsilon(G)$ for the number of edge orientations with equal indegree and outdegree at every vertex. Then

$$
\begin{aligned}
d=8:\quad &\varepsilon(G)\le 3230080^{n/9},\\
d=10:\quad &\varepsilon(G)\le 48251508480^{n/11}.
\end{aligned}
$$

In each case equality holds exactly for disjoint unions of complete graphs on $d+1$ vertices.

**Theorem 2.** For a finite simple **triangle-free** graph with all degrees even and at most ten,

$$
\varepsilon(G)\le\prod_{v\in V(G)} c_{d_v},
\qquad c_j=\varepsilon(K_{j+1})^{1/(j+1)}.
$$

The inequality is strict if $G$ has an edge. Another mixed-degree case, allowing triangles, follows at the end.

These are cases of [Schrijver’s Eq. (22)](https://ir.cwi.nl/pub/10053/10053D.pdf), also [Conjecture B of Srimani–Verstraëte–Yang](https://arxiv.org/html/2611.29726v1). They do not give the unrestricted mixed-degree bound through degree eight. Unlike the [degree-six argument](../schrijver-eulerian-orientation-degree-bound/PROOF.md), the spin bound here is **not** exact on cliques. The point is to remove clique components first and recover the loss on every other component by choosing the order of vertex deletions.

## 1. An integer upper bound from five phases

Put $C=\{0,1,2,3,4\}$. Expand one factor $z_u/z_v+z_v/z_u$ per edge. Each choice of terms gives an orientation, and the exponent at each vertex is its signed imbalance. All exponents are even. Independently average each $z_v$ over the five values $\exp(\pi i x/5)$, $x\in C$. An even power averages to one if its exponent is divisible by ten, and to zero otherwise. Thus the average counts orientations whose imbalances are all multiples of ten. This equals $\varepsilon(G)$ at degree eight and is an **upper** bound at degree ten: imbalances $\pm10$ introduce extra orientations, not negative terms.

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

since $99\cdot1001^d<100\cdot1000^d$ for $d=8,10$. The clique itself gives equality by the definition of $c_d$, without using (1). Counts multiply across components. This proves Theorem 1.

## 4. Mixed degrees on triangle-free graphs

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

The checker raises the comparison to $(a+1)(b+1)$ and finds strict inequality in every case. This proves Theorem 2.

**A mixed-degree corollary allowing triangles.** Suppose all degrees are even and at most eight, and the edges between the degree-eight vertices and the others form a matching. The conjectured product bound holds, with equality exactly for disjoint unions of the corresponding odd cliques. Indeed, partition into the two degree classes $U=\{v:d_v=8\}$ and $V(G)\setminus U$. For an assignment of directions $z$ to the crossing edges let $f(z),g(z)$ count the completions on the respective sides. By Cauchy–Schwarz,

$$
\varepsilon(G)^2=\left(\sum_z f(z)g(z)\right)^2\le
                 \left(\sum_z f(z)^2\right)\left(\sum_z g(z)^2\right).
$$

Each sum of squares is the orientation count on two copies of that side joined at corresponding crossing-edge endpoints: reverse all orientations in the second completion. This is a bijection, since the joining edges record $z$. The matching hypothesis makes both doubled graphs simple, with original degrees unchanged. Use Theorem 1 on the degree-eight double and the [mixed degree-six theorem](../schrijver-eulerian-orientation-degree-bound/PROOF.md) on the other. If there is a joining edge on the degree-eight double, it belongs to no triangle, so its component is not $K_9$ and the bound is strict. If there are no crossing edges, use the two componentwise equality classifications.

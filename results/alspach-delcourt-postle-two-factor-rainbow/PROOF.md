# Alspach's orthogonal matching problem: a sublogarithmic vertex surplus suffices

**Theorem.** There are absolute constants $C$ and $d_0$ with the following property. Let $d\ge d_0$ and let a simple graph on $N$ vertices be the edge-disjoint union of $d$ spanning 2-factors. If

$$
N \ge 2d + C\,\frac{\log d}{\log\log d},
$$

then some matching contains one edge from every factor.

Alspach's conjecture would dispense with the surplus hypothesis: simplicity already forces $N\ge 2d+1$. The theorem gives a full matching, not a matching short by a sublogarithmic number of edges. It does **not** resolve the minimum order or assert that the surplus is necessary.

The problem is [Delcourt–Postle, Conjecture 2.12](https://doi.org/10.1112/jlms.70660). [Munhá Correia–Pokrovskiy–Sudakov (MCPS)](https://people.math.ethz.ch/~sudakovb/rainbow-matchings-short-proofs.pdf) obtained a full matching with a surplus of $d^{3/4+o(1)}$ (Theorem 1.5) and noted in their concluding remarks how to obtain $d^{1/2+o(1)}$. Their Theorem 1.6, with no extra vertices assumed, concerns a *partial* matching. We use the random orientation and cut from their proof of that theorem, but prescribe one side of the cut to have size exactly $d$. The key is to **exchange the roles of factors and heads of arcs**: the two parts to be perfectly matched now each have size $d$, while the surplus vertices become surplus colours.

## 1. The matching input and its one-sided codegree condition

We record precisely the form of [Keevash–Pokrovskiy–Sudakov–Yepremyan (KPSY), Theorem 4.1](https://people.math.ethz.ch/~sudakovb/ryser-conjecture.pdf) we use. Consider a linear tripartite triple system with classes $A,B,S$: two distinct triples share at most one point. Its *shadows* are the three bipartite graphs on pairs of classes, a pair being adjacent when it lies in a triple. Equivalently the $A,B$ shadow is a simple properly edge-coloured graph in which $ab$ has colour $s$ when $abs$ is a triple.

**One-sided version of the matching input.** Fix $p\in(0,1]$ and a fixed sufficiently small $\eta>0$. For all sufficiently large $m$, suppose $|A|=|B|=m$, all three class sizes are $m(1\pm m^{-\eta})$, and in **each** shadow:
- every degree is $pm(1\pm m^{-\eta})$;
- each two *distinct* points on the same side have at most $p^2m(1+m^{-\eta})$ common neighbours.

There is a constant $K$ (with $p,\eta$ fixed) such that if $|S|\ge m+K\log m/\log\log m$, the triple system has a matching of size $m$.

**Justification of the one-sided version.** This is the case $G=H$ of the proof of KPSY Theorem 4.1, with only the *upper* inequality in their (P3) in all three shadows. KPSY state a two-sided (P3). The following details explain the weakening; in particular we do not assume a lower codegree follows from degree concentration.

**Random thirds (Lemma 2.6(a), Claim 4.2).** When retaining each point independently at rate $t=1/3$, the expected sizes and degrees in a sampled shadow scale by $t$ and $t^2$, respectively. For degrees, count neighbours of a fixed point whether or not that point is retained. A common neighbour of two fixed points survives in their joint neighbourhood with probability $t^3$: it and its two *different* third points must be retained. Thus an upper bound for the old codegree gives an upper bound for the new expectation, precisely at the scale $(tp)^2(tm)$. In each of these counts a point decision changes at most two summands by linearity, and there are $O(m)$ relevant decisions. Bounded differences with deviation $m^{2/3}$ and a union bound over the three shadows, all pairs and the finitely many blocks give the upper-codegree form of Claim 4.2(i), with exponent $\eta/8$ as there. The two-sided size and degree bounds are retained, also if the initial class sizes differ by $O(m^{1-\eta})$. This argument applies to every block formed by retaining one specified third of the vertices in each of $A,B$ and one specified third of the colours in $S$. Claim 4.2(ii) uses only degrees and properness.
**Edge distribution (Lemmas 2.7 and 2.8).** In a shadow with sides $L,R$, centre its adjacency matrix by subtracting $p$ from every entry. For two different columns indexed by $u,v$, their inner product is

$$
d(u,v)-p(d(u)+d(v))+p^2|L| \ \le\ 4p^2 m^{1-\eta}.
$$

This uses only the upper codegree and the two-sided degree and size estimates. For any $I\subseteq L$, $J\subseteq R$, Cauchy–Schwarz bounds the squared edge discrepancy by $|I|$ times the squared norm of the sum of the columns indexed by $J$. The diagonal contribution to that norm is at most $|L||J|$; the off-diagonal contribution needs **only the above upper bound**, since all coefficients in the column sum are $1$. This is exactly the estimate in KPSY Lemma 2.7 with their original constants. In particular Lemma 2.8, bounding the number of low-degree vertices for a set of colours by applying Lemma 2.7 to each incidence shadow, is unchanged.
**Expansion and completion.** To track where typicality enters the rest of the proof: the random expansion in Lemma 3.4 uses the edge-distribution estimate in Claim 3.5; the remaining neighbour counts there use degrees and independent sampling. Lemma 3.7 on discarded collisions requires only coloured regularity. Lemmas 3.8 and 3.9 combine those results with the purely graph-theoretic Lemma 3.3. To obtain Lemma 3.2 the residual matching estimates (Lemmas 3.10 and 2.5) likewise require only coloured regularity, i.e. the two-sided sizes and degrees, not (P3). Hence the expansion conclusion of Lemma 3.2 is available under the stated upper bounds. In Claim 4.3 the inputs in each random block are just this expansion lemma and the low-degree bound of Lemma 2.8. From Claim 4.3 on, KPSY's switching proof uses the expanding matchings, the neighbourhood bound of Claim 4.2(ii), class sizes and properness, not any lower shadow codegrees. Its six disjoint sets of unused colours, each of size of order $\log m/\log\log m$, are available by the hypothesis on $|S|$ (take $K$ large enough, including rounding). The ambient minimum-neighbourhood hypothesis of Theorem 4.1 holds since $H=G$ and degrees are $(1\pm m^{-\eta})pm$. This gives its perfect rainbow matching in the $A,B$ shadow, as asserted.

## 2. An oriented cut with controlled shadows

Write $s=N-2d$. We only need to consider $s\le d^{4/5}$, since for larger $s$ the conclusion follows from MCPS Theorem 1.5 for all sufficiently large $d$. Let $D$ be the set of factors. Independently orient every component cycle in one of its two cyclic directions, uniformly. For $i\in D$ let $\pi_i$ be its successor permutation. At each vertex, all $2d$ predecessors and successors, over all factors, are different by simplicity and edge-disjointness.

For distinct $u,v$, let $L^+(u,v)$ be the set of their common out-neighbours before cutting, and let $L^-(u,v)$ be the common in-neighbours. Both have expected size at most $N/4$. Indeed at a common neighbour $w$, two edges of different factors have independent orientations. If they have the same factor they cannot both point into $w$, nor both out of $w$. Reversing one cycle changes at most four candidates in either count; at most $2d$ cycle choices meet $u$ or $v$. By the bounded-differences inequality with deviation $d^{2/3}$, and a union bound over all pairs and both signs, we may fix orientations with

$$
|L^\pm(u,v)|\le N/4+d^{2/3}\quad\text{for every distinct }u,v.
$$

A lower estimate here would in general be false: for example, double each vertex of a 1-factorized even complete graph and replace every matching edge by the four edges between the clone pairs. In this 2-factorization the two clones of a vertex have no common out-neighbour under any cycle orientations.

Independently put each vertex into $X$ with probability $a=d/N$ and into $Y$ otherwise, with probability $b=1-a$. Keep the triples

$$
(i,x,y),\qquad x\in X,\quad y=\pi_i(x)\in Y.
$$

These give a linear triple system on $D,X,Y$: $(i,x)$ and $(i,y)$ each determine the other endpoint because $\pi_i$ is bijective, and $(x,y)$ determines at most one factor because the graph is simple.

Here are all shadow estimates. When counting the neighbours of specified points, compute the statistic regardless of the memberships of those specified points; it then gives the desired count if they lie on the side under consideration.

- A factor has expected degree $Nab$ in either incident shadow: count the arcs of its permutation from $X$ to $Y$. A tail has expected degree $db$, by counting its distinct successors in $Y$; a head has expected degree $da$, by counting its distinct predecessors in $X$. Each of the latter counts gives the degree in both relevant shadows.
- For two factors $i,j$, their common tails have expected number $Nab^2$: for each vertex $x$, the vertices $x,\pi_i(x),\pi_j(x)$ are distinct. Their common heads have expected number $Nba^2$, using the inverse permutations.
- For two different tail candidates $x,x'$, the number of common factors has expectation $db^2$: for each $i$ the two images under $\pi_i$ are different and must both be in $Y$. For two head candidates, the corresponding expectation is $da^2$.
- In the $X,Y$ shadow the common heads of two tails are the points of $L^+(x,x')$ in $Y$. The expectation is at most $b(N/4+d^{2/3})$. The common tails of two heads have expected number at most $a(N/4+d^{2/3})$.

For fixed orientations these statistics are all functions of $N$ independent membership decisions, with changes bounded by $3$ per decision. For example, in the common-tail count for two factors a changed vertex can occur as the tail or as either of two images (each has just one preimage). In the common-factor count for two tails it can be the image of either tail for at most one factor per tail. Thus simultaneously all counts deviate from their respective expectations by at most $d^{2/3}$ except with probability $O(N^2)\exp(-\Omega(d^{1/3}))$. We can also insist on **exactly** $|X|=d$: the binomial variable has integer mean $d$, a mode, so this event has probability at least $1/(N+1)$, larger than the failure probability.

Since $a,b=1/2+O(s/d)$, the degrees in the resulting shadows are $d/2+O(s+d^{2/3})$ and all same-side codegrees are at most $d/4+O(s+d^{2/3})$. The class sizes are $d,d,d+s$. As $s\le d^{4/5}$, these estimates meet the one-sided hypotheses of Section 1 with $m=d$, $p=1/2$ and a sufficiently small fixed $\eta<1/10$.

## 3. Spend the surplus on colours

Use **$D$ and $X$ as the two vertex classes**, and **$Y$ as the colour set**. The auxiliary edge $ix$ has colour $\pi_i(x)$ when that image lies in $Y$. It is properly coloured and uses all of $Y$, since each head has positive degree. The hypothesis on $N$ gives $|Y|\ge d+K\log d/\log\log d$ on taking $C\ge K$. Section 1 supplies a perfect rainbow matching between $D$ and $X$. Its $d$ distinct heads in $Y$ and $d$ distinct tails in $X$ are disjoint sets. Reading each arc back as an undirected edge uses each original factor once, giving the desired full rainbow matching.

The finite checks in the companion script exercise the change of roles and the shadow counts, including a twin-pair example where a two-sided codegree assertion would fail. The asymptotic existence statement rests on the proof above, not on those tests.

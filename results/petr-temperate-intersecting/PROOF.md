# The Petr–Turek bound throughout the upper half of the cube

Let $n=2k$ and $N_j=\binom{n}{j}$. A family is **temperate** if each member $A$ contains at most $|A|$ other members. [Petr and Turek, Conjecture 1.7](https://arxiv.org/abs/2406.18437v2) ask whether the largest intersecting temperate family has size
$$
L_k=\tfrac12N_k+N_{k+1}+\binom{2k-1}{k+2}.
$$

**Theorem.** If every member has size **at least** $k$, the maximum is $L_k$, for every $k\ge2$. In fact, the upper bound only needs temperance and the condition that at most half the $k$-sets are used. With **no restriction on member sizes**, the exact maxima for $k=2,3,4$ are $7,26,98$. The same upper bound holds if at most one member lies below rank $k$ (see the deficit estimate below).

The unrestricted problem for $k\ge5$ is not settled here. [Williams](https://arxiv.org/abs/2609.24747) studied ranks $k,k+1,k+2$. The point of the upper-half argument below is that the same quadratic in the $k$-shadow still pays for **all** larger ranks, not just rank $k+2$.

## The construction

Take the $k$-sets containing a fixed point, every $(k+1)$-set, and the $(k+2)$-sets omitting the point. Complementation bisects the middle layer. Two middle-layer members meet at the point; all other pairs meet by their sizes. Any proper inclusion between members has rank difference one: a bottom member cannot lie in a top member. Thus each $A$ contains at most its $|A|$ immediate predecessors. This gives $L_k$.

## A bound for the entire upper tail

Write $F_j$ for the part of the family $F$ in layer $j$. Suppose $k\ge3$ and $F$ has no members smaller than $k$. Put $t=k+2$, $h=\binom{k+1}{2}$, and for every $t$-set $T$ put
$$
m(T)=|\{D\in F_k:D\subseteq T\}|,\qquad p(T)=(1-m(T)/h)^2.
$$
We first show
$$
\sum_{j\ge t}|F_j|\ \le\ N_{k+1}-|F_{k+1}|+\sum_{|T|=t}p(T). \tag{1}
$$

Take a uniformly random maximal chain, with $C_j$ its $j$-set. Let $X=\sum_{j\ge t}N_j\mathbf1_{C_j\in F}$ and $Y=N_{k+1}\mathbf1_{C_{k+1}\notin F}+N_t p(C_t)$. Their expectations are the two sides of (1). Condition on the **largest** member $A$ of $F$ on the chain. Given $A$, the chain below it is uniform in its subsets: the condition excluding larger members uses only the chain above $A$. If there is no such $A$, or $a=|A|<t$, then $X=0$.

If $a=t$, then $X=N_t$. At least $m(A)$ of its $t$ immediate predecessors are missing from $F$ by temperance. Their contribution to the conditional mean of $Y$ is at least $N_{k+1}m(A)/t=N_t m(A)/(k-1)$. This suffices because $1-p(A)\le2m(A)/h\le m(A)/(k-1)$.

Now let $a\ge t+1$. Replace $p(C_t)$ by its lower bound $1-2m(C_t)/h$. Relative to the budget $N_{k+1}+N_t$, the conditional inequality $\mathbb E[X\mid A]\le\mathbb E[Y\mid A]$ will follow if we can pay $N_a$ for $A$ itself and the following charge per strict member $D\subset A$, where $d=|D|$:
$$
\begin{cases}
N_d/\binom ad,& d\ge t,\\
N_{k+1}/\binom a{k+1},& d=k+1,\\
2N_t(t/k)/\binom ak,& d=k.
\end{cases}
$$
The last charge uses $\Pr(D\subset C_t\mid A)=\binom tk/\binom ak$ and $\binom tk/h=t/k$. Each charge is at most $N_t/a$:

* For $t\le d<a$, $N_d/\binom ad$ increases weakly with $d$, so it is at most $N_{a-1}/a\le N_t/a$.
* For the other two charges, $a/\binom aj=j/\binom{a-1}{j-1}$ decreases weakly with $a$, so evaluate at $a=k+3$. After multiplication by $a/N_t$ the two bounds are respectively $2/(k-1)$ and $12/[k(k+1)]$, both at most one.

There are at most $a$ strict members, and $N_a\le N_{k+1}$. This proves (1).

## The quadratic average

For a function $f$ on $j$-sets let $(P_j f)(B)$ be its average over the immediate predecessors of a $(j+1)$-set $B$. Use the uniform probability inner product on each layer. For a mean-zero $f$,
$$
\|P_j f\|_2^2\le\frac{j(n-j-1)}{(j+1)(n-j)}\,\|f\|_2^2\qquad(0\le j<n). \tag{2}
$$
Here is a proof to specify the normalization. The adjoint averages over immediate successors. On layer $j\ge1$, counting single replacements gives
$$
(j+1)(n-j)P_j^*P_j
=j(n-j+1)P_{j-1}P_{j-1}^*+(n-2j)I .
$$
The nondiagonal terms on both sides replace one point by another once; the diagonal counts on the left and in the first term on the right are $n-j$ and $j$. The centered spaces are preserved by both averages. At $j=0$ there is no nonzero centered function. Induct using the identity: on centered functions the adjoint has the same operator norm as $P_{j-1}$, so the numerator bounding the squared norm at step $j$ is $(j-1)(n-j)+(n-2j)=j(n-j-1)$. This proves (2).

Write $\alpha=|F_k|/N_k\le1/2$ (in the intersecting case, use complementary pairs). Apply (2) twice to $\mathbf1_{F_k}-\alpha$. Its two-step average at $T$ is $m(T)/\binom tk-\alpha$, and the contraction factors telescope to $(k-2)/(k+2)$. Therefore
$$
\mathbb E_T p(T)
\le (1-(t/k)\alpha)^2+(t/k)^2\frac{k-2}{k+2}\,\alpha(1-\alpha)=:Q(\alpha).
$$
By (1), $|F|\le N_{k+1}+\alpha N_k+N_t Q(\alpha)$. The last two terms form a convex quadratic, so check its endpoints. At $\alpha=1/2$, $Q(\alpha)=(k-2)/(2k)$, giving exactly $L_k$ since $N_t(k-2)/(2k)=\binom{2k-1}{t}$. At $\alpha=0$, $Q(0)=1$ and $(t/k)N_t=[(k-1)/(k+1)]N_k\le N_k$, so the bound is no larger. It is important to keep the $\alpha N_k$ term when checking this endpoint. For $k=2$ the unrestricted bound follows below (or, under the middle-layer cap alone, the full set permits at most five members and otherwise there are at most three $2$-sets and four $3$-sets).

## What a missing face is worth

For $k\ge3$ set
$$
c=\max\left\{\frac{2(k-1)}h,\,\frac{N_{k+3}}{N_{k+1}}\right\}<1.
$$
In (1) one can multiply the term $N_{k+1}-|F_{k+1}|$ by $c$. Indeed at $a=t$ the proof only needs $c/(k-1)\ge 2/h$. At $a>t$, pay $N_a$ from $cN_{k+1}$ and the strict-member charges from $N_t$ as before (the charge at $d=k+1$ only decreases). Thus an arbitrary intersecting temperate family, with $\ell$ members below $k$ and $D=N_{k+1}-|F_{k+1}|$, satisfies
$$
|F|\le L_k+\ell-(1-c)D. \tag{3}
$$
Apply the strengthened estimate to its upper half and then put the $\ell$ members back. If $\ell=1$, intersection forces $D\ge1$, so integrality gives $|F|\le L_k$.

In the four ranks $k-1,\ldots,k+2$ there is also a uniform error bound of order $N_k/k^2$, rather than order $N_k/k$. Since there is no $a>t$, use $c_0=2(k-1)/h$ instead of $c$. Put $e=D-\ell\ge0$, the number of unrepresented complementary $(k-1,k+1)$ pairs. Count incidences from the $\ell$ low sets to all their $(k+1)$-supersets. A missing $(k+1)$-set whose complement is selected receives **no** incidences, a selected $(k+1)$-set receives at most $k+1$, and every other one receives at most $h$. Consequently
$$
h\ell\le(k+1)|F_{k+1}|+he,\qquad e\ge\max\{0,\ell-2N_{k+1}/k\}.
$$
By (3) the excess above $L_k$ is at most $c_0\ell-(1-c_0)e$. For $k\ge6$ we have $c_0\le1/2$. Below $\ell=2N_{k+1}/k$ use $e\ge0$; above it the resulting affine upper bound has slope $2c_0-1\le0$. In both cases
$$
|F|\le L_k+\frac{8(k-1)}{k^2(k+1)}\,N_{k+1}.
$$
This is an additive estimate, not sharp optimality in all four ranks.

## Exact unrestricted checks

Run `python3 verify.py` from this directory. Only the Python standard library is needed. The following reductions specify why its finite search is exhaustive.

* If the full set is present, the total size is at most $n+1$. If a singleton is present, all members contain its point. Delete the singleton and strip the point from all remaining members. Each trace of size $a$ has at most $a$ strict trace members inside it, since the original singleton used one of the $a+1$ slots. This is a temperate family on $n-1$ points. Its size is at most the sum of the two largest layers there, by Petr and Turek's Theorem 1.3 (or the weighted-chain argument in the next paragraph with $a$ slots). Adding one gives at most $7,21,71$ for $n=4,6,8$. The empty set is excluded by intersection.
* For $n=4,6$, fix which co-singletons occur. Up to relabelling only their number matters. The remaining ranks $2,\ldots,n-2$ consist of complementary pairs, with at most one side chosen. The checker branches on these choices.

On $[8]$ a $7$-set accounts for at most eight members contained in it. All others contain its omitted point. Strip this point: each trace of size $a$ contains at most $a+1$ strict trace members. Weight a random chain in the seven-dimensional cube by $\binom7j$ at each selected $j$-set. Conditioning on the largest selected trace as in (1), the conditional contribution per strict submember of size $d$ is $\binom7d/\binom ad\le\binom7{a-1}/a$. For $1\le a\le7$ the maximum of $\binom7a+(1+1/a)\binom7{a-1}$ is $315/4$, at $a=4$. (The zero-size case costs at most one.) Thus a $7$-set cannot occur in a family of size $99$.

Only ranks $2$ through $6$ remain. Write $a=|F_4|$, $b=|F_3|+|F_5|$, $c=|F_2|+|F_6|$. Complementation gives $a\le35$ and $b\le56$. The temperate LYM bound gives $a/70+b/56+c/28\le2$: conditional on the largest chain member of size $s$, each of at most $s$ nonempty strict submembers lies on the chain with probability at most $1/s$. If $a+b+c\ge99$, then $c\ge8$ and $2\ge (99+c)/56-a/280$, whence $c\le20$.

Make a graph with one edge $e$ for each occupied $2$/$6$ pair: colour it blue if $e$ itself occurs, red if its complement occurs. Blue edges intersect pairwise. Every intermediate member $X$ of size $3,4,5$ must meet every blue edge. It costs one slot in each red edge's budget for which $X$ is disjoint from that edge. Each red edge has six slots, less the number of blue edges disjoint from it. For each complementary pair in the intermediate ranks, take the cheaper cost of its allowable orientations; discard pairs with neither orientation allowable. The sum of the $99-c$ cheapest costs cannot exceed the total remaining budget.

The checker generates uncoloured graphs by adding one vertex with every possible neighbourhood, deduplicating by permuting vertices within sorted degree classes. First apply the cost test as though every edge were red: on a legal orientation the cost is unchanged by the blue edges since it must meet them, and the budget can only decrease. Just five graph types survive. After the coloured cost test there are 69 cases. The final branching keeps intersection, each member's strict-subset budget, and the number of remaining usable complementary pairs. If every live pair is needed, its sole surviving orientation, if unique, is forced. Otherwise both decisions on a live set are tried. No case extends to 99. The code also tests a feasible completion and rejects size-preserving corruptions of all three lightning witnesses.

The upper-tail estimate (1) counts **missing** $(k+1)$-sets as available budget. In an unrestricted family such a set can be absent precisely because its $(k-1)$-complement is present. Counting both the budget and that lower member would double-count the same slot. This is why the upper-half proof alone does not give the unrestricted result.

## Formalized scope

The Lean module `Conjectures.PetrTemperateIntersecting` proves the lightning lower bound for every $k\ge2$ and the unrestricted upper bound for $n=4$ (theorems `lightning_lower_bound` and `upper_four` in namespace `PetrTemperateIntersecting`). The upper-half theorem above is a written proof; the unrestricted $n=6,8$ upper bounds use the exact checker, not Lean.

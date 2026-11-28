# Equality heaps and a uniform one-eighth bound for Coxeter balance

[Gaetz and Gao, *Balance constants for Coxeter groups*](https://arxiv.org/abs/2005.09719), Question 3.10, ask which fully commutative intervals in finite Weyl groups attain the sharp lower bound $1/3$. There is an orientation issue in the question: taking the inverse of the top element reverses the heap. Once **each connected component is allowed its own order dual**, the figures in the question are exhaustive. For general convex sets, the last section gives the uniform lower bound $1/8$.

## The classification

Let $w\ne e$ be fully commutative in a finite Coxeter group (in particular, a finite Weyl group). Then $b([e,w]_L)=1/3$ if and only if every connected component of its **unlabelled poset** $H_w$ is one of the following or its order dual. The relations listed are covers, from bottom to top.

* $P_2$: the two-element chain.
* $P_4$: $a,b<c<d$ with $a,b$ incomparable.
* $P_7$: bottom points $a,b,c$, then $d$ covering $a,b$ and $f$ covering $b,c$, then $g$ covering $d,f$, then $h$ covering $g$.

These are Figure 1, Figures 2 and 3 (the same unlabelled poset), and Figure 4, respectively. In particular the answer **without duals** is no: invert the Figure 2 word $s_4s_2s_3s_1$ in type $D_4$. The resulting connected heap has four points and one minimum, whereas the four-point heap drawn has two minima. The result here is the **necessity of the list in every rank**, not just this counterexample to the literal wording. It does not resolve Conjecture 1.2 for arbitrary convex sets.

For a finite poset $P$, sample an order ideal $I$ uniformly from $J(P)$ and put $p_x=\Pr(x\in I)$. Gaetz and Gao identify the balance constant of the fully commutative interval with $\max_x\min(p_x,1-p_x)$. An ideal of a disjoint union is a tuple of independently chosen ideals; dualizing complements the ideals and changes each $p_x$ to $1-p_x$. The three shapes have respectively $3,6,15$ ideals. Their membership counts in the displayed orders are $(2,1)$, $(4,4,2,1)$, and $(10,11,10,5,5,2,1)$, giving balance $1/3$ for each. Thus sufficiency follows. For necessity we can treat one connected heap and suppose

$$
p_x\notin(1/3,2/3)\qquad\text{for every point }x.
$$

We call this the gap condition. Connectedness means connectedness of the undirected cover graph. Components are precisely the nonempty pieces on the connected components of the support in the Coxeter diagram: points of equal or neighboring labels are ordered, and all relations are generated in these columns. We can discard unused labels and work on connected full support.

## The classical heap models

We recall the part of the finite-type classification of fully commutative heaps that we use. A *column* comprises all points of one label, ordered bottom to top. On a path diagram, an *alternating* heap is one in which the chain on each pair of neighboring columns alternates between them. In type $B_r$ number the labels $s_0,\ldots,s_{r-1}$, with the 4-edge at $s_0$. Read columns from the **ordinary end** $s_{r-1}$ towards $s_0$. Ranks at most five of types $B,D$ are covered directly by the finite check; it suffices to use their descriptions below in higher rank.

1. An alternating heap has at most one point in the ordinary end column. Ordinary type $A$ heaps also have this form. Alternatively, one may regard a type $A$ heap as a type $B$ heap by relaxing one end braid length from 3 to 4: the dependency graph is unchanged and a heap avoiding convex alternating triples on that edge also avoids convex alternating quadruples.
2. The other type $B$ heaps are left peaks. For some $1\le j\le r-1$ the part on $s_j,\ldots,s_0$ is the chain with labels $s_j,\ldots,s_1,s_0,s_1,\ldots,s_j$. There is no $s_{j+1}$ between its ends. Collapsing this whole block to one $s_j$ leaves an alternating heap on $s_{r-1},\ldots,s_j$ with at most one point at the ordinary end. Equivalently the original heap **substitutes** a chain of $2j+1$ points for the single terminal point. Every outside point below (above) the terminal point is below (above) the whole block: the only adjacent outside label is $s_{j+1}$ and its occurrences lie before or after both ends.
3. In type $D_{r+1}$ the two prong labels replace $s_0$ in a type $B_r$ model. In an alternating heap one may use alternating prong labels at successive occurrences of $s_0$; this does **not** change the unlabelled poset since consecutive such occurrences are still ordered through an intervening $s_1$. There is also the option, for a single occurrence, to replace it by two incomparable twins with its outside relations. In the left peak the single $s_0$ is replaced in this latter way. Thus the nontrivial terminal substitution in type $D$ is a chain of $j$ points, followed by an incomparable pair, followed by a chain of $j$ points, in ordinal sum; here $j=0$ is allowed. Support omitting a prong reduces to a path of type $A$.

To see the ordinary-end restriction directly, two consecutive points of that label with just one neighbor between them would form a convex braid triple: every chain from the lower point into the open interval, or out to the upper point, must pass through that same neighbor. This excludes repeated end labels in the alternating region at a 3-edge. If a substituted chain is adjacent to the ordinary end and two end points enclose the block, the whole heap is itself the longer pure peak; use that description ($q=0$ below).

These are the finite-type descriptions in Biagioli–Jouhet–Nadeau, [*Fully commutative elements and lattice walks*](https://math.univ-lyon1.fr/~jouhet/fullycommut_fpsac_final.pdf), proofs of Propositions 11–12; for the left-peak conditions see also Bagno–Biagioli–Jouhet–Roichman, [Definition 3.4 and Proposition 3.6](https://elibagno.com/wp-content/uploads/2023/01/1-s2.0-S019566982100158X-main-22.pdf). The classical classification describes the heaps, not their equality cases.

## Ideals as paths with a terminal weight

For a column with $h$ points let $x$ be the number included in the ideal, between 0 and $h$. On two neighboring columns the chosen points must form an initial segment of their joint chain. Because these chains generate the heap order, this condition on every pair is sufficient. In an alternating pair the next count is either $x$ or $x+1$ if the next column starts the joint chain, and either $x-1$ or $x$ otherwise, subject only to its range. Adding an offset to the count in each column converts the successive steps into **0 or 1**: keep the offset in the former case and increase it by one in the latter.

Start with a fictitious state 0 at time 0; at time 1 the ordinary end with a single point allows states 0 and 1. Use all $q$ columns in an unsubstituted alternating heap, and only the $q$ regular columns **preceding** the substituted point in a substituted heap. (For a pure block $q=0$.) At time $t$ the states form an integer interval $[l_t,h_t]$; both endpoints advance by 0 or 1, by alternation. Every integer in it is reachable and extendible: on each side the two interleaved chains allow some compatible count in the next column. In particular $0\le l_t\le h_t\le t$, and $h_t-l_t\ge1$ for each actual column by full support. A sequence of admissible states with steps 0 or 1 is exactly a choice of compatible initial segments. In the unsubstituted model it has weight 1.

For a substitution by a poset $Z$, put $M=|J(Z)|$. The original single point was inserted at one gap in the chain of the preceding column. At the state for that gap it is free, and **every** ideal of $Z$ is possible. Below the gap $Z$ is forced empty; above the gap it is forced full. The resulting path multiplicities at time $q$ are therefore 1 except for the free state of weight $M$. The preceding column has at most one point on each side of the gap, by alternation with a single point. Thus the terminal weight vector is a truncation of $(1,M,1)$ including its middle. For $q=0$ there is just one free empty prefix.

Let $N=|J(H_w)|$. Give a regular prefix path its terminal multiplicity and normalize by $N$ to obtain the path measure. Write $K_t$ for its state. Since states are translated counts in a column, the gap condition applies to **every threshold** of $K_t$: the event $K_t\ge k$ is constant or is membership of a point of the column. Consequently there is a median $m_t$ with both strict tails of probability at most $1/3$. It is unique, and $m_0=0$, $m_t-m_{t-1}\in\{0,1\}$ since $K_{t-1}\le K_t\le K_{t-1}+1$ on every path.

For later use the suffix weight at state $i$ is the number of completions after arrival there, zero outside the admissible interval. Each suffix vector is log-concave and positive throughout its interval. At the end the vector is constant or a truncation of the three terms $1,M,1$. Earlier vectors are obtained by replacing $v_i$ by $v_i+v_{i+1}$ and truncating to an interval. The sum operation preserves log-concavity: expand the difference of the middle square and the product of its neighbors; it is the sum of $v_i^2-v_{i-1}v_{i+1}$, $v_{i+1}^2-v_iv_{i+2}$, and $v_iv_{i+1}-v_{i-1}v_{i+2}$. The last is also nonnegative by decreasing consecutive ratios on the positive interval, including the zero-boundary cases.

## Four-column obstruction

We prove that **if $q\ge4$, a median satisfying the gap condition goes straight for all $q$ steps**. By the reflection $K_t\mapsto t-K_t$, assume $m_1=0$. This reflection reverses each suffix vector, preserves the threshold condition and preserves all path weights under the reflected description. Suppose the first increment of the median is from $m_k=0$ to $m_{k+1}=1$. At least $1/3$ of the mass crosses the edge from 0 to 1 there: at time $k$ mass at 0 is at least $2/3$ and at time $k+1$ mass at 0 is at most $1/3$. Every path using that edge has an all-zero prefix of length $k$. Move its increment to any of the first $k$ steps instead. All these paths exist, since every layer up to $k$ contains 0 and 1; their suffixes, and hence their weights, are unchanged. The $k$ disjoint images are in the strict upper tail at time $k$. This gives $k/3\le1/3$, so $k=1$.

We now have $m_1=0,\ m_2=1$. Write $r_i$ for the layer-2 suffix weights. There are $1,2,1$ potential prefixes to states $0,1,2$, with unavailable states assigned weight zero. The first-column upper tail and second-column lower tail give

$$
3(r_1+r_2)\le N,\qquad 3r_0\le N,\qquad N=r_0+2r_1+r_2 .
$$

They force $r_2=0$ and $r_0=r_1=N/3$. Thus layer 2 consists exactly of states 0 and 1. Write $s_i$ for layer-3 suffix weights. The two recursions $r_0=s_0+s_1$ and $r_1=s_1+s_2$ give $s_0=s_2$. These are positive: otherwise only state 1 can occur in layer 3, contradicting its nonempty column. The layer is therefore $[0,2]$ and its prefix counts are $1,3,2$.

At layer 4 write $u_0,u_1,u_2,u_3$ for the suffix weights (zeros permitted at the ends). Both $u_1,u_2$ are positive because the endpoints of $[0,2]$ can advance only by 0 or 1. The prefix counts before killing unavailable states are $1,4,5,2$. We know

$$
u_0+u_1=u_2+u_3,\qquad N/3=u_0+2u_1+u_2,\qquad u_1^2\ge u_0u_2 .
$$

If $u_2\ge2u_1$, the first identity gives $u_0\ge u_1$, contradicting the last inequality and $u_1>0$. Hence $u_2<2u_1$. The weight of the event $K_4\le1$ is $u_0+4u_1$, **strictly between** $N/3$ and $2N/3$: subtract the middle expression above for the lower comparison and double it for the upper comparison. This violates the gap condition. It excludes the turn, proving the obstruction.

This argument uses the path-counting viewpoint familiar from width-two posets (compare [Sah](https://arxiv.org/abs/1811.01500)). The endpoint here need not be fixed: the suffix may even include a peak block. Only log-concavity of the continuation was used in the four-column calculation.

## Excluding straight medians and long peaks

In the straight case use the same reflection so the median stays at 0. At least $2/3$ of the mass reaches state 0 at time $q$, and there is only **one** prefix to it. Weight 1 cannot suffice, since $N\ge2$. This already disposes of unsubstituted heaps with $q\ge4$.

For a substituted heap let $A,B,F$ count regular prefixes forcing respectively the empty block, the full block, or neither. Then $F\ge1$ and $N=A+B+MF$. If $d_z$ is the number of ideals of $Z$ containing $z$, its count in the full heap is $B+Fd_z$.

* For a chain block ($j\ge1$), $M=2j+2\ge4$ and the $d_z$ run from 1 to $M-1$ by ones.
* For a doubled-center block with $j\ge1$, $M=2j+4$. The top chain has counts $1,\ldots,j$; each twin has count $j+2$; the bottom chain has counts $j+4,\ldots,2j+3$.

In both cases consecutive distinct global counts have gap **less than** $N/3$: in the first case $F\le N/4$, and in the second $2F\le2N/M$. The sole possible tie in the latter bound has $M=6$, $A=B=0$; then a twin has probability $1/2$ and equality is already impossible. Thus all block counts must be on the *same* side of the open middle third. Since the extreme block counts are 1 and $M-1$, this implies

$$
3(M-1)F\le N,\qquad (2M-3)F\le A+B .
$$

Indeed, use inclusion of the most frequent point if all points are rare, and omission of the least frequent if they are common. The free state has mass $MF/N\le M/(3(M-1))<2/3$. It cannot be the straight endpoint either.

The remaining block is just the two twins ($j=0$ in type $D$). Here $M=4$. Inclusion and omission of a twin each have count at least $2F$, so $4F/N\le2/3$. For the straight endpoint to carry $2/3$ it must be the free state, with $F=1$ and $N=6$. But there are at least $q$ additional paths: take a single increment at any of the first $q$ steps and end at state 1. Every layer contains 0 and 1. This gives $N\ge4+q$, impossible for $q\ge4$.

We have proved $q\le3$ in **all** classical models. In the chain and doubled-center cases with $j\ge1$ we further have $A+B+F\le2^q\le8$, so $(2M-2)F\le8$ and $M\le5$. Thus a chain peak must have $j=1$, and a doubled-center peak with $j\ge1$ is excluded altogether. An ordinary alternating heap uses at most three columns. A type $B$ chain peak has rank $q+j+1\le5$; a type $D$ substitution with $j=0$ has rank $q+2\le5$. Splitting alternating labels without changing the heap adds at most one label. This reduces **every rank** in the classical families to standard parabolics of $B_5$ or $D_5$ (including the small type $A$ paths; type $A_5$ itself can be checked via the edge relaxation in $B_5$).

## Finite remainder

The companion [exact verifier](verify.py) checks these bounded diagrams and the exceptional diagrams, including the noncrystallographic types $H_3,H_4$. Here are the counts; the last three columns count connected equality heaps with their generator labels retained, **after** checking their unlabelled poset types.

| Diagram | All FC elements including identity | $P_2$ | $P_4$ or dual | $P_7$ or dual |
|---|---:|---:|---:|---:|
| $B_5$ | 293 | 8 | 2 | 0 |
| $D_5$ | 167 | 8 | 6 | 0 |
| $E_6$ | 662 | 10 | 6 | 2 |
| $E_7$ | 2670 | 12 | 6 | 2 |
| $E_8$ | 10846 | 14 | 6 | 2 |
| $F_4$ | 106 | 6 | 4 | 0 |
| $G_2$ | 11 | 2 | 0 | 0 |
| $H_3$ | 44 | 4 | 2 | 0 |
| $H_4$ | 195 | 6 | 2 | 0 |

Here is why the finite test is exhaustive.

* Build heaps bottom to top. A new point of label $s$ sits over all points of the same or neighboring labels; the principal ideal it generates is obtained by taking the union of their principal ideals and adjoining the new point. Choose the canonical parent by deleting the maximal point whose label is greatest in a fixed numbering. Maximal points have distinct labels. In the forward construction, keep an addition only if the newly added point would be deleted by this rule.
* Use [Stembridge's FC heap criterion, Proposition 2.3](https://public.websites.umich.edu/~jrs/papers/FC.pdf): there is no equal-label cover and no convex alternating chain on neighboring labels of their braid length. Deleting a maximal point preserves the criterion. When adding a point it suffices to test violations ending there. An equal-label cover occurs precisely if a former maximal point had that label. A forbidden alternating chain must be the suffix of the joint two-label chain, and is convex precisely if its interval has exactly the braid length. These tests and the canonical parent enumerate each labelled FC heap once.
* For the induced subposet on a mask of points, split its ideals according as they contain a selected point or not. In the first summand delete its principal ideal, in the second its principal filter. This gives exact counts by integer recursion, with one ideal of the empty mask. For each connected nonempty heap the verifier checks the balance inequality by cross multiplication; at equality it checks the **entire order relation up to permutation** against the templates and their duals, not merely the number of ideals or points.

For completeness, in a dihedral group $I_2(m)$ with $m\ge3$, every nonempty fully commutative heap is a chain: the two labels do not commute. The balance of a chain of length $L$ (number of points) is $\lfloor(L+1)/2\rfloor/(L+1)$, which is $1/3$ only at $L=2$. The rank-one case has no equality. By the classification of irreducible finite Coxeter groups, this exhausts all types and proves necessity. The finite test uses only the Python standard library (`python3 verify.py`). It also independently enumerates the ideals of the templates by subsets, and rejects a four-point mutation that rewires one cover.

## A bound for arbitrary convex sets

There is also progress on the ambient problem which does **not** assume a fully commutative interval. For any nonsingleton geodesically convex $C$ in a finite Coxeter group,

$$
b(C)\ge \frac18 .
$$

In type $D_r$ we obtain $b(C)\ge 1/(2e^{7/6})$. These are lower bounds, **not** proposed optimal constants. The corresponding bounds in Gaetz–Gao's Table 1 are $1/(2e^{12})$ uniformly for Weyl groups and $1/(2e^4)$ for type $D$.

**Counting at one chamber.** Write $N=|C|$. Minimize the sum of distances to $C$ over chambers of $C$, then right translate a minimizer to $e$. Call a simple generator $s$ active if $s\in C$, and let $a$ be their number. Moving to an active neighbor changes the sum by $N-2|C_s|$, since the distance from $s$ to $w$ in the left Cayley graph is $\ell(ws)$. Thus $|C_s|\le N/2$. More generally the following count works at *any* base chamber where the sides away from it at its active walls have size at most $N/2$.

The active $C_s$ cover $C$ except for $e$: take the first step on a geodesic to each $w\ne e$. Conversely, a simple right descent of $w\in C$ can be the first such step, so its generator is active. If $a\le2$ and $N\ge3$, some $|C_s|\ge(N-1)/2\ge N/3$; the two-chamber case has balance $1/2$. If $a\ge3$, in the triangle-free diagram of a finite Coxeter group some pair $s,t$ of active generators commute. Their product lies on a shortest path between them, hence belongs to $C_s\cap C_t$. This compensates for the omitted identity and gives $\sum_s |C_s|\ge N$, so $b(C)\ge1/a$. In particular rank at most eight gives the asserted $1/8$, and rank three gives $1/3$, including for arbitrary convex sets in $H_3$.

**The cube for type $D$.** Use the standard chamber $x_1\ge\cdots\ge x_{r-1}\ge |x_r|$. Intersect the chamber union for $C$ with the cube $[-1,1]^r$, giving a full-dimensional convex body $Q$: the union is an intersection of root half-spaces by Tits' characterization. All chamber pieces have equal volume by signed permutation symmetry. Thus the volume proportions on the two sides of every root wall are exactly the two counting proportions.

Put $c=1/(2e^{7/6})$ and suppose $b(C)<c$. A half-space containing the centroid of a convex body has at least $1/e$ of its volume (Grünbaum's inequality, also the zero-displacement case of the Brunn–Minkowski estimate in Gaetz–Gao, §5.2). Since $c<1/e$, the centroid is on no root wall and lies on the majority side of each cut. Move its chamber to the standard one by the group action, preserving the cube. The preceding counting argument applies here. Since $c<1/6$ (already the cubic Taylor lower bound gives $e^{7/6}>3$), at least seven simples are active.

Let $v$ be $r+1$ times the centroid of $Q$. It is an average of signed permutations of the vector

$$
v_0=(r,r-1,\ldots,2,0).
$$

Indeed, inside the standard chamber the absolute coordinates of a uniform cube point are the decreasing order statistics of independent uniforms on $[0,1]$, with a fair sign on the smallest coordinate. The descending absolute means are $r/(r+1),\ldots,1/(r+1)$; the last signed mean is zero. In particular $v_1\le r$. For an inactive standard simple root $\alpha_i$, **every** chamber piece is on its positive side; its scaled centroid projects to a positive integer against $\alpha_i$. Hence $\langle v,\alpha_i\rangle\ge1$ for each inactive wall.

For $\alpha_i=e_i-e_{i+1}$ up to $i=r-1$ and $\alpha_r=e_{r-1}+e_r$, write $e_1=\sum_i d_i\alpha_i$. The coefficients are 1 along the stem and $1/2$ at the last two nodes. Their sum is $r-1$. Write $T$ for their sum over active nodes. Then $T\ge a-1\ge6$ and

$$
\sum_{i\ {\rm active}}d_i\langle v,\alpha_i\rangle
\le r-\bigl((r-1)-T\bigr)=T+1.
$$

There is consequently an active $\alpha$ with $0<\langle v,\alpha\rangle\le1+1/T\le7/6$. In both directions against $\alpha$, $Q$ extends at least one unit in the scalar coordinate $\langle x,\alpha\rangle$: use the standard chamber and its active neighbor, reflecting a cube point with projection 1. For $e_i-e_{i+1}$ take the point with its first $i$ coordinates 1 and the others 0; for $e_{r-1}+e_r$ take the first $r-1$ coordinates 1 and the last 0.

Apply the two-sided form of Gaetz–Gao's Brunn–Minkowski corollary in §5.2: if the projection extends to both $-1$ and $1$ and the absolute centroid projection is at most $m/(r+1)$ with $m\ge1$, both sides have volume fraction at least $1/(2e^m)$. Here $m=7/6$. The chosen wall contradicts $b(C)<c$.

Finally $1/(2e^{7/6})>1/8$ since $e^{7/6}<4$. Types $A,B,C$ already have the bound $1/(2e)$ by Gaetz–Gao and the results they cite. Every other irreducible type has rank at most eight. For a product, the reflection constraints are factorwise, convex sets are products, and the balance is the **maximum** over factors (a reflection tests one factor). A nonsingleton product has a nonsingleton factor. This proves the uniform bound.

**Lean verification scope.** In the namespace `YiboGaoWeylConvexBalance`, [`classicalHeapClassification`](../../lean/Conjectures/YiboGaoWeylConvexBalance/Shapes.lean) proves an if and only if for the classical path model above, with no bound on the number of columns, their heights, or the length of a chain or doubled-center substitution. On the left is `exactThird`: compute the column cut counts by the binary-step recursion and the block counts with the displayed terminal multiplicities; all cuts avoid the open middle third and some cut attains its boundary. On the right, the unlabelled order generated by the column and block relations is isomorphic to $P_2$, $P_4$, or the dual of $P_4$. The comparison uses all order ideals under a single permutation, so matching just the ideal counts is not enough.

The [strip proof](../../lean/Conjectures/YiboGaoWeylConvexBalance.lean) derives log-concavity from the terminal weights, checks reflection, proves `atMostThreeColumns`, and derives a finite arm bound using a block point that occurs in exactly half the block ideals. A kernel-checked exhaustion then finds six wall/block descriptions, paired by reflection. Separately, [`Ideals.chain_iff`](../../lean/Conjectures/YiboGaoWeylConvexBalance/IdealBalance.lean) proves the actual order-ideal balance criterion for chains of every length, and `templateUnion_oneThird` proves sufficiency for every nonempty finite disjoint union of $P_2,P_4,P_7$ with independent duals and arbitrary relabelling.

The Coxeter-to-heap and heap-to-weighted-path correspondences (including the interpretation of the block multiplicities), the finite-type case split, and the exceptional-type necessity census are **not** Lean theorems here. The census is checked by [the exact Python verifier](verify.py). The analytic bound for arbitrary convex sets is also outside Lean.

**Related computations.** The earlier [finite census](https://openwitness.net/p/10529) reported agreement with the figures and their duals in several bounded diagrams, including $E_6$; a [follow-up](https://www.openwitness.net/p/10816) checked small convex sets in higher ranks. These computations do not give the all-ranks reduction above. Neither this classification nor a finite census settles balance for general type $A$ posets.

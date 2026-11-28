# Which induced subgraphs can the adjacency spectrum recognize?

**Theorem (Barranca's Conjecture 2.1.2).** Among nonempty finite simple graphs, exactly $K_1$, $2K_1$, $K_2$, $K_3$, and $P_3$ are recognizable by spectrum (RS). Here $H$ is RS if every two graphs with the same adjacency characteristic polynomial agree on whether they contain an **induced** copy of $H$. Hosts may be disconnected. If order zero is admitted for the pattern, the null graph is an additional trivial case: it occurs in every host.

The conjecture is from [Emily Barranca's dissertation](https://doi.org/10.23860/diss-1678), Definition 2.1.1 (p. 23) and Conjecture 2.1.2 (p. 26). RS is different from being determined by one's own spectrum. The [double-star characterization](https://arxiv.org/abs/2506.06934) treats the latter question.

## 1. Trading an integral graph for cliques and stars

**Spectral trade.** For every graph $X$ with integral adjacency spectrum, there exist disjoint unions $L,R$ of cliques, stars and isolated vertices such that $X\sqcup L$ and $R$ are adjacency-cospectral.

For each eigenvalue of $X$, **with multiplicity**, perform these operations:

| Eigenvalue | Add to $L$ | Add to $R$ |
|---|---|---|
| $p>0$ | nothing | $K_{p+1}$ |
| $0$ | nothing | $K_1$ |
| $-r<0$ | $K_{r+1}$ and $r^2-1$ isolated vertices | $K_{1,r^2}$ |

Indeed, $K_{p+1}$ has eigenvalues $p$ once and $-1$ repeated $p$ times, by writing its adjacency matrix as $J-I$. The complete bipartite graph $K_{a,b}$ has nonzero eigenvalues $\pm\sqrt{ab}$, each once, from the two-dimensional space of part-constant vectors; the vectors summing to zero on each part are killed. In the negative row the star therefore supplies $r,-r$ and $r^2-1$ zeros. Comparing $X\sqcup L$ with $R$, all contributions other than the extra copies of $-1$ from the cliques already match. The numbers of these extra copies agree because

$$
\sum_{p>0} p = \sum_{-r<0} r
$$

with multiplicities: the adjacency matrix has trace zero. Disjoint union adds eigenvalue multiplicities.

**Induced integral host.** Given any $H$ on $n$ vertices, use the additive group $\mathbb F_2^n$ and its standard unit vectors $e_i$. Take the Cayley graph $X$ with connection set

$$
S = \{e_i+e_j : ij\in E(H)\}.
$$

This is simple and undirected. The map $i\mapsto e_i$ embeds $H$ as an induced subgraph: a weight-two vector uniquely specifies its unordered pair of coordinates. The characters $x\mapsto(-1)^{u\cdot x}$, indexed by $u\in\mathbb F_2^n$, form an orthogonal basis (a nonconstant character sums to zero by translation). The adjacency eigenvalue on character $u$ is the integer $\sum_{s\in S}(-1)^{u\cdot s}$. This is the standard cubelike-hull construction, here using the entire binary group rather than a single parity class; see [Mančinska, Pivotto, Roberson, and Royle](https://arxiv.org/abs/1808.02051).

Together the two facts give hosts $X\sqcup L,R$ such that the first contains $H$ and the second is a disjoint union of cliques and stars. If $H$ is connected, an induced copy in the second would lie in **one** component. A nonempty connected induced subgraph of a clique is a clique, and one of a star is a star or a singleton. Hence **no connected graph other than a clique or a star is RS**.

## 2. Large cliques and stars

These exclusions are already implied by Barranca's Theorems 2.2.2 and 2.4.1. Here are explicit witnesses, independent of switching.

* For $m\ge 3$, take $K_{1,2(m-1)}$ and $K_{2,m-1}$, adding isolated vertices to the smaller host to equalize orders. Their nonzero spectra are identical. The first contains $K_{1,m}$, whereas the maximum degree in the second is $m-1$.
* For $d\ge 3$, take the two hosts below, again adding isolates to equalize orders:

$$
K_{d+1}\sqcup K_{d-1,d-1}
\quad\text{and}\quad
K_d\sqcup B_d,\qquad B_d=K_{1,1,d(d-1)/2}.
$$

To see the spectrum of the book $B_d$, put $t=d(d-1)/2$. The difference of the two singleton-part vectors has eigenvalue $-1$, and the vectors supported on the large part with coordinate sum zero are killed. On vectors taking one common value at both singleton parts and one value on the large part, adjacency acts by the matrix with rows $(1,t)$ and $(2,0)$. Its characteristic polynomial is $x^2-x-2t=(x-d)(x+d-1)$. Thus the two displayed hosts have the same nonzero eigenvalues with multiplicities. The first contains $K_{d+1}$; the largest clique on the right has order $d$, since the book is tripartite.

Consequently the only possible connected RS patterns are $K_1,K_2,P_3,K_3$.

## 3. Disconnected patterns: cancellation and ten seeds

**Cancellation.** For finite graphs $F,G,T$, $F\sqcup T$ embeds induced in $G\sqcup T$ if and only if $F$ embeds induced in $G$.

Only the forward direction needs proof. First take $T$ connected and nonempty. If the image of the source $T$ is in the target $T$, it exhausts that summand, so the image of $F$ lies in $G$. Otherwise the source $T$ is entirely in $G$. Its image there is an induced copy of $T$ anticomplete to the image of $F$ in $G$. Relocate the vertices of $F$ that landed in the target $T$ into this reserved copy, via the isomorphism from $T$ to its image in $G$. They retain all adjacencies and nonadjacencies among themselves and have no edges to the unmoved vertices. This gives the required induced embedding. Cancel the connected components of arbitrary $T$ one at a time.

It follows that if $F$ is not RS, then $F\sqcup T$ is not RS for **every** $T$: add $T$ to both witnesses. Thus if any component is not RS, we are done. Otherwise every component is one of the four connected possibilities. If all are singletons, it suffices to exclude $3K_1$. In any other disconnected case, choose a nonsingleton and any other component. It remains only to exclude the nine two-component patterns other than $2K_1$.

Here is the entire finite certificate. Vertices of each host are $0,\ldots,n-1$; a token $ij$ denotes the undirected edge between digits $i$ and $j$. In each row $A,B$ are cospectral and only $A$ contains the indicated pattern(s).

| Pattern | $n$ | Edges of $A$ | Edges of $B$ |
|---|---:|---|---|
| $K_2\sqcup K_1$, $P_3\sqcup K_1$ | 5 | 03 04 13 14 | 04 14 24 34 |
| $P_3\sqcup K_2$ | 6 | 04 15 25 35 | 03 05 14 15 |
| $2K_2$ | 6 | 03 14 15 24 25 | 04 14 25 35 45 |
| $K_3\sqcup K_2$ | 6 | 03 14 15 24 25 45 | 03 05 14 15 35 45 |
| $K_3\sqcup K_1$ | 6 | 03 04 05 13 24 35 45 | 03 05 14 15 25 35 45 |
| $2P_3$ | 7 | 04 06 14 16 25 26 35 46 | 04 06 15 16 25 35 46 56 |
| $3K_1$ | 7 | 03 04 05 06 14 15 16 24 25 26 34 35 36 45 46 56 | 02 03 04 05 06 12 13 14 15 16 24 25 26 45 46 56 |
| $P_3\sqcup K_3$ | 8 | 05 07 16 26 37 47 57 | 05 07 15 26 27 36 57 |
| $2K_3$ | 8 | 04 05 16 17 26 27 36 37 45 67 | 03 04 07 15 16 25 26 34 37 47 |

For reproducibility, [verify.py](verify.py) multiplies adjacency matrices over the integers and recovers every characteristic coefficient by Newton's identities. It tests induced injections by extending a partial image one vertex at a time, enforcing edges **and** nonedges. Run `python3 verify.py`; no dependencies or graph databases are needed. It also implements the general construction and tests both a perturbed edge and reversed witness orientation.

## 4. The positive cases

The spectrum gives the order, edge count and triangle count (the latter two are $\operatorname{tr}(A^2)/2$ and $\operatorname{tr}(A^3)/6$). These recognize $K_1,K_2,K_3$ and also $2K_1$, which occurs precisely when the graph is not complete. Finally, $P_3$-free graphs are exactly disjoint unions of cliques: in a connected nonclique a shortest path between nonadjacent vertices starts with an induced $P_3$. On a union of cliques, $A+I$ is positive semidefinite since every diagonal block is all ones. On an induced $P_3$ its quadratic form on $(1,-2,1)$ supported on that path is negative. Thus the spectrum also recognizes $P_3$. This exhausts the nonempty patterns.

## Verification scope

[The Lean theorem `Barranca.recognizable_iff`](../../lean/Conjectures/BarrancaInducedSubgraphSpectral.lean) proves the full classification above, in both directions, for every nonempty finite simple graph up to isomorphism. Its definition of `RS` quantifies over arbitrary finite hosts with equal **integer adjacency characteristic polynomials**; `Has` means an induced embedding, not just a graph homomorphism. The companion theorem `rs_iff_listed` allows the null pattern and includes it as the sixth case.

The proof includes the cubelike host and Walsh diagonalization, the integral-spectrum trade, the unbounded clique and star exclusions, disjoint-union cancellation, and recognition of all five small patterns. For the ten disconnected seeds (nine distinct host pairs), [the finite certificates](../../lean/Conjectures/Barranca/Seeds.lean) check actual coefficient lists against a Laplace expansion proved equal to the determinant of the characteristic matrix over $\mathbb Z[X]$. They also check each positive induced injection and exclude injections into the other host by a proved backtracking test. These are kernel computations; the Lean classification does not assume the output of the Python verifier.

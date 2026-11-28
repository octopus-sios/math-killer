# Full Ramsey chains through order ten and in almost all colourings

A full Ramsey chain in a red/blue $K_n$ partitions the edges into monochromatic links of sizes $1,\ldots,n-1$, each isomorphic to a subgraph of the next. Different links may have different colours. [Chatterjee–Zhang, Conjecture 2.6](https://doi.org/10.61091/jcmcc129-01) asks whether every colouring has such a chain; the paper reports the unrestricted result through $n=6$.

**Results.**

1. $AR(K_n)=n-1$ for every $3\le n\le10$, with **no restriction on the colouring**.
2. For fixed $0<p<1$, independent red/blue colours with red probability $p$ admit a full chain ending in a Hamilton path with failure probability at most $\exp(-\Omega_p(n))$. In fact one prescribed sequence of shapes works for all sufficiently quasirandom dense colourings of each order.
3. For all sufficiently large $n$, one colour class of bounded maximum degree suffices. Also, for each fixed degeneracy bound $D$, a nonempty $D$-degenerate colour class of size at most $n-1$ and maximum degree at most $c_Dn/\log n$ can be used intact as a link. This includes forests in that degree range.
4. At **every** order, the nonempty edge sets that can occur intact as a link with a Hamilton path as last link are exactly the linear forests.

The first result is computational; the other three are proved below without computation.

## Unrestricted finite census

Represent the red edges by a bit mask, with bit $\binom v2+u$ for edge $\{u,v\}$, $0\le u<v<n$. Swap colours if necessary so that the red size $r$ is at most $\binom n2/2$. At equality we allow both a graph and its complement.

**Coverage.** Delete a vertex of maximum red degree $d\ge2r/n$. The remaining graph has at most $r(1-2/n)\le(n-1)(n-2)/4$ red edges. Starting with one vertex, the checker takes each retained graph of order $n-1$ and adjoins a vertex with **every** possible neighbourhood. It keeps a child if its edge count is at most half and the new vertex has maximum degree (ties allowed). By induction every required graph occurs up to relabelling. For deduplication the checker refines vertex classes by neighbour counts, individualizes vertices to break ties, and records the adjacency mask in the resulting vertex order. Only the fact that this operation returns a *relabelling* is needed: failing to identify two isomorphic records would produce extra work, not omit a colouring.

**Witnesses.** For every retained red mask the search must produce link masks $M_i$ and vertex maps $\pi_i$. An independent predicate checks the sizes, disjointness, exact union, and monochromaticity against the input. For each transition it verifies that $\pi_i$ permutes the vertices and that it carries every edge of $M_i$ to an edge of $M_{i+1}$. The search first tries paths and then other terminal shapes, successively deleting an edge and embedding the remainder in an unused colour class. The search budgets affect only how to find witnesses. No failed search can pass the checker.

| Order | Red graph representatives checked | Failed |
|---:|---:|---:|
| 3 | 2 | 0 |
| 4 | 7 | 0 |
| 5 | 20 | 0 |
| 6 | 78 | 0 |
| 7 | 522 | 0 |
| 8 | 6,996 | 0 |
| 9 | 154,354 | 0 |
| 10 | 6,002,584 | 0 |

As a second check, for a vertex permutation let $d_1,\ldots,d_s$ be its orbit lengths on unordered pairs. Its invariant red sets are counted by $\prod_j(1+z^{d_j})$. Summing coefficients up to half the edge count and averaging over vertex permutations gives the counts above by Burnside's lemma. Since a chain cannot exceed length $n-1$ by edge count, the witnesses give equality.

## Large orders: pack the colours separately

Use [Allen–Böttcher–Clemens–Taraz (ABCT), Definition 1 and Theorem 2](https://arxiv.org/pdf/1906.11558). Write $p_H=e(H)/\binom n2$. A $(\xi,k)$-quasirandom host has $(1\pm\xi)p_H^\ell n$ common neighbours for every set of $\ell$ vertices, $1\le\ell\le k$. Fix an integer $D\ge1$ and positive $\mu,p_0$. ABCT gives constants $\xi,c>0$ such that, for large $n$, a $(\xi,4D+7)$-quasirandom host of density at least $p_0$ packs a family of $D$-degenerate graphs of maximum degree at most $cn/\log n$ under the following conditions:
- each guest has at most $n$ vertices and the total guest edge count is at most the host edge count;
- at least $h=\lfloor\mu n\rfloor$ guests each have at most $n-h$ vertices and at least $h$ leaves.

Indeed, put $h$ such special guests last, pad them with isolates to order $n-h$, and pad the others to order $n$. This is ABCT's required sequence. After packing, discard the isolates. Equality of edge counts gives a decomposition.

**Dense quasirandom colours.** Fix $0<p_0\le1/2$. Order the edges of a path on $n$ vertices with a maximum matching first, and let $H_i$ consist of the first $i$ edges without isolates. Thus $H_i=iK_2$ up to $i=\lfloor n/2\rfloor$ and the shapes are nested. Both colour graphs being $(\xi,11)$-quasirandom of density at least $p_0$ suffices for this profile, for suitable $\xi>0$ and all large $n$.

Take $\mu=p_0/100$, $h=\lfloor\mu n\rfloor$. Reserve the $h$ indices $h,\ldots,2h-1$ for red and $2h,\ldots,3h-1$ for blue. Each gives a matching on at most $6h\le n-h$ vertices with at least $h$ leaves. Each reserved sum is at most $3h^2<p_0\binom n2$. The remaining indices realize **every** subset sum from zero to their total: $1,\ldots,h-1$ give an interval of sums, and the next index $3h$ is at most one plus its upper endpoint for large $n$. Each subsequent index extends the interval without a gap. We can therefore assign the remaining indices so the red sizes sum to exactly the red edge count and likewise for blue. Apply ABCT with $D=1$ separately in the two hosts; all guest degrees are at most two. The packings cannot overlap between colours, and their link shapes ascend independently of their placements.

For the random colouring, take $p_0=\min(p,1-p)/2$. The red common-neighbour count of any fixed set of $\ell\le11$ vertices is binomial with parameters $n-\ell,p^\ell$; the blue analogue uses $(1-p)^\ell$. Chernoff bounds and a union bound over $O(n^{11})$ sets give simultaneous concentration with failure probability $\exp(-\Omega_p(n))$. Apply this with a sufficiently small fixed relative tolerance, also requiring the two empirical edge densities to be within that tolerance of $p,1-p$. This gives the required relative error $\xi$ with the *actual* densities.

**One sparse prescribed link.** Let $D\ge1$ be fixed and let $F$ be $D$-degenerate with $1\le t=e(F)\le n-1$. Construct nested shapes with $F$ at size $t$, and apply ABCT in the *uncoloured* complete host. Fix $\mu=1/(300D)$ and $h=\lfloor\mu n\rfloor$.

If $t\ge n/8$, the edge support of $F$ has at least $t/D$ vertices by a degeneracy ordering. It contains a star forest of at least $t/(4D)$ edges: pick one neighbour for every nonisolated vertex, and put each vertex independently on one of two sides with equal probabilities. In expectation at least a quarter of the chosen arcs go from the first side to the second. Those arcs form a star forest since every tail has only one selected edge. Order the edges of such a star forest first, then the remaining edges of $F$. At sizes $h$ through $2h-1$ the prefix is a star forest with at least $h$ leaves and at most $4h$ vertices. Choose any Hamilton path $P$.

If $t<n/8$, order all of $F$ first, then $2h$ independent edges on unused vertices. Choose a Hamilton path $P$ containing these independent edges. The $h$ prefixes at sizes $t+h,\ldots,t+2h-1$ have at most $2t+4h\le n-h$ vertices and at least $h$ leaves. In both cases append unused edges of $P$ until the ordering has $n-1$ edges; there are enough since $P$ has $n-1$ edges.

Every prefix is a subgraph of $F\cup P$, hence is $(D+2)$-degenerate with maximum degree at most $\Delta(F)+2$. The complete host has density one and common-neighbour counts $n-\ell$, so it satisfies the fixed quasirandomness requirement for large $n$. Choose the constant in $\Delta(F)\le c_Dn/\log n$ small enough for ABCT with degeneracy $D+2$. The packing of the prefixes uses all edges. Relabel the entire result to put its copy of $F$ on the prescribed edges; if these are the red edges, all other links are blue.

**Bounded maximum degree, with more than $n-1$ edges.** Suppose $\Delta(F)\le d$ for fixed $d$ and $t\ge n$. A greedy edge colouring partitions $F$ into $b=2d-1$ matchings, allowing empty ones initially. Equalize their sizes: if two differ by at least two, an alternating path in their union has one extra edge of the larger class. Swapping along this path reduces the sum of squared sizes. At termination the sizes $s_1\ge\cdots\ge s_b$ differ by at most one. For large $n$, $s_b\ge\lfloor n/b\rfloor>2b$. Split matching $j$ into sizes $j$ and $s_j-j$. All $2b$ sizes are distinct: the latter sizes strictly decrease and exceed $b$. None exceeds $\lfloor n/2\rfloor$.

Use these actual red matchings at their indices in the matching-first path profile. The blue host has density $1-O_d(1/n)$ and any $\ell\le11$ vertices have at least $n-\ell(d+1)$ common neighbours there. It is sufficiently quasirandom for ABCT with $D=1$. After removing just $2b$ indices, there are still at least $\lfloor n/100\rfloor$ blue matching guests with indices between $n/8$ and $n/4$, providing the special graphs. Pack the blue guests by ABCT. Together with the preceding argument this handles every colour class of fixed bounded maximum degree for sufficiently large $n$.

The argument does not cover arbitrary structured dense colourings. For instance, the red union of two nonempty cliques with orders differing by at least two and its blue complete bipartite complement have no Hamilton path in either colour. A Hamilton path consisting of two monochromatic segments would not supply the required monochromatic terminal link of our path profile.

## Prescribing a linear forest at every order

**Theorem.** Let $n\ge3$ and let $F$ be a nonempty set of edges of $K_n$. There is an ascending decomposition $G_1,\ldots,G_{n-1}$ of $K_n$, with $i$ edges in $G_i$, in which **$F$ is one whole link and the last link is a Hamilton path**, if and only if $F$ is a linear forest (a disjoint union of paths, ignoring isolated vertices).

**Ramsey consequence.** If $F$ is the red edge set and is a linear forest with $t>0$ edges, take $E(G_t)=F$. Every other link is blue. Thus [Chatterjee–Zhang, Conjecture 2.6](https://doi.org/10.61091/jcmcc129-01) holds for every order when either colour class is a linear forest, with no restriction on its component lengths or on vertices it misses. The empty colour class is immediate from the uncoloured decomposition.

In an ascending decomposition the links partition the edges, and each embeds into the next **up to isomorphism**, not by inclusion on the given labels. Necessity in the theorem follows by composing embeddings: every link must embed in the final path. We prove sufficiency.

### Pair the small and large links

Write $n=2m$ or $2m+1$. Use the Walecki decomposition into $m$ copies of a template $H$: a Hamilton path in the even case and a Hamilton cycle in the odd case. To see the decomposition explicitly, on the residues modulo $2m$ take the paths

$$
x,\ x-1,\ x+1,\ x-2,\ x+2,\ \ldots,\ x-(m-1),\ x+(m-1),\ x-m
$$

for $0\le x<m$. The consecutive pairs are exactly the non-loop pairs with sum $2x-1$ or $2x$ modulo $2m$: the path uses $m$ of the former and $m-1$ of the latter, all distinct. These sum classes partition the edges. For odd $n$, close every path through the extra vertex; the path endpoints exhaust the residues exactly once.

The number $L$ of edges of $H$ is odd; put $k=(L-1)/2$. In a single template choose nested edge sets $S_0\subset S_1\subset\cdots\subset S_k$ with $|S_i|=i$. Index the $m$ copies of $H$ by $i=0,\ldots,k$ for paths and $i=1,\ldots,k$ for cycles. In copy $i$, take the images of $S_i$ and its edge complement as links of sizes $i$ and $L-i$, dropping the empty link. This partitions all edges, using each size from $1$ to $n-1$ exactly once. The small links ascend by nesting; the large ones ascend by **reverse** nesting of their complements. The last is a full path, or a cycle minus one edge.

There is only one embedding left to arrange: $A=S_k$ must embed in $B=E(H)\setminus A$. It is enough that the two parts agree up to isomorphism after deleting one edge from $B$ and ignoring isolated vertices. To prescribe $F$ it suffices to arrange, on this same template, one of the following:
- If $t=|F|\le k$, place a copy of $F$ inside $A$. Order the edges of $A$ with that copy first; its prefixes give the $S_i$ with $S_t$ the desired copy.
- If $t>k$, place a copy of $F$ **containing** $B$. Order the edges of $A$ with all $L-t$ edges outside that copy first. Then the complement of $S_{L-t}$ is the desired copy.

In either case the copy produced as link $t$ can be moved to the prescribed labelled edges by a permutation of $V(K_n)$ applied to the entire decomposition. It remains to construct the middle split. In the words below, $A,B$ mark the two parts of this split, **not** the red and blue colours.

### Construct the middle split

Let $\ell_1,\ldots,\ell_c$ be the positive path lengths of $F$. Thus $\sum_j\ell_j=t$ and $t+c\le n$.

**Small link, $t\le k$.** Choose $a_j\ge\ell_j$ with $\sum_j a_j=k$. Along $H$, alternate a run of $B$ edges and a run of $A$ edges for each $j$. Give both runs length $a_j$, except that the first $B$ run gets one additional edge. The $A$ runs contain disjoint paths of the required lengths. Trimming an end edge of the longer $B$ run leaves exactly the $A$ path lengths.

**Large link, $t>k$.** Lay out the prescribed forest in blocks $(\ell_j,g_j)$: $\ell_j$ consecutive forest edges followed by a gap of $g_j$ edges. The gaps must sum to $q=L-t<t$. For a cycle $q\ge c$; for a path $q\ge c-1$.

If $q\ge c$, start all gaps at one and spend the remaining $q-c$ units by filling one gap at a time up to $\ell_j$. There is capacity since $q<t$. If $q=c-1$, we are on a path: use gaps of one except for a single zero gap, whose block will go last. These rules give $g_j\le\ell_j$. Apart from at most one exception, every block has $g_j=1$ or $g_j=\ell_j$.

Call a block odd if $\ell_j+g_j$ is odd. There are an odd number of odd blocks because $L$ is odd. All but at most one of them have the form $(2p,1)$ with $p\ge1$. Set aside **one** odd block, choosing the exception if present. Pair the remaining odd blocks arbitrarily. Every even block and the set-aside block will be used singly. Place the groups in any order, keeping the zero-gap block last if present (it is single).

- On a **single block** of total length $h$, use $\lceil h/2\rceil$ edges marked $B$, then $\lfloor h/2\rfloor$ edges marked $A$. All $B$ edges belong to the forest since $\lceil h/2\rceil\le\ell_j$. The two runs have equal lengths except on the set-aside block, where the $B$ run is one longer.
- On a **pair** $(2p,1),(2s,1)$ use the word $(BA)^p\,AB\,(BA)^s$. Both gap positions (position $2p+1$ and the last position) are marked $A$. Each letter has exactly one run of length two and all its other runs have length one. The two parts therefore have identical path lengths on this group.

Groups start with $B$ and end with $A$; the sole possible empty $A$ run is on a final $(1,0)$ block of a path. Runs do not merge between groups, including at the join of a cycle. The gap rule also keeps the prescribed forest paths separate. Thus $B$ lies wholly in the forest. Deleting one end edge of its run on the set-aside block gives precisely the multiset of path lengths of $A$. In particular $|A|=k$, $|B|=k+1$, and $A$ embeds in $B$, as required. This proves the theorem.

## Scope and verification

The unrestricted problem allows the last link to have any shape. The [2023 paper, §4](https://doi.org/10.3390/sym15020523) and [2026 restatement, pp. 5–6](https://doi.org/10.61091/jcmcc129-01) report the unrestricted equality through $n=6$. The result on [Ramsey chains in linear forests](https://doi.org/10.3390/axioms12111019) instead concerns an arbitrary colouring of a **host** linear forest. Here the host is complete and the prescribed linear forest is an entire colour class.

The path-ending condition cannot simply be kept for arbitrary forests: a red spanning star on $n\ge4$ has no red Hamilton path, and its centre is isolated in blue. This does **not** refute the conjecture: when the red edges form any star, order its leaves first, then its centre, then the other vertices; the stars from each vertex to its predecessors give a full monochromatic-link decomposition.

**Replay.** Run `python3 -I verify.py` in this directory. The unrestricted census compiles the self-contained C++20 verifier into a temporary directory, checks every witness, rejects a damaged vertex map, and compares counts with the independent Burnside computation. No graph database, SAT solver or stored witness table is required. Use `python3 -I verify.py --through 8` for a shorter run. Separately the Python constructor checks all 4,504 linear-forest types through order 22 and rejects a colour-breaking edge swap; `python3 -I verify.py 9 2 2 2` prints an example. The finite tests do not stand in for the all-order proofs.

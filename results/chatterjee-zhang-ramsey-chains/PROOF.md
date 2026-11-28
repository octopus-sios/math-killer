# A prescribed linear forest in a full Ramsey chain

**Theorem.** Let $n\ge3$ and let $F$ be a nonempty set of edges of $K_n$. There is an ascending decomposition $G_1,\ldots,G_{n-1}$ of $K_n$, with $i$ edges in $G_i$, in which **$F$ is one whole link and the last link is a Hamilton path**, if and only if $F$ is a linear forest (a disjoint union of paths, ignoring isolated vertices).

**Ramsey consequence.** If $F$ is the red edge set and is a linear forest with $t>0$ edges, take $E(G_t)=F$. Every other link is blue. Thus [Chatterjee–Zhang, Conjecture 2.6](https://doi.org/10.61091/jcmcc129-01) holds for every order when either colour class is a linear forest, with no restriction on its component lengths or on vertices it misses. The empty colour class is immediate from the uncoloured decomposition.

In an ascending decomposition the links partition the edges, and each embeds into the next **up to isomorphism**, not by inclusion on the given labels. Necessity in the theorem follows by composing embeddings: every link must embed in the final path. We prove sufficiency.

## 1. Pair the small and large links

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

## 2. Construct the middle split

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

Run `python3 -I verify.py` in this directory. It constructs labelled edge partitions for every linear-forest isomorphism type through order 22 and independently checks each successive embedding by deleting one edge and comparing path lengths. It also tests rejection of a corrupted partition. For example, `python3 -I verify.py 9 2 2 2` prints the chain with three prescribed disjoint two-edge paths as its sixth link. The finite tests check the implementation; the argument above proves the assertion for all orders.

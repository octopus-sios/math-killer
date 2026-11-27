# Two obstructions to a 5-edge-connected quintic class-2 graph

**Carving theorem.** Every 5-edge-connected 5-regular loopless multigraph of carving width at most seven is 5-edge-colorable. In particular a witness to Problem 1.6 must have carving width at least eight, with parallel edges counted separately.

**Cover theorem.** Let $P$ be the Petersen graph, let $M,N$ be two of its perfect matchings (possibly equal), and let $B=P+M+N$, with a separate edge for each added copy. For $p\in\{2,3,5,7\}$ and every $d\ge 0$, every **5-edge-connected** voltage lift of $B$ with group $\mathbb F_p^d$ has a decomposition into five perfect matchings.

The connectivity threshold cannot be decreased to four, even for a connected double cover with no triple edges. We give explicit examples at the four-cut boundary below.

This is a partial answer to [Ma, Mattiolo, Steffen and Wolf, Problem 1.6](https://arxiv.org/abs/2206.10975), not a nonexistence theorem for general quintic graphs. The two base types are not arbitrary test graphs: by [Ma et al., Theorem 3.3](https://doi.org/10.1007/s00493-025-00144-4), all smallest class-2 5-graphs are of this form. The base graphs already have the required coloring obstruction; the question is whether separating their parallel edges across sheets can repair their connectivity while retaining the obstruction.

## A width-seven obstruction for arbitrary bases

A carving tree has the vertices of the graph at its leaves and all internal nodes of degree three. Each tree edge defines a shore (the leaves on one side); its width is the number of graph edges crossing that shore. The carving width is the minimum, over such trees, of the largest width. We actually only need a tree in which **each** cut size belongs to $\{5,6,7\}$. This condition follows from the hypotheses of the carving theorem. For example, small width does not force planarity: take $K_{3,3}$ with the edges of a six-cycle doubled, and group the ends of three disjoint doubled edges into cherries around a central node. Its tree cuts have sizes five and six.

On the boundary of a shore retain half-edges with distinguishable ports. A partial coloring uses every color once at every vertex of the shore. Each color then occurs on the boundary with the parity of the shore size, which is also the parity of its boundary size since all degrees are five. Record only an equality pattern of port colors, independent of color names. For instance, `012012` means that the first and fourth ports agree, the second and fifth agree, and the third and sixth agree, with three distinct colors. There are respectively 1, 31 and 35 parity-allowed patterns on 5, 6 and 7 ports. On five ports all colors differ; on seven, one color occurs three times and the other four occur once each.

The finite certificate in `carving()` in [the verifier](verify.py) consists of **seven templates**, each a short list of allowed words. The induction invariant is that the feasible patterns of each shore **contain**, in some ordering of the ports, all the words of one template. The templates for 5, 6, 7 ports have respectively the following numbers of words:

| Ports | Template sizes |
|---:|---|
| 5 | 1 |
| 6 | 6, 8 |
| 7 | 9, 12, 13, 12 |

Here is the full rule by which the lists certify the invariant. Start with a single leaf and its all-distinct word. For two child boundaries of sizes $i,j$ giving a parent of size $k$, exactly $m=(i+j-k)/2$ edges join the two children. Choose any $m$ ports on each side and any bijection joining them. In suitable port orders a proposed parent word $w=xy$, with $|x|=i-m$ and $|y|=j-m$, is realizable whenever some $m$-tuple of colors $z$ makes $xz$ and $zy$ instances of words of the respective child templates. Indeed, global color permutations in **each** child realize the actual names in these tuples and the two colors on every glued edge agree. For every such pair of templates and every joining, the parent words certified by this rule contain some permuted template of size $k$.

This last finite assertion is checked by enumerating $z$ in $\{0,1,2,3,4\}^m$. One may fix the order of the glued ports on the left, try all orders on the right, and keep the inherited order on unglued ports, since the output template may be arbitrarily permuted. There are 20,979 oriented template joins after eliminating duplicate input masks. Finally, for each $k$ and each pair of templates of that size, **every** bijection across the final cut gives a common word; the minima of the intersection sizes for $k=5,6,7$ are 1, 2, 1. Thus rooting at any tree edge, building both shores by induction and joining them gives a full 5-coloring. No enumeration of graphs or bound on the number of leaves enters this argument.

## Lifts and a coloring test

Orient the base edges. In an $A$-voltage lift an edge $e=uv$ with label $s_e\in A$ gives the edges $(u,j)(v,j+s_e)$ for $j\in A$. Parallel copies may have completely different labels. Switching, or changing the origin separately in each fiber, adds a vertex-potential difference to each edge label. It does not change the lift. A label assignment is **flat** on a connected subgraph if it can be switched to zero there, equivalently if all its signed cycle sums there vanish.

Call all parallel copies of an edge of $P$ a bundle. A bundle **splits** if its labels are not all equal. A **cubic choice** keeps one copy from each bundle. Its lift is cubic, and the other two layers are lifts of perfect matchings: simply assign the remaining copies over each base edge to $M,N$ in their prescribed multiplicities. Thus a 3-edge-colorable cubic choice suffices. In particular no assumption about the lengths of cycles in an arbitrary discarded 2-factor is needed.

For a nonzero linear form $\ell:A=\mathbb F_p^d\to\mathbb F_p$, the scalar labels $\ell(s_e)$ define a $p$-sheeted quotient. Any proper edge-coloring of this quotient pulls back: the map $(v,j)\mapsto(v,\ell(j))$ is bijective on the incident edge copies at each vertex. We will choose the quotient rather than assume it inherits the connectivity of the original graph.

For labels on the simple $P$, write $[s]$ for their class modulo vertex-potential differences. With scalar labels this space is $\mathbb F_p^6$: switch a spanning tree to zero and read the six chord labels. Let $D_e$ be the class of a unit change on the oriented edge $e$. Let $H_p$ be the set of classes for which the scalar cubic lift is not 3-edge-colorable.

## Finite scalar lemma

The following are exact, finite statements. Their verification is detailed below.

1. For $p=2,3,7$, if $e,f$ are vertex-disjoint edges of $P$ and $a,b\ne0$, the four points $x,x+aD_e,x+bD_f,x+aD_e+bD_f$ do not all lie in $H_p$. Also, if $x,x+aD_e\in H_p$ with $a\ne0$, the restriction of $x$ to $P$ minus the two ends of $e$ is flat.
2. For $p=5$ and $M=N$, if all five triples split, at least one cubic choice is 3-edge-colorable.
3. For $p=5$ and $M\ne N$, let $t=uv$ be their common edge. Suppose its triple splits and either a double splits or the core $P-\{u,v\}$ has nonflat labels when all doubles are unsplit. Then the scalar quintic lift is 5-edge-colorable **or** the entire assignment on the 25 edge copies of $B$ can be switched to have at most two nonzero copies.

The third assertion uses full quintic colorings; the cubic test alone is not enough at this prime.

## Proof in arbitrary rank

Every two distinct perfect matchings of $P$ meet in one edge, and every edge is in exactly two of the six matchings. For $M=N$ there are five vertex-disjoint triple bundles. For $M\ne N$ there is one triple $t=uv$ and eight doubles, all disjoint from $t$. These elementary facts also follow by listing the matchings in the verifier.

In a 5-edge-connected lift **every triple splits**: otherwise two lifted vertices joined by three parallel edges have a four-edge boundary. In the distinct case with no split doubles the core must be nonflat. Otherwise switching the core to zero exhibits an eight-vertex copy with just four exiting edges, the two non-$t$ edges at each of $u,v$. Rank zero is thus already excluded.

We use two elementary facts:

- A form can be chosen nonzero on any specified list of at most $p$ nonzero vectors. Each forbidden kernel condition is a hyperplane in the dual. Fewer than $p$ such hyperplanes cannot cover it by counting; even $p$ cannot, since they all contain zero.
- If a voltage assignment on $B$ can be switched to have at most two nonzero edge copies, one whole sheet has boundary at most four: each nonzero copy contributes two to that boundary. Thus this is impossible in the given lift.

For $p=2,3,7$ with at least two disjoint split bundles, choose a form seeing one nonzero difference on each. The four choices in part 1 of the scalar lemma give a colorable cubic choice in the quotient. This covers the repeated case and the distinct case with any split double. In the remaining distinct case choose a form seeing both a triple difference and a nonzero cycle sum in the core. Part 1 says that two choices differing on the triple cannot both be bad. Pull back the resulting coloring.

For $p=5$, in the repeated case choose one difference from each triple and a single form seeing all five. Apply part 2. For the distinct case we choose a form satisfying the hypotheses of part 3 **and avoiding its small-support alternative**. The details matter: a small cut can appear in a quotient even if the original lift has none.

- **At least two split doubles.** See a difference on each of two doubles and on the triple. Three split bundles require at least three nonzero copies under every switch.
- **Exactly one split double $f$.** If the triple has three distinct labels, see its three pairwise differences and a difference on $f$. At least two triple copies and one double copy are then nonzero under every switch. If the triple has a majority label, fix it in the cubic choice. Using either of the two labels on $f$ gives two cubic assignments. Neither is flat on $P$: otherwise switching it to zero would leave at most one nonzero copy at each of $t,f$ in the full lift. Take one nonzero cycle sum from each assignment and see both, as well as the two bundle differences. If the quotient could be switched to support at most two, exactly one copy at each of $t,f$ could be nonzero, so one of those two cubic assignments would have become flat. This contradicts the choice of form.
- **No split doubles.** Fix a nonzero cycle sum $c$ in the core. If the three triple labels are distinct, see $c$ and their three differences. At least two copies on $t$ and one in the core remain nonzero. It remains to treat a triple with majority label. Let $h$ be the nonzero triple difference. Use the majority label and denote the resulting six vector-valued chord coordinates by $X$. The map $\ell\mapsto\ell(X)$ has image a scalar subspace $U\subseteq\mathbb F_5^6$. It is not zero, by $c\ne0$.

In this last case it suffices to see $c,h$ and make $\ell(X)$ nonzero and outside the lines spanned by $D_e$ for **single** edges $e$ of $B$. Indeed, if the switched quotient had support at most two, at least one copy on $t$ and one in the nonflat core would be nonzero. Hence exactly one copy on $t$ would be nonzero (the minority copy), and the other nonzero edge would be single: an unsplit double contributes two copies. The resulting majority section would have class on a forbidden line.

If $\dim U=1$, its line is not forbidden. Otherwise all linear forms would send $X$ into a fixed line spanned by a single-edge column $D_e$. In coordinates this means $X=D_e w$ for some $w\in A$ (take a nonzero coordinate of $D_e$ to recover $w$). Switching makes the majority section zero off $e$, leaving at most the single copy at $e$ and the minority copy at $t$ nonzero, impossible. Any form seeing $c,h$ now works.

If $\dim U\ge2$, first choose $\ell_1$ seeing $c,h$, so $\ell_1(X)\ne0$. Choose $\ell_2$ giving an independent image. In their two-dimensional span there are six projective choices of form. At most two fail to see $c$ or $h$. At most three image directions lie on edge-column lines: **no plane contains more than three such lines.** Indeed, there are no one- or two-edge cuts in $P$, and its only three-edge cuts are vertex stars. A dependence of three distinct edge columns would give a nonzero vertex-potential difference supported on those three edges, so their deletion disconnects $P$ and the three form a star. Similarly no column is zero and no two are proportional. Four edge lines in a plane would make each triple a star, impossible for two distinct stars sharing two edges of a simple graph. Thus at least one projective choice works. This proves the theorem.

## How to reproduce the scalar lemma

Run `python3 verify.py` in this directory. The verifier uses integer arithmetic and the Python standard library only. It labels the edges $0,\ldots,14$ in order: the outer edges $i\to i+1$, inner edges $5+i\to5+((i+2)\bmod 5)$, then spokes $i\to5+i$, for $0\le i<5$ (outer indices modulo five). The non-tree edges are $4,9,11,12,13,14$.

| $p$ | Chord signatures | Noncolorable cubic signatures | Of these, supported on a star up to switching |
|---|---:|---:|---:|
| 2 | 64 | 16 | 16 |
| 3 | 729 | 51 | 51 |
| 5 | 15,625 | 901 | 181 |
| 7 | 117,649 | 391 | 391 |

For a star-supported assignment each sheet contains a copy of $P-v$ with three exiting edges. In a cubic 3-coloring each color crosses that odd shore an odd number of times. All three colors would cross once, extending to a coloring of $P$, impossible. For the other signatures the verifier searches the three colors on individual edge copies, fixing their names at one vertex. Each branch tries every remaining color allowed by the endpoints. A found coloring is checked directly. Orbits are formed only by adjacency-preserving vertex permutations of $P$ (including orientation reversal on moved edges) and nonzero changes of scalar unit. Every chord signature is accounted for. Part 1 then tests the indicated translations of the bad set and checks flatness by integrating along core paths.

At five, use the all-spoke matching for $M$ and spoke $t=10$. If $M\ne N$, the other matching through $t$ is forced. The verifier checks the matching-pair orbits and, in the repeated case, transitivity on the marked edge of $M$. Normalize one nonzero difference on $t$ to one. Choose one label per bundle as the reference section and switch its tree labels to zero. Only reference signatures in $H_5$ need further tests. The possible offsets on $t$ are now $(0,1,b)$ for $0\le b<5$. On each other multiple edge enumerate every possible multiset of offsets containing zero. If *any* of the resulting cubic choices leaves $H_5$, the remaining bundles need not be assigned: choosing their reference copies completes that good choice. This enumerates descriptions, not isomorphism classes.

When all five triples split, **zero** descriptions survive. In the distinct case **4,908** survive the cubic test and the split/core hypothesis. For small support the verifier generates all placements of two potentially nonzero voltages on the 25 edge copies. For the other descriptions `data/five-colors.txt` gives 131 representatives with directly checkable colorings. On a bundle of size $m\le3$ the mean label exists modulo five. The key consists of the six normalized chord means followed, in base-edge order for nonsingle bundles, by the sorted deviations from each bundle mean. This is a complete encoding up to switches and permutation of parallel copies: switch the means on the tree to zero, then add back the deviations. The second field is one color per lifted edge in base-edge, deviation, sheet order. After checking each color word, the verifier explicitly registers its images under base automorphisms preserving bundle sizes and nonzero scalar multiplication. No graph database or SAT solver is trusted. The checker accepts a proper coloring of the bipartite double cover of $P$ and rejects a one-edge color corruption.

## Sharpness at edge connectivity four

Here is a cyclic cover of every degree $n\ge2$ with maximum multiplicity two, edge connectivity four and no 5-coloring. Use distinct $M,N$ as above. Give voltage $1\in\mathbb Z/n$ to one of the three copies of $t$ and to the inner rim edge $5\to7$ at its inner endpoint. Give all other copies voltage zero.

First, $B$ itself is class 2. If its five color classes projected $x_i$ times to the $i$th perfect matching of $P$, and $m_i$ counts its multiplicity in $M,N$, then $(x_i-m_i)+(x_j-m_j)=1$ for every pair $i\ne j$, by counting their unique common edge. Six integers cannot satisfy these equations. In any 5-coloring of the core with its four dangling edges, each color occurs an even number of times on the four ends, since the core has eight vertices. If the two ends on the outer-vertex side had distinct colors, the other two would have the same distinct pair. Assigning the three remaining colors to the triple would color $B$. Thus the two outer-side ends must agree. The lift contains intact copies of the core in which both these ends meet the same outer vertex, ruling out a coloring.

Finally $B$ has minimum cut four: $P$ has no nontrivial cut of size at most three, singleton degrees in $B$ are five, and the triple's ends have boundary four. In the lift each sheet internally contains $B$ minus two edge copies, so splitting a sheet costs at least two internal edges. A cut splitting at least two sheets costs at least four. If it splits no sheet, at least two interfaces in the cyclic sequence of sheets change side and each contributes two edges (for $n=2$ count both directed interfaces). If exactly one sheet splits and both sides occur among the unsplit sheets, at least one of their interfaces changes side, contributing two more edges. Otherwise take the side contained in the split sheet: each deleted base edge crossing it has its crossing replaced, so the cut is at least the corresponding base cut. One whole sheet has boundary exactly four. This proves sharpness.

Outside the carving-width criterion, the cover theorem does not cover arbitrary permutation lifts, all primes, or bases other than $P+M+N$. Problem 1.6 remains unresolved by these arguments.

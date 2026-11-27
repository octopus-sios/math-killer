# Sharp odd colorings of 4-trees and 5-trees

**Theorem.** Every finite 4-tree is odd 6-colorable, and every finite 5-tree is odd 7-colorable. Both bounds are sharp.

These are the $k=4,5$ cases of the conjecture of [Kashima and Ozeki, *Odd coloring of k-trees*](https://arxiv.org/abs/2504.20573). The authors proved the sharp bounds for $k=2,3$ and gave the lower-bound construction for general $k$. The results here impose **no bound on the number of vertices**. They do not settle the conjecture for $k\ge 6$.

The proof works from simplicial vertices towards a root clique. A piece can be deleted if its colorings can repair every possible exterior parity assignment on its boundary. The computation certifies that the pieces that can survive in a smallest counterexample belong to a small, explicit table. None of the terminal pieces is a counterexample.

## Rooted forests

Fix $k\in\{4,5\}$. Start with a $k$-clique $Q$ with slots $0,\ldots,k-1$. A **forest at $Q$** is an unordered collection of branches, possibly empty. A branch introduces one center $u$ adjacent to $Q$ and places a forest on each of $k$ new faces. Face $i$ replaces the vertex in slot $i$ by $u$, retaining the other slots. All introduced vertices are fresh; the only edges added at an introduction go from the new vertex to its attachment face.

These expressions give exactly the $k$-trees, together with the bare $K_k$. One vertex on $Q$ makes the initial $K_{k+1}$. In any subsequent addition each newly created $k$-clique contains the new vertex and $k-1$ of its earlier neighbors; it is one of the $k$ new faces. Assign each later attachment to its face of creation, or to $Q$. This gives the expression. In reverse, reading the expression with ancestors before descendants gives an addition order.

Any selection of whole sibling branches, including their descendants, can be deleted while leaving a valid expression. So can child forests on two different faces of one branch, **retaining their common center**. No interior vertex of a deleted forest has neighbors in the remaining graph except in its attachment face. Interiors of the two child forests are disjoint with no edges between them.

## Testing whether a piece is reducible

Use colors $0,\ldots,k+1$. The **mask** of a multiset of colors records their multiplicities modulo two. Masks of disjoint multisets combine by coordinatewise XOR; a nonzero neighborhood mask is precisely the odd condition.

Precolor a core clique of order $m$, normalizing its colors to $0,\ldots,m-1$. We use either $m=k$ for a forest at one face, or $m=k+1$ for forests on distinct faces of a bag. Any injective precoloring is equivalent by a palette permutation. Enumerate the proper extensions for which all interior vertices have nonzero neighborhood masks. Each such extension gives a **signature** $s$: its entry $s_i$ is the mask contributed by interior neighbors to core vertex $i$. It excludes edges within the core. Let $S$ be the set of signatures.

Suppose the remaining graph, including the core, has been odd-colored, and write $b_i$ for the current nonzero mask of core vertex $i$. The whole graph can be odd-colored by extending this coloring if and only if some signature satisfies $s_i\ne b_i$ for all $i$: precisely then $s_i\mathbin{\mathrm{XOR}} b_i$ is nonzero. Other exterior vertices keep all their neighbors. Call a piece **reducible** if such avoidance is possible for *every* tuple of nonzero forbidden masks $b_i$. This is sufficient for deletion, even though not all tuples need occur in an actual exterior.

**Slice-cover test.** Failure of reducibility means that $S$ can be covered by selecting at most one slice $s_i=b_i$ per coordinate, where $b_i\ne 0$. Pick a still-uncovered signature $s$. For each unused coordinate $i$ with $s_i\ne 0$, try the slice $b_i=s_i$, discarding every signature hit by it and removing coordinate $i$. An empty remaining family is covered, and a nonempty family with no available choice is not. This recursion is exact: any cover must hit the chosen signature, and any recursive cover extends by the chosen slice. Unused coordinates can be filled with arbitrary nonzero masks. The depth is at most $m$.

## The finite certificate

The accompanying [verifier](verify.py) specifies finite tables $T_k$ by giving their slot-permutation representatives and expanding them under all permutations of the $k$ slots. A representative is just a sequence of attachment-face numbers: initially only face 0 exists; each step attaches a vertex to the indicated face and appends the $k$ new faces in slot order. All permutations act consistently down the expression, and siblings are unordered. No completeness assumption is made about this list: only the following closure tests are used.

1. **Terminal.** For each forest in $T_k$, enumerate its signatures at the root face. Some signature must avoid the tuple for the bare $K_k$: the forbidden mask at $i$ has exactly the bits $\{0,\ldots,k-1\}\setminus\{i\}$.
2. **Siblings.** For each table forest and each *single-branch* table forest, form their multiset union. It must be in the table or have a nonempty reducible subcollection of whole siblings.
3. **Two faces.** Fix a bag of order $k+1$, precolored identically, with center in slot $k$. For two nonempty table forests on faces omitting slots 0 and 1, combine their signatures by coordinatewise XOR and test reducibility on the **entire bag**. This gives exactly the joint signatures, since the interiors can be colored independently on the fixed bag. Mark every successful pair for pruning. Relabeling the root slots transfers this test to any ordered pair of distinct faces.
4. **One center.** Enumerate every ordered $k$-tuple of table child forests that contains no pruned pair. The single branch with these children must itself be in $T_k$ or be reducible at its root $k$-clique.

For the last test, fix the center color to $k$ and combine one signature per child by XOR. Discard a combination if its center entry equals the mask of the $k$ root colors: precisely then the center fails the odd condition. For each other entry toggle bit $k$, since every root vertex sees the center. This gives the signatures for center color $k$; swapping colors $k$ and $k+1$ gives the signatures for the only other available center color. Thus the test checks properness and oddness at *all* interior vertices, including the center.

The enumeration uses only integer operations. A small chosen subfamily of signatures can certify success: if it has no slice cover, the full family cannot have one. An inconclusive sample **never** prunes a pair or certifies a branch; the full set of distinct coordinatewise XORs is tested in that case. Checks need only run once per slot-permutation orbit. For a fixed pair of faces, only permutations preserving the unordered pair of slots are used, interchanging the two forest labels when the slots are exchanged.

| Certificate statistic | Four-trees | Five-trees |
|---|---:|---:|
| Listed slot-permutation representatives | 10 | 35 |
| Terminal forests | 72 | 917 |
| Unlisted sibling unions tested, up to slot permutations | 144 | 4,914 |
| Two-face orbit representatives tested | 1,352 | 77,410 |
| Retained ordered pairs of nonempty labels on a fixed pair of faces | 148 | 3,983 |
| Residual ordered child tuples, including listed ones | 2,509 | 476,162 |
| Unlisted residual singleton orbits tested | 145 | 5,646 |

Reproduce both certificates with `python3 verify.py` (standard library only). As a negative control, deleting the last displayed representative at each width makes its one-center closure check fail. No SAT solver, precomputed coloring, numerical tolerance, or graph-order cutoff is used.

## From closure to all orders

Suppose a counterexample exists at the specified width, and take one of minimum order. The bare clique is odd-colorable. No nonempty reducible collection of whole siblings can occur anywhere in the expression: delete it, odd-color the smaller $k$-tree or bare clique, and extend at its core. Similarly, no pair marked in test 3 can occur: delete both child forests, keep the common center, and extend on the precolored bag.

Work from the leaves towards the root. When every child forest of a branch is in $T_k$, its child tuple has no pruned pair. Test 4 forces the branch into $T_k$, because the alternative is a reducible whole branch. Every forest of such siblings is also in $T_k$: start with the empty forest (which is listed), and insert the siblings one by one. If an insertion leaves $T_k$, test 2 gives a reducible subcollection of that prefix. These whole branches can also be deleted from the actual graph with all the other siblings present, a contradiction. Structural induction puts the entire expression in $T_k$. Test 1 now odd-colors it on the bare root clique. This contradicts the choice of a counterexample.

For sharpness use Kashima and Ozeki's construction. Take a $(k+1)$-clique with center $z$ and other vertices $v_1,\ldots,v_k$. For each $i$ add one vertex on the face omitting $v_i$. In any proper $(k+1)$-coloring this vertex must take the color of $v_i$, so $z$ sees each of the $k$ other colors exactly twice. The resulting $(2k+1)$-vertex $k$-tree is not odd $(k+1)$-colorable.

**Verification scope.** The Python certificates and the structural induction prove the two all-orders results. The accompanying Lean module proves the slice-cover recursion, cover/avoidance duality, and the parity criterion on a finite simple graph. It does not verify the tables or the two theorems end to end.

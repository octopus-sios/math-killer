# Every 4-tree has an odd six-coloring

**Theorem.** Every finite 4-tree has a proper coloring with six colors in which every vertex sees some color an odd number of times. Six is best possible.

This proves the $k=4$ case of the conjecture of [Kashima and Ozeki, *Odd coloring of $k$-trees*](https://arxiv.org/abs/2504.20573). They proved the sharp bounds for $k=2,3$ and gave the lower-bound construction for general $k$. The result here imposes **no bound on the number of vertices**; it does not settle the conjecture for $k\ge 5$.

## Forests on a four-clique

Start with a four-clique $Q$ with slots numbered $0,1,2,3$. A **forest at $Q$** is an unordered collection of branches, possibly empty. A branch introduces one center $u$ adjacent to $Q$ and places a forest on each of four new faces. Face $i$ is obtained by replacing the vertex in slot $i$ by $u$, without moving the other slots. All introduced vertices are fresh; the only edges added at an introduction are those from the new vertex to its attachment face.

These expressions give exactly the 4-trees, together with the bare $K_4$. Indeed one vertex on $K_4$ makes the initial $K_5$. In any subsequent addition each newly created four-clique is one of the four faces just described: it must contain the new vertex and three of its four earlier neighbors. Each such clique therefore has a unique creation step. Assign each later attachment to its face of creation (or to $Q$). This gives the expression, and reading the expression with ancestors before descendants gives a valid addition order in the reverse direction.

A selection of whole sibling branches can be deleted, including all their descendants, while leaving a valid expression. So can the child forests on two different faces of one branch, leaving their shared center in place. No interior vertex of a deleted forest has a neighbor outside it except in its attachment face. In particular, two such forests have disjoint interiors and no edges between their interiors.

## The extension test

Colors are $0,\ldots,5$. The **mask** of a multiset of colors is the six-bit vector recording their multiplicities modulo two. Combining disjoint multisets adds their masks by bitwise XOR; a nonzero mask is exactly the odd condition.

Fix a precolored core clique, either the four-clique $Q$ or a five-clique consisting of a face and a center. Normalize its colors to distinct consecutive integers; any other injective precoloring is obtained by a palette permutation. For a forest or union of forests attached to this core, enumerate its proper extensions for which every interior vertex has a nonzero neighborhood mask. Each gives a **signature** $s$: the entry $s_i$ is the mask contributed by interior neighbors to core vertex $i$. It excludes edges within the core. Let $S$ be the set of these signatures.

Suppose the exterior, including the core, is already odd-colored. Write $b_i$ for the nonzero mask at core vertex $i$ in that coloring. A signature extends it to an odd coloring if and only if $s_i\ne b_i$ at every core vertex: precisely then $s_i\mathbin{\mathrm{XOR}} b_i$ is nonzero. Other exterior vertices keep all their neighbors. Thus a piece is **reducible** if this simultaneous avoidance is possible for every tuple of nonzero forbidden masks. We also use the stronger test that allows zero forbidden masks. For forests on distinct faces of a precolored five-clique, the set of joint signatures consists exactly of the coordinatewise XORs of one signature from each forest, since their colorings are independent on the given core.

Here is the finite test used below. A failing tuple would cover $S$ by at most one slice $s_i=b_i$ in each coordinate $i$. Pick any still-uncovered signature $s$. Branch over the unused coordinates $i$ where $s_i$ is an allowed forbidden mask; set $b_i=s_i$, discard all signatures hit by this choice, and remove coordinate $i$. The empty remaining family is covered; a nonempty family with no available choice is not. This recursion is exact: any cover of the current family must hit the chosen signature in one of these ways, and any recursive cover extends by the chosen slice. Unused coordinates of a cover may be filled arbitrarily with an allowed mask. The depth is at most the size of the core.

## A closed table of small forests

In the following table specification $E$ is the empty forest, $B$ is the singleton forest with a leaf center (all four child forests empty), and $J(i:F,j:H,\ldots)$ is a singleton branch with the indicated child forests and all unmentioned faces empty. A plus sign joins siblings. Put $D=J(3:B)$ and $L=J(3:D)$. Use the following ten representatives and **all** their images under permutations of the four slots, applying the same permutation throughout an entire forest:

1. $E$;
2. $B$;
3. $D$;
4. $B+D$;
5. $L$;
6. $J(3:J(2:B))$;
7. $J(2:B,3:B)$;
8. $B+L$;
9. $J(2:B,3:J(1:J(0:B)))$;
10. $J(2:B,3:J(0:B,1:B))$.

Write $T$ for the resulting table. By interior order $0,1,2,3,4,5$ the numbers of distinct slot-labeled forests are $1,1,4,26,4,36$. There is no assumption that these are all the irreducible forests: only the following closure properties are needed.

| Check | Domain | Required outcome |
|---|---:|---|
| Terminal | 72 table forests | Some signature avoids the masks of the bare four-clique. |
| Siblings | 2,555 distinct unions of a table forest and a singleton table forest | The union is in $T$, or a nonempty subcollection of its sibling branches is reducible. |
| Two faces | 4,884 ordered pairs from $T$ on faces 0 and 1, both of order at least 2 and at least one of order at least 3 | Their joint signatures avoid **arbitrary** forbidden masks on the five-clique. |
| One center | 3,408 remaining ordered quadruples of table forests, those containing no pair meeting the size criterion | The singleton branch with those children is in $T$ or is reducible at its four-clique. |

These are exact finite checks, reproduced with the standard library by running `python3 verify.py` beside this file. The verifier expands the ten representatives, builds the actual adjacency lists for each test, enumerates the two available colors at each introduction, and computes masks from neighbor colors. It uses the slice-cover test above. In the two-face test, a subfamily that already cannot be covered certifies that the full family cannot be covered. Checking faces 0 and 1 suffices because every ordered pair of distinct faces can be moved to them by a slot permutation, and the entire table is closed under such permutations. In the terminal check the forbidden mask at vertex $i$ has precisely the bits $\{0,1,2,3\}\setminus\{i\}$. As a negative control, removing the last displayed representative causes its singleton-branch closure check to fail.

## Why the finite checks prove the theorem at every order

Suppose there were a counterexample, and take one of minimum order. The bare four-clique is odd-colorable. No nonempty reducible sibling subcollection can occur anywhere in its expression: delete it, color the smaller 4-tree or bare clique, and use the extension test to put it back. For the same reason the expression cannot contain a pair passing the two-face test; here delete the two child forests but **not** their common center, then extend on the precolored five-clique.

Work from the leaves towards the root. If each of the four child forests is in $T$, their ordered quadruple cannot contain a pair meeting the size criterion, by the two-face check and minimality. The one-center check now forces their singleton branch into $T$, since the alternative is a reducible subcollection. Every forest of such sibling branches is also in $T$: start with $E$ and insert its branches one at a time. If any insertion leaves $T$, the siblings check exhibits a reducible subcollection of that prefix. Those whole branches are also deletable from the actual graph with all the other siblings present, which is impossible. Structural induction therefore puts the entire forest on the initial $Q$ in $T$. The terminal check colors that forest together with $Q$, a contradiction.

For sharpness, specialize Kashima and Ozeki's construction: take a five-clique with center $z$ and four other vertices $v_1,\ldots,v_4$. For each $i$ add one vertex on the four-clique omitting $v_i$. In a proper five-coloring this new vertex must take the color of $v_i$. Consequently $z$ sees each of the four other colors exactly twice and does not satisfy the odd condition. This nine-vertex 4-tree requires six colors.

**Verification scope.** The Python certificate and the structural induction above establish the four-tree theorem. The companion Lean module proves the slice-cover recursion and the parity criterion for an interface of a finite simple graph. It does not verify the finite table or the four-tree theorem end to end.

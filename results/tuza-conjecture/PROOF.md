# Rotating triangle books: a $39/14$ bound for Tuza's problem

**Theorem.** For every finite simple graph $G$, the minimum number $\tau(G)$ of edges hitting all triangles satisfies
$$
14\tau(G)\le 39\nu(G),
$$
where $\nu(G)$ is the maximum number of pairwise edge-disjoint triangles. The coefficient $39/14$ improves on [Sichen Wang’s September 12, 2026 arXiv bound](https://arxiv.org/abs/2609.13831v1) of $165/59$ by $9/826$, and on the $81/29$ bound in [Tyler B. Hughes’s November 23, 2026 unrefereed draft](https://mathdiscoveries.org/results/tuza-triangle-cover) by $3/406$. This does not prove Tuza's conjectured coefficient $2$.

The starting packings, the book covering principle and the $8/3$ colored lemma are from [Sichen Wang, *A Bound Below 2.8 for Tuza's Conjecture*, arXiv:2609.13831v1](https://arxiv.org/abs/2609.13831v1). We give the needed proofs. Two additional moves are important. One can free an opposite edge held by another book before testing whether the first book's spine is private. Also, when an opposite is an unused red edge, its four vertices give a complete graph with a red matching. Rotating the two pages to a **blue** spine saves a blue edge, and a packing surviving those blue edges supplies additional pages. Counting **distinct** opposite edges makes the rotations simultaneous.

### 1. Books and one-red triangles

Triangles meet when they share an edge. A book of $j=1,2,3$ pages consists of $j$ triangles sharing a spine. Its support is the union of its edges. For pages $uvx,uvy$, call $xy$ the opposite if it is present.

**Book principle.** Suppose supports of books are pairwise edge-disjoint and every selection of one page per book is a maximal packing of a given triangle family. Let $C$ consist of the edges of the singletons (one-page books) and the spines of the multipage books. A family member avoiding $C$ must be $uxy$ or $vxy$ at a two-page book $uvx,uvy$. Hence adding the present opposites gives a transversal of size at most $\sum(4-j)$.

Indeed a triangle must meet every page of some one book, or choose one avoiding page in each book and augment the resulting packing. A triangle avoiding $C$ cannot meet a singleton or use a spine to hit a multipage book. To hit pages $uvz$ it must use $uz$ or $vz$ for every distinct tip $z$. Three tips and an endpoint of the spine need at least four vertices. For two tips the two chosen edges must share an endpoint, giving exactly the two stated possibilities.

Here and below, for a red/blue edge coloring of $H$, let $F(H)$ consist of **all** triangles with exactly one red edge. Write $B(K),R(K)$ for the unions of blue and red edges of a packing $K$ and $E(K)$ for its whole edge set. For any triangle family, $\nu,\tau$ denote edge-packing and edge-covering numbers in the sense above. An edge is private in a specified family when it occurs in exactly one member.

**Colored bound (Wang).** If $U$ is a maximum packing of $F=F(H)$, $p=|U|$, and $u$ of its red edges are private in $F$, then $3\tau(F)\le 8p-2u$.

*Proof.* Set $F_0=F(H-B(U))$ and take a maximum packing $V$ there, of size $q$. Each surviving triangle meets $U$ only in its red edge, which must be in $R(U)$ by maximality. Pair each member of $V$ with its unique red-edge partner in $U$; other members of $U$ are singletons. Supports are disjoint, and a selection is a maximum packing of size $p$. Write $r$ for the number of private red edges of $V$ in $F_0$.

If $uvx\in U$, $uvy\in V$ are paired and the opposite $xy$ is red outside $R(U)$, then $uv$ is private in $F_0$. Otherwise take $uvz\in F_0$ with $z\ne y$. Also $z\ne x$ since $uvx$ uses deleted blue edges. The two triangles $uxy$ and $uvz$ are edge-disjoint (their only common vertex is $u$); they meet $U$ only in $ux$ and $uv$ respectively. Both have one red edge. Substituting both for $uvx$ contradicts maximal cardinality.

The book principle gives a core of size $3p-2q$. An uncovered one-red triangle already uses two blue page spokes, so its opposite is red and not in the core (which contains $R(U)$). At most $r$ opposites need adding. The $u$ initially private red edges belong to singletons; delete them, since their unique triangles are hit by their blue edges. Thus $\tau(F)\le 3p-2q+r-u$. Alternatively use $B(U)\cup E(V)$; this hits every triangle, and the $r$ private red edges of $V$ can be removed because the only surviving triangles containing them retain their two blue edges. This gives $\tau(F)\le 2p+3q-r$. Twice the first bound plus the second gives $3\tau(F)\le8p-2u-q+r\le8p-2u$. $\square$

### 2. General packings

Take a maximum packing $P$ of all triangles, write $n=|P|$, and call its $3n$ edges **old**. Every triangle has an old edge. Let $A$ be a maximum packing of triangles with exactly one old edge; write $a=|A|$. Pair each member of $A$ with its old-edge partner in $P$. Two cannot meet the same member of $P$, or both would replace it, increasing $n$. Books have disjoint supports, and every selection has size $n$ and hence is maximal. The book principle gives
$$
\tau(G)\le 3n-a. \tag{1}
$$

Remove $E(A)$ and call the graph remaining $G'$. Each triangle now has either two or three old edges, by maximality of $A$. There are $3n-a$ surviving old edges. In $G'$ color old edges blue, others red. Choose a packing $P'$ of $G'$ maximizing first the number $b$ of one-red triangles, then its total size $m$. Write $U$ for its $b$ one-red members and $N=R(U)$ for their $b$ red edges. In particular $U$ is a maximum packing of $F(G')$. Also $a+m\le n$. Any packing of $G'$ with the same $(b,m)$ is maximal in all triangles of $G'$.

Let $S=F(G'-B(P'))$. Every triangle of $G'-B(P')$ belongs to $S$: an all-blue triangle there could be added to $P'$. Each triangle of $S$ uses a red edge of $N$, since it avoids the blue edges of $U$. Choose a maximum packing $Q$ of $S$, put $c=|Q|$, and let $h$ of its red edges be private in $S$. Form the $m$ books of $P',Q$ by pairing the pages on their common red edges. Each of the $c$ pairs is $uvx,uvy$ with $uv$ red, $uvx\in P'$, $uvy\in Q$. All other books are singletons, possibly all-blue. Supports are disjoint, and any selection has counts $(b,m)$. Write $L$ for the set of **distinct present opposites red outside $N$**, and $\ell=|L|$. All colors, presence of opposites and switches from now on refer to $G'$.

**Cut cover.** Let $W$ contain both blue edges of each of the $b-c$ one-red singletons. For the one-red family alone, discard the all-blue books; each selection among the remaining books has size $b$ and is maximum there. Their book core is $W\cup N$. Thus every one-red triangle avoiding $W$ has red edge in $N\cup L$: otherwise it avoids the core and its red edge must be the opposite by the book principle.

Independently assign a fair bit to each vertex. Take $W$ and every monochromatic blue edge. All-blue triangles are met. Any remaining triangle has two bichromatic blue edges, so its red edge is monochromatic and belongs to $N\cup L$. Add the monochromatic edges of $N\cup L$. Together with $E(A)$ this is always a cover, of expected size
$$
3a+|W|+\tfrac12(3n-a-|W|)+\tfrac12(b+\ell).
$$
Consequently
$$
\tau(G)\le \tfrac32 n+\tfrac52a+\tfrac32b-c+\tfrac12\ell. \tag{2}
$$

**Safe opposite switch.** For *all* $m$ books let $C$ again be the singleton edges and paired spines. If the opposite $xy$ of a pair $uvx,uvy$ exists outside $C$, then $uv$ is private in $S$.

To prove this, assume there is a second $uvz\in S$, so $z\notin\{x,y\}$. We first obtain an equal-objective packing in which $xy$ is unused, still containing $uvx$, and against which the edges $uy,uz,vz$ are unused. If $xy\notin E(P')$, take $P'$ itself. Otherwise, since $xy\notin C$, it is a blue spoke of a *different* paired book in its $P'$ page. Write that page as $pit$ and its $Q$ page as $pis$ with red spine $pi$, where $\{p,t\}=\{x,y\}$ and $pt=xy$. Neither $i$ nor $s$ is $u$ or $v$: if $i$ were, $it$ would coincide with a spoke of the first book, and if $s$ were, $ps$ would coincide with such a spoke. Thus the page $pis$ contains neither $u$ nor $v$. Replace $pit$ by $pis$. The switch removes $xy$, preserves disjointness and $(b,m)$, and introduces no edge incident with $u$ or $v$. This proves the assertion about unused edges in both cases.

Now $uxy$ and $uvz$ meet the adjusted packing only in $ux$ and $uv$ respectively. They are edge-disjoint; the second is one-red, and the first is one-red or all-blue. Substituting them for $uvx$ does not decrease $b$ and increases $m$, impossible. Thus only $h$ pairs can require an opposite outside $C$. Its size is $3m-2c$, so
$$
\tau(G)\le 3a+3m-2c+h\le 3n-2c+h. \tag{3}
$$

**Rotation and promotion.** For each edge of $L$ choose exactly one representative pair $uvx,uvy$. Here $uv,xy$ are both red, and all four spokes $ux,vx,uy,vy$ are blue. Enlarge its support temporarily to this entire $K_4$. The enlarged supports remain disjoint from each other and from all other books: the only additional edge is the representative's opposite, red outside $N$, and the chosen opposites are distinct.

At each representative replace its two pages by $uvx,uxy$, sharing the **blue** spine $ux$. These are both one-red, have different red edges $uv,xy$, and use three blue spokes instead of four (they omit $vy$). No other books change. Each selection from the resulting books still has $(b,m)$. Let $H$ be the union of their blue edges, so
$$
|H|=(3m-b)+2c-\ell .
$$
Every triangle $T$ avoiding $H$ meets every page of some book, by maximality of selections. It cannot be all-blue. It meets any page only by its sole red edge, so the forced book is not rotated (the two red edges there are different), and not an all-blue singleton. Its red edge is the original red spine of an unrotated pair or a one-red singleton. In particular the family left after deleting $H$ is exactly $J=F(G'-H)$.

Choose a maximum packing $D$ of $J$ of size $k$. Its members have distinct red edges in these unrotated books, and their blue edges avoid every book. Add each member as a page at its red edge. The supports remain disjoint, no book acquires more than three pages, and every selection still has $(b,m)$. The book principle on $m$ books with $m+c+k$ pages yields
$$
\tau(G)\le 3a+3m-c-k\le 3n-c-k. \tag{4}
$$
This argument needs no selection of red edges outside $N$ with multiplicity: a repeated opposite was rotated only once.

**Two colored residuals.** Selecting $E(A)$, $B(P')$ and a cover of $S$ gives, by the colored bound of Section 1,
$$
\tau(G)\le 3n-b+\tfrac83c-\tfrac23h. \tag{5}
$$
Selecting $E(A)$, $H$ and a cover of $J$ instead gives, by the same bound without its private-edge saving,
$$
\tau(G)\le 3n-b+2c-\ell+\tfrac83k. \tag{6}
$$

### 3. Certificate

Multiply (1)–(6), **in their displayed order**, by
$$
15,\quad 6,\quad 4,\quad 8,\quad 6,\quad 3
$$
and add. The $a,b,c,h,\ell,k$ coefficients vanish and $42\tau(G)\le117n$. Thus $\tau(G)\le (39/14)\nu(G)$, also for $n=0$. The six relaxed rows are simultaneously tight at
$$
(n,a,b,c,h,\ell,k)=(14,3,9,3,3,0,0),\qquad \tau=39.
$$
This is an LP witness, **not** a graph construction. Improving $39/14$ requires information beyond those six rows.

### 4. A separate colored-family consequence

For any red/blue graph $H_0$, let $F=F(H_0)$, and let $U,V,p,q,u,r$ be as in Section 1. Then in fact
$$
8\tau(F)\le 21p-5u .
$$
This strengthening is not needed in (1)–(6).

To see this, let $\ell$ be the number of distinct red opposites outside $R(U)$ in the $U,V$ books. The exchange proof in Section 1 gives $\ell\le r$. The first cover in that proof counts only $\ell$ added opposites, giving $\tau(F)\le3p-2q+\ell-u$. Rotate one representative per distinct opposite exactly as above, let $H$ be the resulting blue support, and let $D$ be a maximum packing of $F(H_0-H)$ of size $k$. The same avoiding-page proof, **inside $F$**, attaches $D$ to unrotated red spines. The new book cover has size at most $3p-q-k$ before removing the $u$ initially private red edges. Each remains a singleton: it can belong neither to $V$ nor to $D$, since a new page would be a second member on that red edge. Deleting those edges is safe. The rotated blue support has size $2p+2q-\ell$. Covering its residual by Section 1 gives the third bound below. Finally apply Section 1 to $F(H_0-B(U))$ and use $r\ge\ell$. In order the four rows are
$$
\begin{aligned}
\tau(F)&\le 3p-2q+\ell-u,\\
\tau(F)&\le 3p-q-k-u,\\
\tau(F)&\le 2p+2q-\ell+\tfrac83k,\\
\tau(F)&\le 2p+\tfrac83q-\tfrac23\ell.
\end{aligned}
$$
Weights $(7,8,3,6)/24$ cancel $q,\ell,k$, yielding the result. The relaxed rows agree at $(p,q,u,\ell,k)=(32,9,0,6,3)$, $\tau=84$.

Both rational certificates are checked by the accompanying Python verifier. The proofs use maximality only in the family specified at each step; no two-red or all-blue face is silently inserted into a one-red packing.

### Lean formalization

In [`Conjectures.TuzaConjecture`](../../lean/Conjectures/TuzaConjecture.lean),
`tuza_bound_39_14` proves the universal bound for finite `SimpleGraph`s.
`le_tuzaNu_iff_adj` and `tuzaTau_le_iff` express its packing and cover
numbers directly in terms of adjacent vertex triples.
`colored_tuza_bound_21_8` proves the private-edge refinement for every
maximum one-red packing; `colored_tuza_bound_21_8_plain` needs no packing as input.

The formal proof obtains the private-edge term from the unrefined colored
inequality: delete both blue edges of each of the $u$ private packed pages.
No surviving one-red triangle can use any edge of those pages, so a surviving
packing extends by all $u$ pages. This costs $2u$ cover edges and decreases
the packing number by at least $u$, giving the saving $21u-8(2u)=5u$ in the numerator.

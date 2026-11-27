# Connected chordal diagrams are counted by squares of Catalan numbers

**Theorem (Nabergall's Conjecture 8.5).** On $2n$ cyclically ordered points numbered starting at $1$, the number of perfect matchings with connected, chordal crossing graph is $C_{n-1}^2$ for $n\ge 1$, where $C_m=\binom{2m}{m}/(m+1)$. There is no quotient by rotation or reflection.

Two chords cross when their endpoints alternate. Passing to a subdiagram takes an induced subgraph, and the two cycle diagrams $T_k,B_k$ are the realizers of an induced $k$-cycle. Thus this counts exactly $\mathcal C_n(T_{\ge4},B_{\ge4})$. The shift matters: the [2021 preprint](https://arxiv.org/abs/2104.02296v1) has $C_n^2$, whereas the [published conjecture](https://escholarship.org/uc/item/1qg5647z) has $C_{n-1}^2$. For example, at $n=2$ only the crossing matching is connected.

We cut intervals whose outgoing chords form a clique. There can be many ways to cut a diagram, but the *earliest* cut gives a unique decomposition with a local counting rule. The rule yields a quadratic equation for a quotient of generating functions; extracting its first Laurent coefficient gives the Catalan square.

## 1. Intervals with a clique boundary

A **fragment** is a linearly ordered, nonempty interval of positions, some paired within the interval and the rest single. Its *weight* is the number $k$ of singletons. Complete it by appending $k$ new positions and pairing them in order with the singletons. The resulting $k$ outgoing strands are pairwise crossing. Call the fragment **valid** if this completed crossing graph is connected and chordal (no induced cycle of length at least four). Length always counts original positions, not appended ones.

In a diagram the **boundary** of an interval is the set of chords with exactly one end in it. Call the interval *good* if its boundary is a clique. Restricting a connected chordal diagram to a good proper interval gives a valid fragment: its completed graph is precisely the induced graph on chords touching the interval. The boundary is nonempty, since an interval paired entirely within itself would be disconnected from its complement. Every component of the induced graph meets the boundary, since an internal chord cannot cross a chord entirely outside. These observations also apply inside the completion of any valid positive-weight fragment.

A split of a fragment into two nonempty consecutive intervals $L,R$ is **admissible** when $L$ and $R$ are good in its completion. Write $E$ for the exterior interval of appended positions. Among the chords joining distinct sectors of $L,R,E$, any two share a sector, so they all cross: the three sector boundaries are cliques.

Conversely, take valid fragments of positive weights $i,j$ and choose an integer $t$ from $0$ to $\min(i,j)$. Make $t$ links from $L$ to $R$ by pairing the **first** $t$ singletons of $L$, in order, with the **last** $t$ singletons of $R$, in order. The remaining $i+j-2t$ singletons go to the exterior in order. This is the unique admissible gluing with $t$ links: in $L$, ends destined for $R$ must precede ends destined for $E$ to cross them, and in $R$ ends destined for $E$ must precede ends destined for $L$. The order within each group is forced by pairwise crossing.

The gluing is valid. Start with the clique of intersector strands. Attach the induced graph of each child along its nonempty boundary clique. There are no other edges: internal vertices from opposite children cannot cross, nor can an internal chord cross a strand missing its sector. Gluing connected chordal graphs along a nonempty common clique, with no edges between their exclusive vertices, preserves connectedness and chordality: an induced cycle using both exclusive sets would need two nonconsecutive vertices of the common clique. Restriction and gluing are inverse at a specified admissible split.

## 2. An admissible split exists

Here it is important to use **all** induced cycles, not just 4-cycles. Consider a cyclic partition of the endpoints into $d\ge4$ consecutive, nonempty sectors, each with clique boundary. We claim there is a good cut grouping at least two consecutive sectors on either side.

Discard chords internal to one sector. The remaining crossing graph is chordal. If it is complete, any cut works. Otherwise choose nonadjacent vertices $a,b$ and a clique $S$ separating them. To recall why $S$ exists, take an inclusion-minimal $a,b$-separator (possibly empty). Every member neighbors both the component of $a$ and the component of $b$ after deletion. Two nonadjacent members would be joined by two shortest paths with interiors in the respective components, forming an induced cycle of length at least four.

After deleting $S$, each occupied sector meets just one component, since its incident surviving strands are a clique. The sector sets occupied by distinct components do not interleave. Indeed, fix a component $K$ and a surviving chord $e$ outside it. Each strand of $K$ has both ends on the same side of $e$, since it does not cross $e$. Strands on opposite sides cannot cross, so connectivity puts all of $K$ on *one* side. Thus both ends of $e$ lie in a single gap between successive endpoints of $K$. Chords in different gaps cannot cross, so the entire component of $e$ lies in that gap. As no occupied sector is shared, the same conclusion holds for the gaps between occupied sectors.

Consequently each other component lies in one cyclic gap between consecutive sectors occupied by the component of $a$. Take the gap containing the component of $b$. It contains at least two sectors, the endpoints of strand $b$; its complement contains at least two, the endpoints of $a$. No surviving strand leaves the gap. Its boundary is contained in $S$, proving the claim.

Apply the claim initially with a sector per original position of the fragment and one sector for $E$ (weight positive). Regard these sectors as sides of a polygon. A cut is a diagonal between sector boundaries. It gives two smaller polygons, each with a new side representing the entire complementary group; this side still has clique boundary. Recursing gives a triangulation all of whose cuts are good. In the triangle incident to $E$, the two other sides delimit nonempty intervals $L,R$ giving an admissible split. This includes the case of a fragment of length two, where the initial polygon already is a triangle. Thus every positive-weight valid fragment of length at least two can be split. (For the polygon-scanline viewpoint for circle graphs, see also [Kloks, *Treewidth of circle graphs*](https://pure.tue.nl/ws/files/4250836/398379.pdf).)

## 3. The earliest cut

Call a fragment **irreducible** when every gap between consecutive positions is spanned by a pair internal to the fragment. A single position is irreducible. At an admissible split of a valid fragment, the fragment is irreducible exactly when $t>0$. For $t=0$ the split is an unspanned gap. For $t>0$, an $LR$ link spans the split. At a gap in $L$ on or after the first $LR$ opening, that link still spans the gap. Before the first opening, the prefix has no singleton of $L$ by the gluing order. If no internal pair of $L$ spanned the gap, this nonempty prefix would be paired entirely within itself, contrary to validity. The argument at the other end uses the last $LR$ closing in $R$.

Choose the admissible split with shortest left interval. For **positive-weight irreducibles of length at least two** the resulting decomposition is in bijection with triples

$$
(L,R,t),\qquad L\text{ valid irreducible of weight }i\ge1,\quad
R\text{ valid of weight }j,\quad 1\le t\le\min(i,j-1).
$$

To see necessity, $t>0$ by irreducibility. If $L$ is a single position then $i=t=1$ and positivity of the parent gives $j>t$. Otherwise split $L$ admissibly into $A,B$ and write $C=R$, $D=E$. Each of $A,B,C,D$ has clique boundary in the full completion: the graphs on chords touching $L$ are unchanged by restriction. If either there is no $AB$ link or there is no $CD$ strand, then $BC$ is good. Indeed two chords crossing the boundary of $BC$ that share a sector cross. With four distinct sectors they are either $AC$ and $BD$, which alternate, or $AB$ and $CD$, excluded here. Hence $A\,|\,BC$ would be an earlier admissible split than $AB\,|\,C$. This contradiction gives an $AB$ link (so $L$ is irreducible) and a $CD$ strand (so $j>t$).

For sufficiency glue any indicated triple. The parent is irreducible since $t>0$, and has positive weight since $j>t$. At any putative earlier cut, the new gap lies strictly inside $L$. Some pair internal to $L$ spans this gap by irreducibility. This pair and a strand from $R$ to $E$ would both be on the boundary of the new right interval, but they do not cross. Thus the indicated split is the earliest one, proving uniqueness.

Finally every positive-weight valid fragment is a nonempty sequence of positive-weight valid irreducibles: split at all gaps not spanned by internal pairs. Each piece must have a singleton by connectivity, and its boundary is a subset of the original singleton clique, so it is valid. Conversely concatenating such pieces (the $t=0$ gluing) gives precisely those unspanned gaps between pieces.

## 4. The generating function

Use $z$ per position. Write $I_i$ for the generating series of positive-weight valid irreducibles of weight $i$, and $H_j$ for that of all valid positive-weight fragments of weight $j$. Put

$$
I(u)=\sum_{i\ge1}I_i u^i,\qquad H(u)=1+\sum_{j\ge1}H_j u^j=\frac1{1-I(u)}.
$$

The closed diagrams being counted have series $zH_1$: the position $1$ is the external end of the unique singleton in the rest of the diagram. In particular, a weight-one fragment of length $2m+1$ corresponds to $m+1$ chords, not $m$.

Set $v=u^{-1}$ and $U_p=(u^{p+1}-v^{p+1})/(u-v)$ for $p\ge0$. These are Laurent polynomials; multiplying their geometric sums gives

$$
U_p U_q=\sum_{h=0}^{\min(p,q)}U_{p+q-2h}.
$$

For a triple above, put $p=i-1$, $q=j-2$, $h=t-1$. Its output of weight $k=i+j-2t$ contributes to $U_{k-1}=U_{p+q-2h}$. Therefore, including the singleton of length one,

$$
A=z+AB,\qquad A=\sum_{i\ge1} I_i U_{i-1},\qquad B=\sum_{j\ge2}H_j U_{j-2}.
$$

All sums are coefficientwise finite in $z$. Multiplying $A(1-B)=z$ by $(u-v)^2$ and using the definitions gives

$$
(I(u)-I(v))\big(uH(v)-vH(u)\big)=z(u-v)^2.
$$

Here the $j=1$ terms in the difference for $B$ cancel. Substituting $I=1-1/H$ and writing $R=H(u)/H(v)$ leaves

$$
\frac uR+vR=u+v-z(u-v)^2.
$$

Work formally in $\mathbb Q(u)[[z]]$. Differentiate in $z$ and use $(u/R-vR)^2=(u/R+vR)^2-4$. Since $R=1$ at $z=0$, the square root is determined, giving

$$
\frac{\partial_z R}{R}=\frac{u-v}{\sqrt{(1-z(u+v))^2-4z^2}}.
$$

## 5. A walk coefficient

The left side is the difference of the logarithmic derivatives of $H(u)$ and $H(v)$. As $H(u)$ has constant coefficient $1$ in $u$ and no negative powers, its logarithmic derivative has $u^1$ coefficient $H_1'$. The term from $H(v)$ has no positive powers. To extract this coefficient on the right use

$$
\frac1{\sqrt{(1-z(u+v))^2-4z^2}}
=[w^0]\frac1{1-z(u+v+w+w^{-1})}.
$$

Indeed, expand the right side in $z(w+w^{-1})/(1-z(u+v))$: only even powers $2r$ survive, with constant term $\binom{2r}{r}$.

At $z^{2m}$ the desired $u^1$ coefficient is the number of axial unit walks of length $2m$ on the square lattice ending at $(0,0)$ minus those ending at $(2,0)$, all starting at the origin. The two terms come from the prefactor $u-u^{-1}$. In the coordinates $(x+y,x-y)$ a step is a pair of independent signs. Hence the difference is

$$
[z^{2m}]H_1'=\binom{2m}{m}^2-\binom{2m}{m+1}^2=(2m+1)C_m^2.
$$

Dividing by $2m+1$ gives $[z^{2m+1}]H_1=C_m^2$, as required.

**Check.** At $n=1,\ldots,10$ the counts are $1,1,4,25,196,1764,17424,184041,2044900,23639044$. The finite checks in `verify.py` are independent evidence for the decomposition; the coefficient argument, not extrapolation from those counts, proves the theorem.

**Verification scope.** Run `python3 verify.py` here to check the bijection on every positive-weight fragment through nine positions and the integer recurrence through 25 chords. Add `--brute 10` for direct enumeration of perfect matchings, including distributions by root degree and number of terminal chords. The Lean theorem `NabergallChordalDiagrams.walk_coefficient` proves the all-length walk identity in Section 5 from the four-step walk recurrence; the diagram decomposition and its generating-function solution above are a written proof, not an end-to-end Lean formalization.

# Tuza's inequality after deleting five vertices to a bipartite graph

**Structural theorem.** Let $G$ be a finite simple graph. If deleting at most five vertices leaves a bipartite graph, then $\tau(G)\le 2\nu(G)$.

**Density corollary.** For every fixed real $c<3$, all sufficiently large $n$-vertex graphs with at least $n^2/4-cn$ edges satisfy $\tau(G)\le 2\nu(G)$.

Here $\nu$ is the maximum number of pairwise **edge**-disjoint triangles and $\tau$ the minimum number of **edges** meeting every triangle. The structural theorem below is the new input. It does not assume any density or codegree condition. Section 3 adapts Liu and Zeng's density argument, with the dependence on $c$ made explicit. Section 5 sharpens the corollary to within an additive constant of the endpoint. Neither result is a universal solution to Tuza's conjecture. This is a mathematical proof, not a Lean formalization.

## 1. A minimum counterexample and its links

Choose a counterexample to the structural theorem minimizing $|V(G)|+|E(G)|$. Every proper subgraph still belongs to the class, so it satisfies Tuza's inequality. By [Kandasamy, Theorem 1.1](https://arxiv.org/abs/2610.15269), all graphs with maximum degree at most ten satisfy the inequality. We use this external result **only** to conclude that $|V(G)|\ge 12$. Enlarge the exceptional set to a set $S$ of exactly five vertices. Write $F=G[S]$, $J=G-S$. Thus $J$ is bipartite and $t=|V(J)|\ge7$. For $v\in V(J)$ put

$$
 A_v=N_G(v)\cap S,\qquad a_v=|A_v|,\qquad q_v=d_J(v).
$$

Call a graph $L$ weak König–Egerváry (WKE) if it has a matching $M$ and a set $Q$ of at most $|M|$ vertices such that every edge outside $M$ meets $Q$. No link $L=G[N_G(v)]$ is WKE: with such witnesses take the smaller graph $(G-v)-M$. Extend its packing by the $|M|$ triangles at $v$ on the matching edges. Extend its cover by $M$ and the spokes from $v$ to $Q$. The budget increases by at most $2|M|$, all triangles at $v$ are hit, and every other triangle not in the smaller graph uses $M$. This is the singleton version of [Puleo's reduction](https://doi.org/10.1016/j.ejc.2015.03.006).

Here are the small facts about WKE that we need.

* Every graph with vertex cover of size at most two is WKE. If it has a matching of size at least two, use that matching and the cover. Otherwise its nonisolated edges, if any, form a star or a triangle (pairwise intersecting pairs). For a star use its center and one edge; for a triangle use one edge and the opposite vertex.
* All graphs of order at most four are WKE: if there is no vertex cover of size two and the order is four, the graph must be $K_4$. A perfect matching there leaves a four-cycle with a two-vertex cover.
* In a non-WKE graph on five vertices the missing edges form a matching. Indeed a matching of size two exists by the star-or-triangle argument. An independent triple gives a cover of size two. If a triple induces just the edge $ab$ and an isolated vertex $z$, let $Q$ be the two other vertices. An edge in $Q\cup\{z\}$ extends $ab$ to a two-matching and $Q$ covers every edge except possibly $ab$. Without such an edge $Q\cup\{z\}$ is an independent triple. Thus every triple spans at least two edges, as asserted.

In particular $\delta(G)\ge5$. For every $v\in J$ its neighbors in $J$ are independent, so $A_v$ covers its link; hence $a_v\ge3$.

**Star reduction (any number of exceptional vertices).** For a nonempty $R\subseteq N_J(v)$ let $U(R)=\bigcup_{y\in R}(A_v\cap A_y)$. Then $|U(R)|>|R|$. Otherwise choose an inclusion-minimal violation. If $U(R)$ is empty, a single edge $vy$ lies in no triangle and may be discarded. Otherwise $|U(R)|=|R|$: this is immediate for a singleton, and for $|R|\ge2$ delete any one row and apply minimality. Every proper nonempty row subset satisfies strict Hall, so there is a bijective choice $y\mapsto s_y\in A_v\cap A_y$ onto $U(R)$. Pack the triangles $vys_y$ and pay for the $2|R|$ edges

$$
 X=\{vs:s\in U(R)\}\cup\{ys_y:y\in R\}.
$$

Discard also $D=\{vy:y\in R\}$. Every triangle through $D$ meets $X$: the third vertex is in $S$ since $J$ is bipartite, and its color belongs to $U(R)$. All packed edges lie in $X\cup D$. A packing and a cover of the proper subgraph $G-(X\cup D)$ therefore extend within budget, a contradiction. Taking all the rows proves $q_v<a_v$ (for zero rows use $a_v\ge3$).

Consequently $\Delta(J)\le4$. Each edge $xy$ of $J$ also has a list of **at least three** colors

$$
 L(xy)=A_x\cap A_y.
$$

This is immediate if $a_x,a_y\ge4$. If $a_x=3$, then $q_x\le2$ by the Hall reduction and $q_x\ge2$ by minimum degree. Its link has order five; its two $J$-neighbors are nonadjacent and hence already form a missing edge of this link. All other missing edges are disjoint from it. Thus each of the two neighbors sees every color in $A_x$.

## 2. Packing the bipartite edges

Let $m=e(J)$, $e=e(F)$, $u=\nu(F)$ and $h=e-2u$. A proper list edge-coloring of a subgraph of $J$, using the lists above, gives a triangle per colored edge: the color is its third vertex, in $S$. Properness prevents reuse of a spoke. No edge inside $S$ is used. On the cover side, $E(F)\cup E(J)$ of size $e+m$ hits every triangle.

A bipartite graph of maximum degree $d$ decomposes into $d$ matchings, by regularizing with dummy vertices/edges on equal-sized sides and repeatedly removing a Hall perfect matching. Also, one may replace the uniform palette by arbitrary edge lists of size $d$ ([Galvin](https://doi.org/10.1006/jctb.1995.1011)). For completeness: orient conflicts between edges of the bipartite graph using a fixed ordinary $d$-edge-coloring, toward the smaller ordinary color on the left and the larger on the right. An edge of color $i$ has at most $(i-1)+(d-i)=d-1$ outgoing arcs. On any subset of the edges, take a stable matching in that bipartite subgraph for these preferences (left vertices propose in preference order; right vertices keep their best offer; rejection is final; a blocking edge cannot remain). Its edges are independent in the conflict graph, and every remaining edge points to one of them, by stability. For an available list color take such a matching among edges offering it; color that matching and delete it, and remove the color from the remaining lists. Each remaining edge losing a color loses an outgoing arc. The invariant “list size greater than outdegree” proves the claim by induction.

In particular, if $\Delta(J)\le3$ we can pack $p=m$ such triangles. In general remove a smallest of four ordinary matching classes (empty classes allowed); on the subcubic remainder the lists still have size at least three. We can therefore achieve

$$
 p\ge m-\lfloor m/4\rfloor,\qquad b:=2p-m\ge m-2\lfloor m/4\rfloor.
$$

We may improve this choice of packing in specific cases. Whenever $b\ge h$ we are done: adjoin a maximum packing of $F$, obtaining $2(p+u)\ge m+e$.

**Five-vertex arithmetic.** We have $h\le6$. If $h\ge5$, at most one edge of $F$ is *mandatory* (belongs to the edge union of every maximum packing in $F$). To see this, if $u=0$, Mantel gives $e\le6$, and no edge is mandatory. Every five-vertex graph with at least eight edges has two edge-disjoint triangles: it contains a $K_5$ minus two edges. If the missing edges are $ab,ac$ use $ade,bcd$; if they are $ab,cd$ use $eac,ebd$. Thus when $u=1$ we have $e\le7$. If also $h\ge5$ then $e=7$ and there are at least two distinct triangles: in a graph with just one triangle each of the other two vertices has at most one neighbor on it, giving at most six edges. The two triangles share at most one edge. Finally if $u\ge2$ then $h\le 10-4=6$; if $h\ge5$, necessarily $u=2$ and $e\ge9$. Deleting any one edge still leaves at least eight edges, and hence a two-packing.

In particular, if $m\ge10$, the bound on $b$ gives $b\ge6$ (check $m=10,11,12,13$ and then increase $m$ by four). It remains to handle $m\le9$.

**If $J$ has an isolate $v$**, then $A_v=S$ by minimum degree. Its five-vertex link $F$ misses only a matching. Extend that missing matching on $S\cup\{v\}$ to a partition into three pairs. Between the pairs all edges are present. This $K_{2,2,2}$ packs four triangles (label each pair by bits and take the four even-parity triples). These four are disjoint from the bipartite-edge packing (each using one vertex of $S$), which uses no edges at $v$ or inside $S$. If $m\ge2$ then $b\ge2$, giving $2(p+4)\ge m+10\ge m+e$. If $m=0,1$, at least $t-2m\ge5$ vertices of $J$ are isolates, all adjacent to $S$. Use five isolates to pack all $e$ edges inside $S$, one isolate per matching in a five-coloring of $E(K_5)$ (on residues modulo five color $ij$ by $i+j$). Color all $m$ edges of $J$ too. This settles the isolate case.

**If $J$ has no isolate**, then $m\ge4$ since $t\ge7$. We can always arrange $b\ge4$ for $4\le m\le9$. For $6\le m\le9$ this is the matching-class bound. For $m=4,5$ it holds if $\Delta(J)\le3$. If there is a degree-four vertex, its star already uses five vertices and four edges. No isolate and $t\ge7$ force $m=5$ and the last edge to be disjoint from the star. The center has $a_v=5$ (Hall reduction), and its leaves have at least four colors (minimum degree). Give the four star edges distinct colors greedily, then color the separate edge. Here $p=5$.

If there is a **leaf** $v$, only $h\ge5$ needs further consideration. At least three colors of $A_v$ remain unused at $v$ after the bipartite-edge packing (each using one vertex of $S$). There is a nonmandatory edge $ij$ of $F$ between unused colors. Indeed, for $a_v=4$ the link has order five and every triple spans at least two edges, of which at most one is mandatory. For $a_v=5$ at least four colors remain. If $u=0$, some edge lies among any four colors since $e=h\ge5$ and deleting one vertex loses at most four edges; none is mandatory. If $u>0$ then $e\ge7$, giving at least three edges on any four colors, again sufficient. Pack $vij$ and a maximum packing of $F-ij$, which has size $u$. Now $b+2\ge6\ge h$.

The remaining graph $J$ has **minimum degree at least two**. If it is subcubic, $b=m\ge t\ge7$. Otherwise let $r$ be the number of degree-four vertices. Then $m\ge t+r$. If $r\ge2$, $m\le9$ and $t\ge7$ force $r=2,t=7,m=9$ and every other degree equal to two. This is impossible in a bipartite graph: on either side the degree sum is the odd number nine but all degrees are even. Thus there is exactly one degree-four vertex. Delete any one of its edges and list-color the rest. This gives $b\ge m-2\ge6$ since $m\ge t+1\ge8$.

Every case contradicts the assumed counterexample. This proves the structural theorem.


## 3. The edge-count corollary

We give the dependency check for the three packing regimes of [Liu and Zeng](https://arxiv.org/abs/2610.15539). Write $k=\nu(G)$ in this section. A negative $c$ imposes a stronger hypothesis than $c=0$, so take $c\ge0$ fixed. All “sufficiently large” conditions below can depend on $c$. The case $k=0$ is immediate.

**Case 1: $k\ge10^{-5}n^2$.** No edge-count assumption at all is needed here. Use the Haxell–Rödl theorem (Liu–Zeng, Lemma 2.1) with $\eta=10^{-18}$, and fractional packing/cover duality: an optimum fractional edge cover $f\in[0,1]^{E(G)}$ has total weight $\nu^{\ast}$ with $0\le \nu^{\ast}-k\le\eta n^2$. Suppose $\tau>2k$ and put $l=\tau$. A maximum cut gives $2l\le e(G)$. For $0\le s\le1/3$ define $Z_s=\{f<s\}$ and $D_s=\{f\ge(1-s)/2\}$. They are disjoint. A triangle using $Z_s$ must meet $D_s$, or its weight sum is below one. Retain $Z_s$ and the crossing edges in a maximum cut of the edges outside $D_s\cup Z_s$. This is triangle-free and gives $2l\le e(G)+|D_s|-|Z_s|$.

Order the weights $f_1\ge\cdots\ge f_{e(G)}$. The edges of weight at least $1/3$ cover, so $f_l\ge1/3$. For $1\le i\le l$,

$$
 2f_i+f_{2l+1-i}\ge1.
$$

Otherwise take $f_{2l+1-i}<s<1-2f_i$; then $s\in[0,1/3]$, $|D_s|\le i-1$, and $e(G)-|Z_s|\le2l-i$, contradicting the cut bound. Sum the paired inequalities to obtain $\sum_{i>l} f_i\le2(\nu^{\ast}-l/2)$. Also each pair of weights contributes at least $1/2$ after truncating each to $1/2$ (if neither reaches $1/2$, use the paired inequality). Therefore $\sum_e(f(e)-1/2)_+\le \nu^{\ast}-l/2$. In particular $0\le \nu^{\ast}-l/2<\eta n^2$.

Split edges by weight into $L=[0,1/6)$, $M=[1/6,2/3)$ and $D=[2/3,1]$ (meaning inverse images). The first $l$ edges lie in $M\cup D$. The tail bound gives $|M|+|D|-l<12\eta n^2$; the excess bound gives $|D|<6\eta n^2$. Thus $|M|>2k-6\eta n^2>10^{-5}n^2$. In $G-D$ no triangle contains two $L$-edges since its weight would be less than $2/6+2/3=1$.

Here is the triangle-independent saving used at this point (Liu–Zeng). If no triangle of an $n$-vertex graph contains two edges of a set $L$ and its complement $M$ has $|M|\ge\beta n^2$, $0<\beta<1/2$, there is a cover of size at most $|M|-\beta^3 n^2/36$. For disjoint sets $U,V$ one can save

$$
 e_M(U,V)-e_L(U)-e_L(V)
$$

over the cover $M$: retain the crossing $M[U,V]$ and all $L$ except the internal edges of $U,V$. A triangle would need two crossing $M$-edges and an internal edge in one part, impossible. In the residual $L$-graph successively take the full neighborhood of any vertex of degree at least $\beta n/2$ as a block and remove that block. The blocks are independent in the entire graph (two $L$-edges at their center) and there are at most $2/\beta$ of them. The leftover $W$ spans at most $\beta n^2/4$ edges of $L$. At least $\beta n^2/3$ edges of $M$ are either between blocks, between blocks and $W$, or inside $W$. In the first case one pair of blocks saves at least $\beta^3 n^2/6$. In the second, one block sees at least $\beta^2n^2/6$ edges to $W$; take it and a random subset of $W$ of inclusion probability $\beta/3$, saving in expectation at least $(\beta/3)(\beta^2n^2/6)-(\beta/3)^2(\beta n^2/4)=\beta^3n^2/36$. In the third case a fair random cut of $W$ saves at least $(\beta n^2/3-\beta n^2/4)/2=\beta n^2/24$ in expectation.

Apply the saving with $\beta=10^{-5}$ and then add back $D$. The resulting cover size is at most $|D|+|M|-\beta^3 n^2/36<l$ since $12\cdot10^{-18}<10^{-15}/36$. Contradiction.

**Common decomposition.** If $H$ is triangle-free with deficit $D=n^2/4-e(H)\le10^{-4}n^2$, let $V_1$ be a maximum-degree vertex's neighborhood and $V_2$ its complement. The first set is independent, and

$$
 e(H)+e_H(V_2)=\sum_{v\in V_2}d_H(v)\le |V_1||V_2|\le n^2/4.
$$

Thus $D\ge0$, the cross deficit $d=|V_1||V_2|-e_H(V_1,V_2)$ is at most $2D$, and the part imbalance from $n/2$ is at most $\sqrt{2D}$ since $e_H(V_1,V_2)\ge n^2/4-2D$. Remove into $A$ all vertices missing more than $n/5$ neighbors across. Then $|A|\le10d/n\le n/500$ by counting both ends of missing edges. Put $B=V_1\setminus A,C=V_2\setminus A$. Both have size greater than $9n/20$ since $\sqrt{2}/100+1/500<1/20$. Their missing cross-pair count is at most $d$. Every two distinct vertices in either have more than $9n/20-2n/5=n/20$ common $H$-neighbors in the other. Hence both are independent in $H$.

**Case 2: $n^{2/3}<k<10^{-5}n^2$.** For a maximum packing $P$, remove its edges to obtain triangle-free $H$. Now $D\le cn+3k\le10^{-4}n^2$ as soon as $c/n\le7\cdot10^{-5}$. Use the common decomposition. For $x\in A$, put into $L_x$ its $H$-neighbors in $B$ and all endpoints in $B$ of the packed triangles $xbb'$; define $R_x$ on $C$ analogously.

There is no $H$-edge $bc$ from $L_x$ to $R_x$. Indeed if $xb,xc$ are both in $H$ there is already an $H$-triangle. If just $xb$ is in $H$, replace the packed $xcc'$ with $xbc,zcc'$, taking a common $H$-neighbor $z$ of $c,c'$ in $B\setminus\{b\}$. The other mixed case exchanges the sides. If neither spoke is in $H$, replace the two packed triangles $xbb',xcc'$ with $xbc,bb'c_0,b_0cc'$, using common $H$-neighbors $c_0\notin\{c,c'\}$ and $b_0\notin\{b,b'\}$. Each exchange uses only the freed edges and edges of $H$, without an edge repetition, improving $P$. The exclusions are possible once $n/20>2$. Nor is any packed triangle entirely in $B$ or entirely in $C$: repack two of its edges using distinct common $H$-neighbors across. Thus $\min(|L_x|,|R_x|)\le\sqrt d$.

Put $x$ on its smaller side, obtaining $X=B\cup A_1$ and $Y=C\cup A_2$. Let $Q$ count the monochromatic packed triangles having at least two vertices in $A$. Every packed triangle contributes one internal edge, plus two if monochromatic. For monochromatic triangles with exactly one $x\in A$, those two extras are exactly the number of spokes outside $H$ added to the smaller set $L_x$ or $R_x$, since packed triangles are edge-disjoint. All internal $H$-edges are in $A_1,A_2$ or are counted by the $H$-neighbors on that smaller side. Thus the number of internal edges of $G$ is

$$
 k+e_H(A_1)+e_H(A_2)+2Q+\sum_{x\in A}\min(|L_x|,|R_x|).
$$

Each of the $Q$ triangles uses a distinct internal edge of $A$ outside $H$, so $e_H(A_1)+e_H(A_2)+Q\le\binom{|A|}{2}$. The internal edges cover. Consequently

$$
 \tau-k\le |A|\sqrt d+|A|^2
 \le 20\sqrt 2\,D^{3/2}/n+400D^2/n^2 .
$$

Using $D\le cn+3k$, $(a+b)^{3/2}\le\sqrt2(a^{3/2}+b^{3/2})$ and $(a+b)^2\le2(a^2+b^2)$ gives

$$
 \frac{\tau-k}{k}\le
 40 c^{3/2}\frac{\sqrt n}{k}+120\sqrt3\,\frac{\sqrt k}{n}
 +\frac{800c^2}{k}+7200\frac{k}{n^2}
 <40 c^{3/2}n^{-1/6}+800c^2n^{-2/3}+\frac34 .
$$

Indeed $120\sqrt{3\cdot10^{-5}}<2/3$ and $7200\cdot10^{-5}<1/12$. This is less than one for all large $n$ at **any fixed $c$**.

**Case 3: $0<k\le n^{2/3}$.** Choose a spanning $G'\subseteq G$ of minimum edge count subject to $e(G)-e(G')=k-k'$ with $k'=\nu(G')$. If an edge $uv$ has more than $2k'$ common neighbors in $G'$, any maximum packing of $G'-uv$ uses at most $2k'$ edges incident to $u$ or $v$ (no triangle there uses both endpoints). It can be extended by a triangle on $uv$, so deleting $uv$ drops the packing number exactly one, contradicting minimality. Thus every edge has codegree at most $2k'$. Also $\tau(G)\le k-k'+\tau(G')$. We may take $k'>0$.

Remove the edges of a maximum packing of $G'$ to obtain $H$. Its deficit is $D\le cn+k+2k'\le(c+3)n$. Write $K=c+3$ and $a=20K$. The common decomposition applies when $Kn\le10^{-4}n^2$. Now $|A|\le a$, $d\le2Kn$, and $B,C$ are independent even in $G'$, since a same-side edge would have more than $n/20>2n^{2/3}\ge2k'$ common neighbors for large $n$. For $x\in A$ the product of its $H$-neighbor counts in $B,C$ is at most $d$: all such cross-pairs are missing in triangle-free $H$. Place $x$ on its smaller side, obtaining $X=B\cup A_1,Y=C\cup A_2$. It follows that

$$
 \big||X|-n/2\big|,\ \big||Y|-n/2\big|\le \sqrt{2Kn}+a,\qquad
 e_{G'}(X)+e_{G'}(Y)\le a^2/2+a\sqrt{2Kn}+3k'.
$$

Here moving $A$ changes each side size by at most $a$, and at most $3k'$ edges were put back into $H$.

Let $S_1,S_2$ be minimum vertex covers of $G'[X],G'[Y]$ of sizes $s_1,s_2$; their sum is at most $a$ because $A_1,A_2$ are covers. In each side choose a witness $T_i$ containing $S_i$ of size at most $s_i^2+2s_i$ with the same vertex-cover number as that side: for every $v\in S_i$ retain up to $s_i+1$ of its neighbors outside $S_i$, or all if fewer. A minimum cover of the witness has size at most $s_i$; if it misses an edge to an omitted neighbor, it omits its $S_i$ endpoint and must contain all $s_i+1$ retained neighbors, impossible.

For $y\in Y\setminus T_2$, its nonneighbors in $T_1$ together with one endpoint per edge internal to $N_{G'}(y)\cap T_1$ cover $T_1$. Summed over $y$, the internal-edge error is at most $2k'e_{G'}(T_1)$ by the codegree bound. Count also with sides interchanged. The two sets of missing pairs are disjoint (one end is in $T_1$ in one count, outside $T_1$ in the other). Hence

$$
\begin{aligned}
 |X||Y|-e_{G'}(X,Y)
 &\ge s_1(|Y|-|T_2|)+s_2(|X|-|T_1|)\\
 &\qquad -2k'\big(e_{G'}(T_1)+e_{G'}(T_2)\big)\\
 &\ge (s_1+s_2)n/2-O_c(\sqrt n+k'+1).
\end{aligned}
$$

The last bound uses only $s_1+s_2\le a$ and $|T_1|+|T_2|\le a^2+2a$. Adding the internal edges, using $|X||Y|\le n^2/4$, and comparing with $e(G')=e(G)-k+k'\ge n^2/4-cn-k+k'$ gives

$$
 ((s_1+s_2)/2-c)n\le O_c(n^{2/3}).
$$

If $c<3$ is fixed, $s_1+s_2\ge6$ would give the impossible lower bound $(3-c)n$ on the left for sufficiently large $n$. Thus $G'-(S_1\cup S_2)$ is bipartite with at most five vertices removed. By the structural theorem $\tau(G')\le2k'$. Transfer back to get $\tau(G)\le k+k'\le2k$. This proves the density corollary.

## 4. Why the next half-unit requires more

Let $F_0$ be *any* fixed graph with a $j$-vertex exceptional set and a bipartite remainder, with side sizes $p,q$. Adjoin $r$ new vertices to each side and add all cross edges involving a new vertex and a vertex of the opposite side, but none to the exceptional set. Every new vertex has an independent neighborhood, so the triangle system is unchanged. If $n_0=j+p+q$, then $n=n_0+2r$ and

$$
 n^2/4-e(G_r)=jr+n_0^2/4-e(F_0)=jn/2+O_{F_0}(1).
$$

In particular **any** fixed density coefficient $c>j/2$ implies the full $j$-vertex structural statement, not just some restricted dense subclass. Conversely the three cases above show that the structural statement for $j$ implies the density statement for every fixed $c<(j+1)/2$. The padding implication is strict at the left endpoint; no conclusion about the sign of its constant error is needed.

With six colors even two four-element neighborhoods can meet in only two colors. The star reduction still gives maximum bipartite degree five, but the five-color packing argument (three lists on a subcubic remainder and a core cost at most six) no longer follows. No six-vertex structural theorem is asserted.

## 5. Within a constant of the endpoint

In fact there is an **absolute constant** $C$ such that, for all sufficiently large $n$, the weaker edge hypothesis

$$
 e(G)\ge n^2/4-3n+C
$$

suffices. One may take $C=\binom{693600}{2}+349$; no effort is made to optimize it. This does not assert the result with $C=0$.

Suppose not. Apply the three regimes with $c=3$. Cases 1 and 2 are unchanged; Case 3 gives the peeled graph $G'$ with $k'=\nu(G')$, codegrees at most $2k'$, $e(G)-e(G')=k-k'$, and an exceptional set of size at most **six** (size at least seven would give $n/2\le O(n^{2/3})$, impossible for large $n$). Since $\tau(G)>2k$, transfer gives $\tau(G')>k+k'\ge2k'$. Delete the edges internal to these six vertices, at most fifteen edges. The remainder is tripartite. By Haxell–Kohayakawa's strict tripartite bound with $\varepsilon>0.044$ (Liu–Zeng, Theorem 2.3),

$$
 2k'<\tau(G')\le15+(2-\varepsilon)k'.
$$

Thus $k'<3750/11$ and $k'\le340$. Also $k+k'<\tau(G')\le3k'$, so $k-k'\le339$.

Let $K$ be induced by the vertices on triangles of $G'$. All triangles lie there, so $K$ violates Tuza's inequality and its minimum vertex deletion number to bipartiteness, $\sigma(K)$, is at least six by the structural theorem. If $h=|V(K)|$, then $h\le6(k')^2\le693600$: every triangle uses an edge of a fixed maximum packing, whose vertex set has size at most $3k'$. Each of the $3k'$ edges has at most $2k'-1$ common neighbors outside that vertex set (one neighbor is already in its packed triangle).

We need an elementary extension bound: if $K$ is an induced $h$-vertex graph inside an $n$-vertex graph $L$ and no triangle of $L$ uses a vertex outside $K$, then

$$
 e(L)\le e(K)+(n-\sigma(K))^2/4 .
$$

To prove it, keep $K$ fixed and maximize the number of edges over all such extensions with this $n$. Among maximizers maximize the sum of squared sizes of the exterior twin classes, where two exterior vertices are twins when their open neighborhoods in the *whole* graph agree. Nonadjacent exterior vertices have equal degrees: otherwise replace the lower-degree vertex by a twin of the other, increasing the edge count and introducing no exterior triangle. If two distinct twin classes have a nonedge between them, there are no edges between them. Replace an entire one of these classes by twins of the other. The edge count is unchanged (both degrees were equal), and no exterior triangle is introduced. The remaining classes do not split, and the two nominated classes merge, strictly increasing the sum of squares. Thus the extremal exterior is complete multipartite, with at most two parts since it is triangle-free. Write their sizes $r,s$, allowing an empty part. Their common neighborhoods in $K$ are independent sets $I_1,I_2$, respectively (empty for an empty part). They are disjoint because otherwise there is an exterior triangle. Their union induces a bipartite graph, so $|I_1|+|I_2|\le h-\sigma(K)$. The edge count is

$$
 e(K)+rs+r|I_1|+s|I_2|
 =e(K)+(r+|I_2|)(s+|I_1|)-|I_1||I_2|
 \le e(K)+(n-\sigma(K))^2/4 .
$$

This proves the extension bound.

Finally $e(G)\le339+e(K)+(n-6)^2/4\le n^2/4-3n+\binom{693600}{2}+348$, a contradiction. The additive conclusion in particular recovers all fixed $c<3$.

**Quantization of the first obstruction.** More generally, if Tuza's inequality is false, let $j$ be the least vertex deletion number to bipartiteness among its counterexamples. Then the maximum number of edges of an $n$-vertex counterexample, for all sufficiently large $n$, equals

$$
 n^2/4-jn/2+O(1).
$$

The padding construction of Section 4 gives the lower bound from a fixed witnessing graph. For the other parity of $n$, place one extra new vertex on one side: the new edge count increases by $r+O(1)$, preserving the bounded error. A maximizing graph therefore satisfies the edge hypothesis for the fixed $c=j/2+1$. Cases 1 and 2 are impossible. In Case 3 the coarse exceptional set $A$ already has bounded size depending only on $c$, with independent $B,C$ in $G'$. Delete $E(G'[A])$ to obtain a tripartite graph. The same gap argument gives $k'=O_c(1)$, $k-k'=O_c(1)$, and a bounded-order triangle core $K$. By minimality of $j$, $\sigma(K)\ge j$. Apply the extension bound to $G'$ and add back the bounded number of peeled edges. This proves the claimed upper bound. The structural theorem proves $j\ge6$ if such a $j$ exists; the argument does not assume there actually is a counterexample.

# Improved Upper Bound, Small-Order Settlement, and Musquash Exclusions for Conway's Thrackle Conjecture

A *thrackle* is a drawing of a finite simple graph $G = (V, E)$ in the plane in which every two distinct edges meet in exactly one point: either a common endpoint or a proper crossing, with no three edge interiors meeting at a point. A graph is *thrackleable* if it admits such a drawing. Write $n = \lvert V(G)\rvert$ and $m = \lvert E(G)\rvert$. **Conway's thrackle conjecture** (recorded by Woodall, 1971; see [the source statement](SOURCE.tex), Simon, *Conway's thrackle conjecture: a new upper bound of 4n/3*, `arXiv:2610.31589v2`, October 2026) asserts that $m \le n$ for every thrackleable graph.

Conway's conjecture in full remains open. Combining audited SAT/DRAT/strict-RUP refutations of all minimal bicyclic graphs up to $15$ vertices plus four $16$-vertex obstructions, an elementary zero-curvature thread-discharging proof whose combinatorial core is formalized in Lean 4, exact periodic plane sharpness witnesses, and a topological confinement argument on standard odd musquashes, we establish four main results that improve both the small-order barrier ($n \le 12$ to $n \le 15$) and the global upper bound ($\lfloor 4(n-1)/3 \rfloor$ to $\lfloor 5(n-1)/4 \rfloor$):

1. **Theorem 1 (Small-order settlement through $n \le 15$ and targeted $n = 16$ exclusions).** Every thrackleable graph on $n \le 15$ vertices satisfies $m \le n$. Moreover, the four $16$-vertex minimal bicyclic graphs $\Theta(1,7,9)$, $\mathrm{DB}(8,8,1)$ (two vertex-disjoint $8$-cycles joined by a single edge), $\Theta(3,5,9)$, and $\Theta(1,5,11)$ are not thrackleable.
2. **Theorem 2 (Global upper bound).** Every thrackleable graph on $n \ge 5$ vertices and $m$ edges satisfies
   $$m \le \left\lfloor \frac{5}{4}(n - 1) \right\rfloor.$$
   More generally, $m \le \max\bigl(n, \frac{5}{4}(n - 1)\bigr)$ for all $n \ge 0$ (the exception at $n = 4$ is $K_3$ with a pendant edge, which has $m = 4$). As shown in Theorem 3, the $5/4$ slope is sharp for this $S^2$ and $\mathbb{RP}^2$ embedding-and-discharging method (not for thrackles themselves, where Conway's conjecture asserts $m \le n$).
3. **Theorem 3 (Sharpness, necessity, and the 6-cycle barrier).** Within bipartite plane embeddings with no $C_4$ and no connected bicyclic subgraph on at most $N$ vertices — denoted $\mathrm{NSB}(N)$ — the asymptotic slopes $21/16$ for $N = 13$, $9/7$ for $N = 14$, $62/49$ for $N = 15$, and $5/4$ for $N = 16$, as well as for $\mathrm{NSB}(15)$ together with $\Theta(1,7,9)$ and $\mathrm{DB}(8,8,1)$, are all best possible: explicit periodic bipartite plane graphs of girth at least $8$ achieve every slope. Furthermore, an explicit $255$-vertex, $319$-edge bipartite periodic plane graph of girth $8$ (`dual_Dstar.json`) satisfies $\mathrm{NSB}(15)$, exceeds density $5/4$ ($4 \cdot 319 = 1276 > 1275 = 5 \cdot 255$), and contains $\Theta(1,7,9)$ as its unique connected bicyclic subgraph on at most $17$ edges; thus excluding $\Theta(1,7,9)$ is strictly necessary to reach $5/4$ from $\mathrm{NSB}(15)$. Because every sharp witness has girth at least $8$, adding any exclusion involving $6$-cycles (even forbidding all $6$-cycles) cannot lower any of these slopes.
4. **Theorem 4 (Unbounded plane musquash exclusion).** In a plane thrackle drawing of a finite simple graph, no distinct cycle of length at most $7$ shares a vertex with a standard odd musquash of *any* order $n = 2h + 1$. Consequently, no $6$-cycle and no distinct $7$-cycle shares a vertex with any Woodall *distinct musquash* of any order. This extends Misereh–Nikolayevsky (2018), who excluded $3$- and $5$-cycles, to all cycles of length at most $7$.

---

## 1. Discharging Proof of $m \le \lfloor 5(n - 1)/4 \rfloor$

We use the established embedding theorem for thrackleable graphs (Lovász–Pach–Szegedy, 1997; Cairns–Nikolayevsky, 2009; Fulek–Pach, 2019; recalled as Theorem 2 in [SOURCE.tex](SOURCE.tex)):

- Every thrackleable graph contains no $4$-cycle.
- Every connected bipartite thrackleable graph admits a crossing-free embedding in the sphere $S^2$ ($\chi = 2$).
- Every connected non-bipartite thrackleable graph admits a crossing-free *parity embedding* in the projective plane $\mathbb{RP}^2$ ($\chi = 1$), in which every even cycle is two-sided and every odd cycle is one-sided, so every facial boundary walk has even length.

### Reduction to a connected minimum-degree-two core

Fix $\alpha \ge 1$ and define $T_\alpha(n) = \max\bigl(n, \alpha(n - 1)\bigr)$. Adding a leaf increases $T_\alpha(n)$ by at least $1$, and $T_\alpha$ is superadditive: $T_\alpha(n_1) + T_\alpha(n_2) \le T_\alpha(n_1 + n_2)$ for all $n_1, n_2 \ge 1$. By strong induction on $n$ (formalized as `ConwayThrackle.Reduction.forest_reduction`), to prove $m \le T_\alpha(n)$ for all thrackleable graphs it suffices to prove $m \le \alpha(n - 1)$ for every connected thrackleable graph $G$ with minimum degree at least $2$ and $m > n$.

Such a graph $G$ is connected and not a cycle, so its sphere or parity $\mathbb{RP}^2$ embedding is a $2$-cell embedding with Euler characteristic $\chi = n - m + f \ge 1$ in which every face $F$ has even boundary length $D(F) \ge 6$ (counted with multiplicity, allowing non-simple donor walks).

### Elementary thread discharging for $\alpha = 5/4$ (Tier `E2b`)

Assume $\mathrm{NSB}(15)$ — every connected subgraph on at most $15$ vertices has at most as many edges as vertices — together with no $\Theta(1,7,9)$ subgraph and no $\mathrm{DB}(8,8,1)$ subgraph. Set $B = 17$; then every connected subgraph with cycle rank at least $2$ has at least $17$ edges (otherwise shrinking to a minimal bicyclic subgraph would yield a connected subgraph with $m' > n'$ and $n' \le 15$).

Every face $F$ with $D(F) \le 16$ is bounded by a **simple cycle**: its non-backtracking boundary support has minimum degree at least $2$, so if it were not a cycle it would have cycle rank at least $2$ on at most $D(F) - 1 \le 15$ vertices, contradicting $\mathrm{NSB}(15)$; and it cannot traverse a cycle twice since $G$ is connected and not a cycle. Likewise, no two distinct faces of lengths $s, t \in \{6, 8\}$ can share an edge, because their union would have cycle rank at least $2$ and at most $s + t - 1 \le 15 < 17$ edges.

Call faces of length $6$ or $8$ *recipients* and faces of even length $D \ge 10$ *donors*. Along a donor boundary walk, maximal contiguous runs of edges opposite the same recipient are *threads* (their internal vertices have degree $2$ because the recipient is a simple cycle). Assign each face $F$ an initial scaled charge of $12\,D(F)$, and apply one transfer rule:

- Across each maximal thread of length $r$ shared between a donor face and a $6$-face, transfer $8r$ from the donor to the $6$-face.
- Across each maximal thread of length $r$ shared between a donor face and an $8$-face, transfer $3r$ from the donor to the $8$-face.

**Recipient final charge.** Because recipients never share an edge with each other, every edge of a $6$-face is opposite a donor, so its final charge is $12 \cdot 6 + 8 \cdot 6 = 120$. Every edge of an $8$-face is opposite a donor, so its final charge is $12 \cdot 8 + 3 \cdot 8 = 120$.

**Donor final charge.** Let $F$ be a donor of even length $D \ge 10$ with $u$ threads to $6$-faces of total length $x$ and $v$ threads to $8$-faces of total length $y$ (so $u \le x$, $v \le y$, and $x + y \le D$).

1. *Incidence caps.* A $6$-face sharing $r$ edges with $F$ forms a union of cycle rank at least $2$ with at most $D + 6 - r$ edges, so $D + 6 - r \ge 17$, giving $r \le \min(6, D - 11)$ and hence $x \le \min(6, D - 11)\,u$. Similarly, an $8$-face shares at most $\min(8, D - 9)$ edges with $F$. When $D = 10$, both $F$ and any adjacent $8$-face are simple cycles; if they shared an edge ($r = 1$), their union would have $17$ edges and would either contain a subgraph of cycle rank at least $2$ on at most $15$ vertices (if they shared any further vertex or edge) or equal $\Theta(1,7,9)$. Both are excluded, so $y = 0$ when $D = 10$ (and $x = 0$ since $D - 11 < 0$). Thus $y \le 0$ for $D = 10$ and $y \le \min(8, D - 9)\,v$ for $D \ge 12$.
2. *Gap bounds.* Consider an unmarked boundary gap of length $g \ge 0$ between two consecutive recipient threads of sizes $s, t \in \{6, 8\}$ on $F$. If they belong to the same recipient face, leaving and re-entering that simple cycle yields a subgraph of cycle rank at least $2$ with at most $s + g$ edges, so $g \ge 17 - s \ge 17 - s - t$. If they belong to distinct recipients, the union of the two cycles and the gap walk has cycle rank at least $2$ and at most $s + t + g$ edges, so $g \ge 17 - s - t$. Hence $g_{6,6} \ge 5$, $g_{6,8} \ge 3$, and $g_{8,8} \ge 1$. Moreover, if $s = t = 8$ and $g = 1$, the two $8$-faces must be distinct (as $8 + 1 < 17$) and vertex-disjoint (otherwise their union has cycle rank at least $2$ on at most $15$ vertices), so together with the gap edge they form $\mathrm{DB}(8,8,1)$, excluded by hypothesis. Therefore $g_{8,8} \ge 2$.
3. *Linear gap inequalities.* Every transition $(s, t) \in \{6, 8\}^2$ satisfies both $g(s, t) \ge \frac{1}{2}(w_1(s) + w_1(t))$ with $(w_1(6), w_1(8)) = (5, 1)$ (giving $5, 3, 1 \le 5, 3, 2$) and $g(s, t) \ge \frac{1}{2}(w_2(s) + w_2(t))$ with $(w_2(6), w_2(8)) = (4, 2)$ (giving $4, 3, 2 \le 5, 3, 2$). Summing around the cyclic boundary of $F$ gives
   $$5u + v \le D - x - y \qquad\text{and}\qquad 4u + 2v \le D - x - y.$$
4. *Final charge check.* We require $12D - 8x - 3y \ge 120$. For $D \ge 30$, since $8x + 3y \le 8(x + y) \le 8D$, we immediately have $12D - 8x - 3y \ge 4D \ge 120$. For $D = 10$, $x = y = 0$ gives $120$. For each even $D \in \{12, 14, \dots, 28\}$, the integer linear constraints above directly imply $8x + 3y \le 12D - 120$ (checked mechanically by `budgetEb` in Lean and by cyclic DP in `verify.py`).

**Euler conclusion.** Every face finishes with charge at least $120$. Because total charge is conserved,
$$120 f \le \sum_{F} 12\,D(F) = 24 m \implies 5 f \le m.$$
Substituting into Euler's formula $n - m + f = \chi \ge 1$ yields
$$5(n - m + f) = 5\chi \ge 5 \implies 4m \le 5n - 5\chi \le 5(n - 1).$$
For $n \ge 5$, $\frac{5}{4}(n - 1) \ge n$, giving $m \le \lfloor \frac{5}{4}(n - 1) \rfloor$.

### Complete conditional discharging ladder

All intermediate tiers between Pammer's $N = 12$ bound ($4/3$) and the $N = 16$ wall ($5/4$) are also proved and matched by sharp bipartite plane witnesses (tiers `A`–`D` use all-integer curvature/corner charging $SD + H(k - 6)$ with high-valence endpoint rebates, and tier `C4`/`D` adds $10$-face virtual thread reimbursement $\lfloor (r - 1)/3 \rfloor$):

| Tier | Finite exclusions (beyond embedding + no $C_4$) | Mean $\delta$ | Curvature $h$ | Slope $\alpha$ | Sharp planar witness |
|:---|:---|---:|---:|---:|:---|
| Simon / Tomar | $\mathrm{NSB}(12)$ | $8$ | $0$ | $4/3 \approx 1.3333$ | Simon girth-8 grid |
| `A` | $\mathrm{NSB}(13)$ | $42/5$ | $1/5$ | $21/16 = 1.3125$ | `A` ($576$ v, $756$ e) |
| `B` | $\mathrm{NSB}(14)$ | $9$ | $1/6$ | $9/7 \approx 1.2857$ | `B` ($504$ v, $648$ e) |
| `C3` | $\mathrm{NSB}(14)$ + $\Theta(2,6,8), \Theta(2,4,10), \mathrm{DB}(8,8,0)$ | $19/2$ | $1/12$ | $19/15 \approx 1.2667$ | `C` ($2736$ v, $3465$ e) |
| `C4` / `D` | $\mathrm{NSB}(14)$ + 4 graphs on $15$ v, or $\mathrm{NSB}(15)$ | $124/13$ | $2/13$ | $62/49 \approx 1.2653$ | `D` ($2352$ v, $2976$ e) |
| `E2` | $\mathrm{NSB}(15)$ + $\Theta(1,7,9), \Theta(3,5,9)$ | $10$ | $0$ | $5/4 = 1.2500$ | `F` ($576$ v, $720$ e) |
| **`E2b`** | **$\mathrm{NSB}(15)$ + $\Theta(1,7,9), \mathrm{DB}(8,8,1)$** | **$10$** | **$0$** | **$5/4 = 1.2500$** | **`F` ($576$ v, $720$ e)** |
| `F` | $\mathrm{NSB}(16)$ | $10$ | $0$ | $5/4 = 1.2500$ | `F` ($576$ v, $720$ e) |

Exhaustive subset search in `verify.py` confirms that within this discharging framework, the four $15$-vertex graphs of tier `C4` — namely $\mathrm{DB}(8,8,0)$, $\Theta(2,4,10)$, $\Theta(2,6,8)$, and $\Theta(4,6,6)$ — form the unique minimum-cardinality set upgrading $\mathrm{NSB}(14)$ to $62/49$, and `E2` and `E2b` are the only two minimum-cardinality pairs upgrading $\mathrm{NSB}(15)$ to $5/4$.

---

## 2. Sharpness Witnesses and Necessity of $\Theta(1,7,9)$

To prove Theorem 3, `verify.py` constructs finite periodic quotients of planar tilings (whose universal covers are infinite bipartite plane graphs, and whose large toroidal patches give finite bipartite plane graphs approaching the stated slope arbitrarily closely):

- **Witness `A` ($21/16$):** $K = 12$ subdivided dual of an augmented triangular grid ($576$ vertices, $756$ edges, bipartite, girth $8$, minimum connected bicycle has $15$ edges, so $\mathrm{NSB}(13)$ holds).
- **Witness `B` ($9/7$):** $K = 12$ parity-split subdivided square grid ($504$ vertices, $648$ edges, bipartite, girth $8$, minimum connected bicycle has $16$ edges, so $\mathrm{NSB}(14)$ holds).
- **Witness `C` ($19/15$):** Truncated doubled-horizontal triangular grid ($2736$ vertices, $3465$ edges, bipartite, girth $8$, $\mathrm{NSB}(14)$ plus `C3` exclusions hold).
- **Witness `Cprior` ($14/11$):** Checkerboard-expanded subdivided square grid ($792$ vertices, $1008$ edges, bipartite, girth $8$, minimum connected bicycle has $16$ edges, so $\mathrm{NSB}(14)$ holds; serves as an intermediate benchmark witness between `B` and `C`).
- **Witness `D` ($62/49$):** Truncated subdivided triangular lattice ($2352$ vertices, $2976$ edges, bipartite, girth $8$, minimum connected bicycle has $17$ edges, so $\mathrm{NSB}(15)$ holds).
- **Witness `F` ($5/4$):** Subdivided triangular-grid dual with weight-1 diagonals and weight-2 non-diagonals ($576$ vertices, $720$ edges, bipartite, girth $8$, minimum connected bicycle has $18$ edges, so $\mathrm{NSB}(16)$ holds).
- **Necessity witness `dual_Dstar.json` ($319/255 > 5/4$):** Obtained from an $8 \times 8$ toroidal triangulation by explicit Pachner edge flips and heavy-edge subdivisions (`dual_Dstar.json`). Its dual expansion has $n = 255$ vertices, $m = 319$ edges ($4m = 1276 > 1275 = 5n$), is bipartite of girth $8$, satisfies $\mathrm{NSB}(15)$, and has $\Theta(1,7,9)$ as its **only** connected bicyclic subgraph on at most $17$ edges. Hence, within this $S^2$ and $\mathbb{RP}^2$ embedding-and-discharging framework, no argument using $\mathrm{NSB}(15)$ alone — or even $\mathrm{NSB}(15)$ plus every other $16$-vertex bicyclic exclusion — can achieve slope $5/4$ without excluding $\Theta(1,7,9)$.

Because every witness above has girth at least $8$, it contains no $6$-cycles at all; therefore adding any exclusion mentioning a $6$-cycle leaves all five sharp slopes unchanged.

---

## 3. Complete Minimal-Bicyclic Exclusions ($n \le 15$ and Targeted $n = 16$)

To prove $\mathrm{NSB}(15)$ (Theorem 1), note that any connected graph with $m > n$ contains a minimal connected subgraph with $m' = n' + 1$ and minimum degree at least $2$. Since $\sum_v \deg(v) = 2n' + 2$, every such simple graph belongs to one of two families:

- **Dumbbells / figure-eights $\mathrm{DB}(j, k, \ell)$:** two cycles of lengths $3 \le j \le k$ joined by a path of length $\ell = n' + 1 - j - k \ge 0$ ($\ell = 0$ is a single shared vertex of degree $4$; $\ell \ge 1$ has two vertices of degree $3$).
- **Theta graphs $\Theta(a, b, c)$:** two vertices of degree $3$ joined by three internally disjoint paths of lengths $1 \le a \le b \le c$ with $b \ge 2$ (for simplicity) and $a + b + c = n' + 1$.

Together with Pammer's $n \le 12$ theorem (2014; independently re-verified by Simon, 2026), establishing $\mathrm{NSB}(15)$ requires ruling out every graph in these two families for $n \in \{13, 14, 15\}$:

| Order $n$ | Minimal bicyclic graphs ($m = n + 1$) | Certified UNSAT | Audited CNF & strict-RUP LRAT |
|---:|---:|---:|---:|
| $13$ | $40$ | $40 / 40$ | $40 / 40$ ($0$ RAT lemmas in core) |
| $14$ | $48$ | $48 / 48$ | $48 / 48$ ($0$ RAT lemmas in core) |
| $15$ | $56$ | $56 / 56$ | $56 / 56$ ($0$ RAT lemmas in core) |
| $16$ (`E2b`, `E2`, bonus) | `db_8_8_1`, `th_1_7_9`, `th_3_5_9`, `th_1_5_11` | $4 / 4$ | $4 / 4$ ($0$ RAT lemmas in core) |

Every $C_4$-containing minimal bicyclic graph on $n \in \{13, 14, 15\}$ vertices is included directly in the $40 + 48 + 56 = 144$ certified UNSAT cases rather than omitted.

### Encoding and independent verification pipeline

Each graph $G$ is encoded into a propositional CNF over the exact combinatorial rotation-system variables of a plane thrackle drawing (crossing orders along each edge and crossing signs for every disjoint edge pair, extending Simon's formulation with exact local subdrawing / $K_4$ genus-obstruction cuts and audited symmetry breaking):

1. **CEGAR & cube-and-conquer search:** Incremental CaDiCaL search iteratively separates any candidate orientation map with positive genus via minimal local edge-subset obstructions recorded in `witness.tsv`, terminating with `formula.cnf` and $0$ plane models.
2. **Independent semantic CNF audit:** Every clause in `formula.cnf` is verified from scratch against `graph.json` and `witness.tsv` (checking crossing-order transitivity, path/quartet/cycle tables independently regenerated from an orientable-map Euler checker, and every local genus obstruction).
3. **Cold UNSAT replay & strict-RUP certification:** `formula.cnf` is solved cold from scratch by CaDiCaL to emit a binary DRAT proof (`proof.bdrat`), trimmed and verified by `drat-trim` into textual LRAT (`proof.lrat`) with **zero RAT lemmas in the core**, and independently checked by a strict-RUP LRAT verifier.
4. **Controls:** Positive genus-0 thrackle models are verified for `cy_6`, `cy_7`, `cy_8`, and `pend_7_0_2`, and negative control mutations are rejected.

Because the raw `.bdrat` and `.lrat` proof files total several gigabytes, `sat_manifest.json` stores the complete machine-readable ledger of all $144$ cases for $n \in \{13, 14, 15\}$ plus the four certified $n = 16$ targets (`db_8_8_1`, `th_1_7_9`, `th_3_5_9`, and `th_1_5_11`, certifying both minimal $5/4$ pairs `E2b` and `E2`) and the audited path catalogues `pa_6` and `pa_7`, including exact edge lists, variable/clause/cut counts, core lemma counts, `0` RAT-lemma status, and SHA-256 digests of every `formula.cnf`, `witness.tsv`, `proof.bdrat`, and `proof.lrat`.

---

## 4. Unbounded Exclusion of Cycles of Length $\le 7$ Meeting a Standard Odd Musquash

An odd cycle $C_n$ ($n = 2h + 1$) drawn in the plane as a regular star polygon $\{n/h\}$ (up to ambient isotopy on $S^2$, with the all-vertices face unbounded) is called a *standard odd musquash*. Orient $C_n$ positively and label each complementary face by its integer winding number $w \in \{0, 1, \dots, h\}$ (with $w = 0$ on the unbounded face).

### Removal triangles and winding counts

Following Misereh–Nikolayevsky (AJCo 70, 2018, Lemmas 2.1–2.4 and Eq. (3.3)):

- Any edge disjoint from the star crosses every star edge once, so its endpoints have winding numbers differing by $1$. An edge attached at a star vertex leaves through either the outer (level 0) or inner (level 1) local sector; an outer start ends at level $1$ and an inner start ends at level $0$, and a second attached edge from an outer start returns to level $0$.
- For any three consecutive star edges $e_{i-1}, e_i, e_{i+1}$, the crossing of $e_{i-1}$ and $e_{i+1}$ together with the middle edge $e_i$ bounds a *removal triangle* $\Delta_i$. If both endpoints of $e_i$ have degree $2$ and the interior of $\Delta_i$ contains no graph vertex, splicing $e_{i-1}$ and $e_{i+1}$ at their crossing shortens the standard $n$-star to a standard $(n - 2)$-star while preserving all remaining edges, all winding numbers outside $\Delta_i$, and simplicity (provided no chord would become parallel to the spliced edge; such a chord would already form a forbidden $C_4$ with the $3$-edge star arc).
- Summing the $n$ positively oriented boundaries $\partial \Delta_i$ gives twice the oriented star plus the innermost convex $n$-gon. Therefore any point at winding level $j < h$ lies in the interior of **precisely $2j$** removal triangles.

### Three-step winding confinement

> **Lemma.** Let $v - x - y - z$ be a $3$-edge path attached to a standard odd $n$-musquash at a single vertex $v$ (with $x, y, z$ off the star). Then the winding levels of $(x, y, z)$ are $(1, 0, 1)$ for an outer start and $(0, 1, 0)$ for an inner start.

**Proof.** The outer-start case is Misereh–Nikolayevsky (Lemmas 2.1–2.2). For an inner start, $w(x) = 0$ and $w(y) = 1$, so it suffices to exclude $w(z) = 2$. Take a minimal odd $n$ admitting an inner-start $(0, 1, 2)$ path. If $n \ge 9$, then $h \ge 4 > 2$, so at most $2$ star edges are incident to $v$ and at most $0 + 2 + 4 = 6$ removal triangles contain $x$, $y$, or $z$, leaving at least $n - 8 \ge 1$ unblocked removal triangle whose removal yields a smaller counterexample. For $n = 3$ there is no level-2 face. For the two residual cases $n \in \{5, 7\}$, exact exhaustive dual-walk enumeration in `verify.py` (constructing the regular stars by rational segment intersections, keeping all genus-0 single-edge and two-edge signed maps, and enumerating **all** raw third-edge dual walks crossing every non-incident edge once, even allowing self-intersections) proves that **zero** raw third-edge walks end at level $2$:

| Standard star $n$ | Inner-start 1-edge plane maps | 2-edge plane maps | Raw 3rd-edge dual walks at level $0$ | Raw 3rd-edge walks at level $\ne 0$ |
|---:|---:|---:|---:|---:|
| $5$ | $2$ | $44$ | $1{,}296$ | $0$ |
| $7$ | $8$ | $610$ | $75{,}028$ | $0$ |

Hence no inner-start $(0, 1, 2)$ excursion exists for any odd $n$. $\square$

### Proof of Theorem 4

Let $C$ be a cycle of length $\ell \in \{3, 5, 6, 7\}$ distinct from a standard odd $n$-musquash $M$ and sharing at least one vertex with $M$. (For $\ell \in \{3, 5\}$ this is already Misereh–Nikolayevsky, 2018; $C_4$ is forbidden.)

- **Case 1: $C$ and $M$ share a single vertex $v$.** Every one of the $\ell - 1 \le 6$ off-star vertices of $C$ lies within distance $3$ of $v$ along $C$. By the three-step confinement lemma, all of them have winding levels in $\{0, 1\}$. Because consecutive off-star vertices are joined by edges disjoint from $M$, their winding levels alternate, so at most $\lceil (\ell - 1)/2 \rceil \le 3$ off-star vertices have level $1$. For $n \ge 9$, at most $2 + 2 \cdot 3 = 8$ star edges are blocked (two incident to $v$, at most two per level-1 vertex). Repeatedly removing unblocked triangles reduces to $n \le 7$, giving a thrackleable bicyclic graph on $n + (\ell - 1) \le 7 + 6 = 13$ vertices (at most $12$ for $C_6$, contradicting Pammer's theorem; at most $13$ for $C_7$, contradicting $\mathrm{NSB}(13)$ from Theorem 1, specifically `db_7_7_0`).
- **Case 2: $C$ and $M$ share at least two vertices.** Because $C \ne M$ is a simple cycle not contained in $M$, $C$ contains an ear $P$ of length $t \in \{1, \dots, \ell - 1\}$ with distinct endpoints $u, v \in V(M)$ and $t - 1 \le 5$ internal vertices off $M$. Every internal vertex of $P$ lies at distance at most $\lfloor t/2 \rfloor \le 3$ from $\{u, v\}$ along $P$, so by three-step confinement all internal vertices have levels in $\{0, 1\}$, alternating along $P$.
  - For $C_6$ ($t \le 5$, at most $4$ internal vertices), at most $2$ internal vertices have level $1$, blocking at most $4 + 2 \cdot 2 = 8$ star edges. Every $n \ge 9$ shortens to $n \le 7$, leaving a bicyclic graph on at most $7 + 4 = 11$ vertices (contradicting Pammer's theorem).
  - For $C_7$ ($t \le 6$, at most $5$ internal vertices), at most $3$ internal vertices have level $1$, blocking at most $4 + 2 \cdot 3 = 10$ star edges. Every $n \ge 11$ ($h \ge 5 > 1$) shortens to $n \le 9$, leaving a bicyclic graph on at most $9 + 5 = 14$ vertices (contradicting $\mathrm{NSB}(14)$ from Theorem 1).

Finally, by Cairns–King (2001), every odd Woodall distinct musquash is standard, and by Cairns–King (1999), the only even distinct musquash has length $6$ (whose union with a meeting $C_6$ or $C_7$ has at most $12$ vertices, excluded by Pammer). Thus no $6$-cycle and no distinct $7$-cycle shares a vertex with any distinct musquash. (Note: this theorem relies on the standard-star winding geometry and does not settle unrestricted pairs of even cycles $C_6 \cup_v C_{2k}$.)

---

## 5. Verification and Trust Boundary

Every component of the result has an explicit verification layer and clearly delineated trust boundary:

1. **Lean 4 kernel verification (`v4.35.0`):** [ConwayThrackleBound.lean](../../lean/Conjectures/ConwayThrackleBound.lean) proves the graph-level discharging and forest-reduction theorems `ConwayThrackle.ThreadA.bound_of_E2b` — giving $\alpha = 5/4$ from $\mathrm{NSB}(15)$, $\neg\Theta(1,7,9)$, and $\neg\mathrm{DB}(8,8,1)$ — together with `bound_of_NSB13` ($21/16$), `bound_of_NSB14` ($9/7$), `bound_of_C4` ($62/49$), `bound_of_NSB15` ($62/49$), `bound_of_E2` ($5/4$), and `bound_of_NSB16` ($5/4$), using only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (verified by `ProofAudit` and `leanchecker`).
   - *Explicit Lean scope boundary (paper-level steps not formalized in Lean):* Lean formalizes the combinatorial discharging, Euler accounting, incidence/gap arithmetic, and forest/separation reduction assuming `NoSmallBicyclic`, explicit subgraph exclusions (`¬hasTheta`, `¬hasOctBridge`), and a supplied `Presentation` carrying its `Local.rankContact` / `rankGap` subgraph certificates, `hasDetails` (the $\Theta(1,7,9)$ $10$-face case), and `hasBridgeTests` (the $\mathrm{DB}(8,8,1)$ gap-1 case). The following bridge steps are argued in Section 1 above rather than checked by Lean:
     - the classical topological theorems of Lovász–Pach–Szegedy (1997) / Cairns–Nikolayevsky (2009) producing a $2$-cell sphere or $\mathbb{RP}^2$ parity embedding from a plane thrackle drawing;
     - that facial boundary walks of length at most $16$ in a core of minimum degree at least $2$ are simple cycles;
     - the topological definition and extraction of threads and gaps along donor face boundaries;
     - constructing the `Presentation` rank-test, $\Theta(1,7,9)$, and $\mathrm{DB}(8,8,1)$ subgraph certificates from the embedded faces;
     - replaying the external SAT/LRAT refutations inside the Lean kernel.
2. **Exact zero-float Python verification (`verify.py`):** Running `python3 results/conway-thrackle/verify.py` (stdlib-only, zero floating-point arithmetic, completes in under 10 seconds) independently verifies:
   - all 12 discharging certificates and minimum-cardinality target sets (with raised-target mutation controls);
   - all 6 periodic bipartite plane sharpness witnesses (`A`, `B`, `C`, `Cprior`, `D`, `F`) and `dual_Dstar.json` (with deleted-edge, triangle, and subdivision mutation controls);
   - the exact rational $C_5$ and $C_7$ standard-musquash 3-step dual-walk enumerations (`{0: 1296}` and `{0: 75028}`), cross-checked against a second independent combinatorial dart-orbit plane checker (with crossing-sign mutation controls);
   - first-principles exhaustive rotation-system verification that $C_4$ admits $0$ plane thrackle models and $C_5$ admits $2$;
   - exact one-to-one minimal-bicyclic catalogue completeness for $n \in \{13, 14, 15\}$ ($40 + 48 + 56 = 144$ graphs) and $n = 16$ (`db_8_8_1`, `th_1_7_9`, `th_3_5_9`, `th_1_5_11`) plus the audited path catalogues `pa_6` and `pa_7` against `sat_manifest.json`, including graph-topology checks, $0$ RAT lemmas in core, audit/replay SHA-256 consistency, and corrupted-manifest mutation controls.
3. **External SAT / DRAT / strict-RUP proofs (`sat_manifest.json`):** The $144$ finite exclusions for $n \in \{13, 14, 15\}$ and targeted $n = 16$ exclusions rely on audited SAT formulations solved by CaDiCaL, verified by `drat-trim` (with $0$ RAT lemmas in the core), and checked by a strict-RUP LRAT checker, with exact SHA-256 provenance recorded in `sat_manifest.json`.

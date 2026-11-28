# Erdős Problem #86: Breaking Baber's 14-Year Hypercube $C_4$-Free Density Barrier, Sharp Finite $Q_n$ Bounds, and Structural Obstructions

## 1. Problem Statement, Scope, and Prior-Art Attribution

Let $Q_n$ be the $n$-dimensional hypercube graph with vertex set $\{0,1\}^n$ and $n 2^{n-1}$ edges joining vertices that differ in one coordinate. Write

```math
\operatorname{ex}(Q_n, C_4) = \max\bigl\{ |E(G)| : G \subseteq Q_n,\; G \text{ is } C_4\text{-free} \bigr\}, \qquad
\pi_e(C_4) = \lim_{n \to \infty} \frac{\operatorname{ex}(Q_n, C_4)}{n 2^{n-1}}.
```

Erdős Problem #86 (Erdős 1984, 1990, 1991; see `SOURCE.tex`) asks whether $\pi_e(C_4) = \tfrac{1}{2}$, i.e., whether every $C_4$-free subgraph of $Q_n$ has at most $(\tfrac{1}{2} + o(1)) n 2^{n-1}$ edges.

**Scope of this result.** The full conjecture $\pi_e(C_4) = \tfrac{1}{2}$ remains open. This entry establishes a sharp quantitative and structural advance across four independently verified components:

1. **New asymptotic upper bound shattering Baber's 14-year record (`0.60318` to `0.59145`):**

```math
\pi_e(C_4) \le \frac{253{,}730{,}158{,}483{,}485{,}323}{429{,}000{,}000{,}000{,}000{,}000} = 0.5914455908705951585\ldots < 0.59145.
```

2. **Six new exact-rational finite $Q_n$ upper bounds strictly improving iterated $f(7)=304$ facet averaging** (including $\operatorname{ex}(Q_8, C_4) \le 684$ — within $2$ edges of the odd-square lower bound $682$ — and $\operatorname{ex}(Q_9, C_4) \le 1536$ — within $4$ edges of $g(9)=1532$).
3. **Exact primal SDP relaxation barriers** proving that pure full $Q_4$ flag algebra cannot improve $\operatorname{ex}(Q_8, C_4)$ below $692$, mathematically explaining why our coupled rooted $B_5$, finite-lattice-cut, and edge-book inventory hierarchy is required to reach $684$.
4. **Three structural obstruction theorems** against non-odd-square lower-bound escapes: the odd-dimension $3$-edge-defect theorem, the $3\times 3$-block Hamilton-fibre obstruction on $Q_9$, and the exact period $\le 16$ translation-invariant extremal theorem on $Q_7, Q_8, Q_9, Q_{10}$.

**Honest prior-art record (through November 2026).**

- *Asymptotic upper bounds:* Chung (1992) proved $\pi_e(C_4) \le 0.6228$; Thomason–Wagner (2009) improved this to $0.6226$; Balogh–Hu–Lidický–Liu (2012/2014) proved $0.6068$; Baber (2012, arXiv:1201.3587) proved $\pi_e(C_4) \le 0.603173074 < 0.60318$, which stood for 14 years.
- *Exact small values & odd-square lower bounds:* $\operatorname{ex}(Q_4, C_4) = 24$, $\operatorname{ex}(Q_5, C_4) = 56$ (Emamy-K.–Guan–Rivera-Vega 1992), $\operatorname{ex}(Q_6, C_4) = 132$ (Harborth–Nienborg 1994), and $\operatorname{ex}(Q_7, C_4) = 304$ (Zhou–Ma–Yang–Ren–Yang–Li, arXiv:2611.27284v1, Nov 20, 2026). Within the odd-square subclass $g(n)$ (equivalent to fully frustrated Ising hypercubes of Derrida–Pomeau–Toulouse–Vannimenus 1979 and Marinari–Parisi–Ritort 1995; see also Brass–Harborth–Nienborg 1995, Laplante–Naserasr–Sunny–Wang 2026, and Minamoto arXiv:2603.29127v5), Lujia Wang (arXiv:2611.14906v1, Nov 11, 2026) proved $g(9) = 1532$, $g(10) \ge 3328$, and the general asymptotic odd-square bound. We benchmark all finite $n$ upper bounds below against the sharpest prior baseline, namely iterated facet averaging $u_{k+1} = \lfloor \frac{2(k+1)}{k} u_k \rfloor$ starting from Zhou et al.'s $u_7 = \operatorname{ex}(Q_7, C_4) = 304$ (which is strictly sharper than one-step $Q_7$-averaging).

---

## 2. Summary of Main Results

### Theorem 1 & Theorem 2 (Exact-Rational Asymptotic and Finite $Q_n$ Upper Bounds)

All seven upper bounds below are established by the coupled full $Q_4$ + rooted $B_5$ + finite-lattice-cut + edge-book inventory dual framework (Sections 3–4), with theoretical soundness formalized in Lean 4 (`lean/Conjectures/Erdos86FlagAlgebra.lean`, 46 proved theorem declarations) and exact rational certificate replay verified zero-float in `results/erdos-86/verify.py` (Suite 1).

| Target | Known Lower Bound | Prior Upper Bound | New Exact-Rational Density Upper Bound | New Integer Edge Bound | Margin vs. Prior |
| --- | ---: | ---: | --- | ---: | --- |
| $\pi_e(C_4)$ | $\ge 0.5$ | $\le 0.603173074$ (Baber 2012) | $\dfrac{253{,}730{,}158{,}483{,}485{,}323}{429{,}000{,}000{,}000{,}000{,}000} \approx 0.5914455909$ | — | $-0.0117275$ |
| $\operatorname{ex}(Q_8, C_4)$ | $\ge 682$ | $\le 694$ (iterated $Q_7$) | $\dfrac{1{,}346{,}954{,}636{,}130{,}710{,}129}{2{,}016{,}000{,}000{,}000{,}000{,}000} \approx \dfrac{684.1674}{1024}$ | **$\le 684$** | $-10$ (gap to $682$: $2$) |
| $\operatorname{ex}(Q_9, C_4)$ | $\ge 1532$ | $\le 1561$ (iterated $Q_7$) | $\dfrac{1{,}075{,}255{,}913{,}169{,}191{,}273}{1{,}612{,}800{,}000{,}000{,}000{,}000} \approx \dfrac{1536.0799}{2304}$ | **$\le 1536$** | $-25$ (gap to $1532$: $4$) |
| $\operatorname{ex}(Q_{10}, C_4)$ | $\ge 3328$ | $\le 3468$ (iterated $Q_7$) | $\dfrac{7{,}960{,}674{,}831{,}095{,}286{,}151}{12{,}096{,}000{,}000{,}000{,}000{,}000} \approx \dfrac{3369.5978}{5120}$ | **$\le 3369$** | $-99$ |
| $\operatorname{ex}(Q_{11}, C_4)$ | — | $\le 7629$ (iterated $Q_7$) | $\dfrac{432{,}415{,}022{,}065{,}590{,}379}{660{,}000{,}000{,}000{,}000{,}000} \approx \dfrac{7379.8830}{11264}$ | **$\le 7379$** | $-250$ |
| $\operatorname{ex}(Q_{12}, C_4)$ | — | $\le 16645$ (iterated $Q_7$) | $\dfrac{5{,}179{,}649{,}375{,}710{,}126{,}039}{7{,}920{,}000{,}000{,}000{,}000{,}000} \approx \dfrac{16072.6090}{24576}$ | **$\le 16072$** | $-573$ |
| $\operatorname{ex}(Q_{16}, C_4)$ | $\ge 327680$ | $\le 355089$ (iterated $Q_7$) | $\dfrac{1{,}081{,}058{,}230{,}849{,}675{,}073}{1{,}680{,}000{,}000{,}000{,}000{,}000} \approx \dfrac{337372.5344}{524288}$ | **$\le 337372$** | $-17{,}717$ |

### Theorem 3 (Exact Primal Obstruction for the Pure Full $Q_4$ SDP Relaxation)

For $n \in \{8, 9, 10\}$, there exist explicit strictly-positive rational probability laws supported on $C_4$-free subgraphs of $Q_4$ (`data/floor8.json`, `data/floor9.json`, `data/floor10.json`; verified by exact rational Schur complements in `verify.py` Suite 2) whose finite $n$ full $Q_4$ moment matrices (over all vertex-, edge-, and square-rooted flag blocks) are positive semidefinite and attain exact edge-density objectives:

| $n$ | Support size in $H_4$ | Exact primal relaxation lower bound | Edge equivalent $q \cdot n 2^{n-1}$ | Consequence for pure full $Q_4$ SDP |
| --- | ---: | --- | ---: | --- |
| $8$ | $118$ | $\dfrac{235{,}127{,}287{,}245}{347{,}826{,}087{,}008}$ | $692.2147\ldots$ | **Cannot prove $\operatorname{ex}(Q_8, C_4) \le 691$** |
| $9$ | $117$ | $\dfrac{10{,}666{,}666{,}601{,}287}{16{,}000{,}000{,}007{,}312}$ | $1535.999989\ldots$ | Pure $Q_4$ cannot pass $1535$ |
| $10$ | $119$ | $\dfrac{10{,}515{,}188{,}745{,}587}{16{,}000{,}000{,}000{,}144}$ | $3364.8603\ldots$ | Pure $Q_4$ cannot pass $3364$ |

**Remark.** Theorem 3 is a lower bound on the pure full $Q_4$ SDP relaxation, not a graph lower bound on $\operatorname{ex}(Q_n, C_4)$. In particular, at $n=8$ it rigorously proves that our leap from $692$ down to $\operatorname{ex}(Q_8, C_4) \le 684$ is unattainable by pure full $Q_4$ flag algebra alone and genuinely relies on the higher-order $B_5$, finite-lattice-cut, and edge-book inventory couplings introduced below.

### Theorem 4 (Three Structural Obstructions Against Non-Odd-Square Escapes)

1. **Theorem 4a (Odd-Dimension Three-Edge-Defect Theorem; Lean 4: `Erdos86Obstructions.threeEdgeDefect`).** For every odd $n \ge 1$, if a $C_4$-free subgraph $H \subseteq Q_n$ satisfies $|E(H) \triangle E(G)| \le 3$ for some odd-square subgraph $G \subseteq Q_n$, then $|E(H)| \le g(n)$. In particular (using Wang's $g(9) = 1532$), any $C_4$-free subgraph of $Q_9$ with $\ge 1533$ edges has Hamming distance at least $4$ from the entire odd-square family.
2. **Theorem 4b ($3 \times 3$-Block Hamilton-Fibre Obstruction on $Q_9$; Lean 4: `Erdos86Obstructions.hamiltonFibreObstruction`).** Partition the $9$ coordinate directions of $Q_9$ into three blocks of size $3$. There is no $C_4$-free subgraph of $Q_9$ having degree $2$ in each of the three blocks at every vertex. Thus no fibrewise Hamilton-cycle construction (even with arbitrarily varying $8$-cycles across fibres) can realize $1536$ edges.
3. **Theorem 4c (Exact Period $\le 16$ Translation-Invariant Extremal Theorem; `verify.py` Suite 3).** Among all $C_4$-free subgraphs of $Q_n$ invariant under addition of a linear subspace $W \le \mathbb{F}_2^n$ of codimension at most $4$, the exact maximum edge counts are $296$ ($n=7$), $672$ ($n=8$), $1472$ ($n=9$), and $3200$ ($n=10$), strictly below the odd-square bounds $g(7)=304$, $g(8)=682$, $g(9)=1532$, and $g(10) \ge 3328$ in every case.

---

## 3. Coupled Full $Q_4$, Rooted $B_5$, Finite-Lattice, and Edge-Book Dual Theory

Write $d(G) = |E(G)| / (n 2^{n-1})$ for a spanning $C_4$-free subgraph $G \subseteq Q_n$. A random signed coordinate embedding chooses a uniform origin $v \in \{0,1\}^n$ and a uniform injection of local coordinate axes into $\{0,\dots,n-1\}$. Restricting a sampled subcube or rooted ball to any fixed coordinate subset preserves uniformity of the induced marginal (`Erdos86FlagAlgebra.subcube_averaging`, `Erdos86FlagAlgebra.Incidence.mean_nested_coordinates`).

### 3.1 Rooted Radius-Two Balls and $B_4 \leftrightarrow B_5$ Marginal Coupling

Let $H$ denote the colored (edge present/absent) $4$-cube $Q_4$, and let $B_d$ denote the radius-two ball centered at the origin in $Q_d$, retaining its $d$ spokes from the center to weight $1$ vertices and $d(d-1)$ edges from weight $1$ to weight $2$ vertices (omitting edges incident only to weight $\ge 3$). Let $p_4(H)$ be the empirical distribution on coordinate-permutation orbits of rooted $B_4$ balls averaged over all $16$ vertices of $H$, and let $p_5(B)$ be the empirical distribution on rooted $B_4$ orbits obtained by deleting one of the $5$ axes of a sampled $B = B_5$ uniformly at random. By uniform outer sampling (`Erdos86FlagAlgebra.ball₂_marginal`), for **every $n \ge 5$**,

```math
\mathbb{E}_H[p_4(H)] = \mathbb{E}_B[p_5(B)].
```

### 3.2 Finite $n$ and Asymptotic Positive Semidefinite Moment Inequalities

Fix a labelled root of dimension $s$ and independently sample two extensions **with replacement** from the remaining $n-s$ ambient coordinates. If $p$ denotes the conditional probability vector of one sampled flag given the root, then for any symmetric positive semidefinite matrix $S$, the conditional pair expectation satisfies $p^\top S p \ge 0$ (`Erdos86FlagAlgebra.Flags.rooted_sos_nonneg`).

**On $Q_4$, term $F^{(n)}(H)$.** We use three rooted families:

1. **Vertex root** ($s=0$): sample an unordered pair of fresh axes (flag = $Q_2$ square). Two independent unordered pairs from $n$ axes have overlap $0, 1, 2$ with exact probabilities

```math
\frac{(n-2)(n-3)}{n(n-1)}, \qquad \frac{4(n-2)}{n(n-1)}, \qquad \frac{2}{n(n-1)}.
```

2. **Edge root** ($s=1$, $2$ types): sample one fresh axis (flag = $Q_2$ square). Overlap $0, 1$ probabilities are $(n-2)/(n-1)$ and $1/(n-1)$.
3. **Square root** ($s=2$, $5$ $C_4$-free types): sample one fresh axis (flag = $Q_3$ cube). Overlap $0, 1$ probabilities are $(n-3)/(n-2)$ and $1/(n-2)$.

Conditioned on each overlap size, sampling the corresponding pair of embeddings inside a uniform $Q_4$ gives an exact unbiased estimator of the finite $n$ moment (`Erdos86FlagAlgebra.Flags.overlap_probability`, `overlap_step_one`, `overlap_step_two`). For repeated flags (overlap $= 2$ for $s=0$, overlap $= 1$ for $s=1,2$), the diagonal entry equals the average of the two diagonals over distinct-axis pairs because the marginals agree. The independent $Q_4$ replay enumerates $48, 96, 24$ zero-overlap events for the three families plus $192$ one-axis-overlap events for the vertex family. At $n = \infty$, collisions have total probability $O(1/n)$ for fixed bounded tables and are discarded, yielding an asymptotic bound on $\pi_e(C_4)$.

**On $B_5$, term $G^{(n)}(B)$.** Root at a vertex, single out an axis $i$, condition on whether the spoke in direction $i$ is present or absent ($2$ types), and sample an unordered pair $\{j,k\}$ of fresh axes to obtain a marked $B_3$ flag quotiented only by swapping $j \leftrightarrow k$ ($126$ absent-spoke flags and $99$ present-spoke flags). For two independent pairs from the $n-1$ axes other than $i$, the exact overlap probabilities for overlaps $0, 1, 2$ are

```math
\frac{(n-3)(n-4)}{(n-1)(n-2)}, \qquad \frac{4(n-3)}{(n-1)(n-2)}, \qquad \frac{2}{(n-1)(n-2)}.
```

Within a $5$-axis ball $B_5$, averaging over all $5$ choices of $i$ gives $15$ complementary pairs, $60$ one-axis-overlap pairs, and $30$ identical pairs (at $n=\infty$, only the $15$ complementary pairs are retained).

### 3.3 Finite Lattice Cuts (Exact Integrality Constraints at Finite $n$)

For a labelled $s$-root ($s \in \{1, 2\}$) and any integer-valued observable $a$ of its one-axis extension flag, the conditional sum $k = (n-s)\mathbb{E}[a \mid \text{root}]$ is an integer. For every integer $h$,

```math
4(k - h)(k - h - 1) = \bigl(2k - (2h+1)\bigr)^2 - 1 \ge 0.
```

Setting $U_i = 2(n-s) a_i - (2h+1)$, the symmetric pair table $M_{ij} = U_i U_j - 1$ satisfies $\mathbb{E}[M_{ij} \mid \text{root}] = 4(k-h)(k-h-1) \ge 0$ under independent sampling with replacement (`Erdos86FlagAlgebra.lattice_nonneg`, `extension_lattice_nonneg`, `split_extension_lattice_cut`), even though $M$ is not itself PSD. For the vertex root ($s=0$), taking $a_i$ to be the number of present root edges in the $2$-axis square flag gives $(n/2)\mathbb{E}[a \mid v] = \deg(v) \in \mathbb{Z}$, so $U_i = n a_i - (2h+1)$ yields the valid cut $4(\deg(v)-h)(\deg(v)-h-1) \ge 0$ (`Erdos86FlagAlgebra.vertex_lattice_nonneg`). Nonnegative integer combinations of these cuts, symmetrized over root automorphisms, are added directly into the finite $n$ flag tables (never used at $n=\infty$).

### 3.4 Four-Page and Three-Page Edge-Book Inventory Coupling

Fix a central directed edge $uv$ along direction $i$ with presence bit $t \in \{0,1\}$. Each other direction $j \ne i$ forms a *page* (a square containing $uv$), colored by the $3$-bit pattern $(u(u+e_j),\, v(v+e_j),\, (u+e_j)(v+e_j)) \in \{0,\dots,7\}$; by $C_4$-freeness, color $7$ is forbidden when $t=1$, leaving $8$ colors for $t=0$ and $7$ colors for $t=1$.

A $5$-ball $B_5$ determines all $4$ pages around each of its $5$ central directed edges. For any price function $w(t, T)$ on sorted $4$-page multisets $T$ (or induced from a $3$-page price $b(t, S)$ via $b^{(4)}(t, T)$ averaged over the $4$ one-page deletions, where the $B_5$ terms cancel algebraically with $B_4$ prices `Erdos86FlagAlgebra.Incidence.edgeBook_three_of_four_marginal`), add the mean of $w$ over the $5$ central edges to the $B_5$ score. To compensate, for any integer $D$ with $4 \le D \le n-1$ (or fixed $D \ge 4$ in the $n=\infty$ limit), sample $D$ ambient pages around $uv$ uniformly without replacement and record only their color multiset (the *inventory*, of which there are $\binom{D+7}{7} + \binom{D+6}{6}$ admissible states). Sampling $4$ pages from this $D$-page inventory without replacement has the exact hypergeometric marginal of a $B_5$ edge-book, and the unconditional distribution is invariant under reversing $uv$ (swapping bits $1$ and $2$ of every page). Subtracting the orientation-averaged hypergeometric expectation $h_w(\text{inv})$ of $w$ and taking its exact maximum over all inventories gives the coupled dual inequality:

```math
d(G) \;\le\; \max_{H \in \mathcal{H}_4}\bigl[\tfrac{e(H)}{32} + F^{(n)}(H) + p_4(H)\cdot \ell\bigr]
\;+\; \max_{B \in \mathcal{B}_5}\bigl[G^{(n)}(B) - p_5(B)\cdot \ell + \bar{w}(B)\bigr]
\;+\; \max_{\text{inv}}\bigl[-h_w(\text{inv})\bigr].
```

Taking expectations over a uniform random embedding of any $C_4$-free $G \subseteq Q_n$ cancels both $\ell$ and $w$, leaves $F^{(n)}$ and $G^{(n)}$ nonnegative (up to $O(1/n)$ at $n=\infty$), and averages $e(H)/32$ to $d(G)$. Crucially, **soundness does not depend on any SDP solver or convergence**: any integer-factored PSD blocks $(I + R^\top R)/s^2$, nonnegative lattice-cut multipliers, and rational prices $(\ell, w)$ yield a 100% rigorous upper bound once the three finite maxima are computed exactly over all orbits.

---

## 4. Exact Zero-Float Verification Architecture (`results/erdos-86/verify.py`)

Running `python3 results/erdos-86/verify.py` (standard library Python 3 + `g++ -std=c++17 -O3 -fopenmp`; ~18 seconds wall time; zero floats, zero NumPy/SciPy/SymPy, zero solvers) independently regenerates and checks everything from scratch:

1. **Independent on-the-fly orbit censuses:**
   - $Q_4$ (`H4`): regenerated by $Q_3$-facet decomposition, checked for strict sorting, $C_4$-freeness across all $24$ squares, canonical minimality under all $384$ cube isometries, and orbit-stabilizer sum $= 1{,}226{,}436{,}381$ matching the independent facet-pair independent-set count across all **$3{,}212{,}821$** orbits.
   - Rooted $B_4$ (`B4`): regenerated and verified to **$2{,}144$** orbits and **$46{,}553$** labelled balls (matching the closed-form spoke-pair count).
   - Rooted $B_5$ (`B5`): regenerated and verified to **$170{,}055$** orbits and **$19{,}571{,}625$** labelled balls.
2. **Untrusted-basis PSD reconstruction & overflow checks:** Every certificate in `data/cert_*.npz` stores integer Gram factors $R$ (so $I + R^\top R$ is PSD by construction without trusting any solver), lifted through integral congruence maps in `data/joint_bases.json.gz`. Every lifted table is checked explicitly for symmetry, invariance under all root automorphisms, and integer range bounds guaranteeing zero overflow in 128-bit exact integer accumulation.
3. **Exhaustive integer scans & mandatory mutation rejections:**
   - **Suite 1:** Scans all $3{,}212{,}821$ $H_4$ orbits, $170{,}055$ $B_5$ orbits, and all $\binom{D+7}{7}+\binom{D+6}{6}$ inventories for all $7$ targets ($n \in \{0,8,9,10,11,12,16\}$), asserts exact `Fraction` equality with the manifest, and verifies rejection of $8$ deliberate corruptions (raising the empty $B_4$ price on each of the $7$ certificates, plus perturbing a Gram factor on the asymptotic certificate).
   - **Suite 2:** Verifies `floor8.json`, `floor9.json`, `floor10.json` directly on raw labelled flags using exact `Fraction` symmetric Schur complements (including singular pivots), with no reliance on any canonical census or Schur basis, plus rejects two mutations (injecting a $C_4$ mask and a negative weight).
   - **Suite 3:** Replays the Period $\le 16$ proof (Section 5.3) and independently verifies all four lifted $Q_7, Q_8, Q_9, Q_{10}$ extremizers (`296, 672, 1472, 3200` edges), the square-defect identity, and rejection of a $C_4$-completing edge mutation in every dimension.

---

## 5. Proofs of the Structural Obstruction Theorems (Theorem 4)

### 5.1 Proof of Theorem 4a: Three-Edge-Defect Theorem (Odd $n$)

*Machine-checked in Lean 4 as `Erdos86Obstructions.threeEdgeDefect`.*

Let $n$ be odd, let $G \subseteq Q_n$ be odd-square, and suppose $H \subseteq Q_n$ is $C_4$-free with $|E(H) \triangle E(G)| \le 3$ and $|E(H)| > g(n)$. Set $d(v) = \deg_G(v)$, $h(v) = n - 2d(v)$, and $\delta = g(n) - |E(G)| \ge 0$. Switching all $n$ edges incident to a vertex $v$ changes the edge count of $G$ by $h(v)$ while preserving the parity of every square, hence $h(v) \le \delta$ for every $v$. Since $n$ is odd, every $h(v)$ is odd. Switching simultaneously at any subset of vertices on the same bipartition side sums their gains because their incident stars are edge-disjoint.

Write $a = |E(H) \setminus E(G)|$ and $r = |E(G) \setminus E(H)|$. Then $a + r \le 3$ and $\delta < a - r$. For any newly added edge $xy = \{x, x \oplus e_i\} \in E(H) \setminus E(G)$ and any direction $j \ne i$ retained in $G$ at both $x$ and $y$, the square on $\{x, y, x \oplus e_j, y \oplus e_j\}$ already has two edges along direction $j$ and is missing $xy$, so odd-squareness of $G$ forces the opposite $i$-edge $\{x \oplus e_j, y \oplus e_j\} \in E(G)$. Thus each common retained direction $j$ yields a $3$-edge path in $G$ that becomes a $C_4$ upon inserting $xy$; as $j$ varies, these $3$-edge sets are pairwise edge-disjoint, so $H$ must delete at least one edge from each.

- **Case $r \ge 1$.** Since $a + r \le 3$ and $a - r > \delta \ge 0$, the only possibility is $r = 1$, $a = 2$, $\delta = 0$. Then $h(v) \le 0$ and $h(v)$ odd forces $h(v) \le -1$, i.e., $d(v) \ge (n+1)/2$ for every $v$. For either added edge $xy$ (absent in $G$), the retained direction sets of $x$ and $y$ inside the $n-1$ directions other than $i$ each have size at least $(n+1)/2$, so they overlap in at least $2 \cdot \tfrac{n+1}{2} - (n-1) = 2$ directions. A single deletion ($r=1$) cannot hit two edge-disjoint forced triples, contradiction.
- **Case $r = 0$.** Then $a \in \{1,2,3\}$, $\delta \le a - 1 \le 2$, and every odd $h(v) \le \delta$ satisfies $h(v) \le 1$. Since no old edge is deleted, for every added edge $xy$ in direction $i$ the retained direction sets of $x$ and $y$ outside $\{i\}$ must be disjoint, giving $d(x) + d(y) \le n - 1$, equivalently $h(x) + h(y) \ge 2$. Together with $h \le 1$ this forces $h(x) = h(y) = 1$, so the retained direction sets of $x$ and $y$ partition the $n-1$ directions outside $\{i\}$. Now suppose two distinct added edges $e_1 = \{x, x \oplus e_i\}$ and $e_2 = \{x, x \oplus e_j\}$ met at $x$: neither $i$ nor $j$ is retained at $x$ in $G$, so the partition property across $e_1$ forces direction $j$ retained at $x \oplus e_i$, and across $e_2$ forces direction $i$ retained at $x \oplus e_j$. Then the square spanned by $\{i, j\}$ at $x$ has exactly $2$ edges in $G$, contradicting odd-squareness. Hence the $a$ added edges form a matching. Switching $G$ simultaneously at all $a$ endpoints of this matching on the even bipartition side preserves odd-squareness and increases $|E(G)|$ by $\sum h(v) = a > \delta$, contradicting the definition of $g(n)$. $\square$

### 5.2 Proof of Theorem 4b: $3 \times 3$-Block Hamilton-Fibre Obstruction on $Q_9$

*Machine-checked in Lean 4 as `Erdos86Obstructions.squareDefectIdentity` and `Erdos86Obstructions.hamiltonFibreObstruction`.*

Suppose $G \subseteq Q_9$ is $C_4$-free and at every vertex has degree $2$ in each of three prescribed coordinate blocks $B_1, B_2, B_3$ of size $3$. Then $\deg_G(x) = 6$ for all $x \in \{0,1\}^9$. Within each $3$-cube fibre of a block $B_r$, a $C_4$-free $2$-regular subgraph must be a single $8$-cycle, so its complement $D$ in the fibre is a perfect matching of $Q_3$. Any perfect matching of $Q_3$ uses each of the $3$ directions an even number of times (cutting perpendicular to an axis separates two odd-parity halves of $4$ vertices); using $4$ edges of one direction would leave two $4$-cycles, so the direction counts are $(2,2,0)$: two parallel edges in one layer and two parallel edges of a different direction in the opposite layer, creating **exactly $2$** internal squares with two opposite retained edges per $Q_3$-fibre ($3 \times 64 \times 2 = 384$ internal opposite-pair squares in total).

Let $M$ be the number of empty squares of $G$ and $A$ the number of squares with exactly two opposite retained edges. By the **square-defect identity** (`Erdos86Obstructions.squareDefectIdentity`, valid for every $C_4$-free $G \subseteq Q_n$),

```math
8(M - A) = \sum_{x \in \{0,1\}^n} (2\deg_G(x) - n)^2 - n 2^n.
```

At $n = 9$ with $\deg_G(x) \equiv 6$, the right-hand side is $512 \cdot 3^2 - 9 \cdot 512 = 0$, so $M = A \ge 384$. On the other hand, at every vertex $x$ there are exactly $3$ missing edges (one per block), hence $\binom{3}{2} = 3$ missing-edge corners at $x$; since every empty square consumes $4$ missing-edge corners, $M \le 3 \cdot 512 / 4 = 384$. Therefore equality holds everywhere: $M = A = 384$, **every** missing-edge corner completes to an all-missing square, and **no** mixed-block square has two opposite retained edges (equivalently two opposite missing edges).

Fix one $Q_3$-fibre $F$ of block $B_1$ and color each vertex $x \in F$ by the unique direction $c(x) \in B_2$ along which $x$'s incident $B_2$-edge is missing ($3$ colors). If $xy$ is a missing edge of $F$, then the missing $B_2$-edge at $x$ and $xy$ form a missing-edge corner, so all-missing corner completion forces the $B_2$-edge in direction $c(x)$ at $y$ to be missing as well, hence $c(x) = c(y)$. Conversely, if $xy$ is a retained edge of $F$ and $c(x) = c(y) = j \in B_2$, then the opposite $F$-edge $\{x \oplus e_j, y \oplus e_j\}$ cannot be missing (otherwise corner completion would force $xy$ missing), so that mixed-block square has two opposite retained edges, contradicting $A = 384$ internal squares. Contracting the $4$ missing matching edges of $F$ identifies pairs of equal-color vertices and maps the remaining $8$-cycle to a simple graph isomorphic to $K_4$ (each layer's two matching edges contract to $2$ adjacent vertices, and the $4$ transverse edges join all $4$ cross-layer pairs because the two layers' matchings use orthogonal directions). Thus $c$ induces a proper $3$-coloring of $K_4$, a contradiction. $\square$

### 5.3 Proof of Theorem 4c: Exact Period $\le 16$ Translation-Invariant Extrema

Shrinking $W \le \operatorname{GF}(2)^n$ if necessary to codimension exactly $4$, identify the quotient space $V = \operatorname{GF}(2)^n / W \cong \operatorname{GF}(2)^4$, let $c_i \in V$ be the image of the $i$-th basis vector, and encode direction $i$ by its endpoint mask $A_i \subseteq V$ (satisfying $A_i + c_i = A_i$, size $b_i = |A_i|$). The lifted edge count is $2^{n-5} \sum_{i=1}^n b_i$, and $C_4$-freeness on every pair $i \ne j$ is equivalent to

```math
\bigl(A_i \cap (A_i + c_j)\bigr) \cap \bigl(A_j \cap (A_j + c_i)\bigr) = \varnothing.
```

Any pair satisfies $b_i + b_j \le 24$, and any five directions satisfy $\sum_{r=1}^5 b_{i_r} \le 56$ by summing $\operatorname{ex}(Q_5, C_4) = 56$ over disjoint $Q_5$-faces (the sole imported finite bound). Moreover, any two zero-column directions ($c_i = c_j = 0$) must have disjoint masks $A_i \cap A_j = \varnothing$, so any collection of two or more zero-column directions contributes at most $|V| = 16$ to $\sum b_i$ in total. Exact integer enumeration (`verify.py` Suite 3) establishes that among nonzero column labels with $b_i \ge 10$, at most $8$ can coexist if one has $b_i \ge 12$, at most $7$ if two do, and at most $5$ if three do. Combining these with the zero-column constraints ($z + b_i/2 \le 16$; $z \le 8$ whenever $b_1 + b_2 = 24$; and impossibility of $z=11$ alongside nine $b_i = 10$ nonzero columns) rules out all signatures with $\sum b_i > T_n$ for $(T_7, T_8, T_9, T_{10}) = (74, 84, 92, 100)$, giving exact upper bounds $296, 672, 1472, 3200$. Explicit lifts from the $10$-direction sequence of `(column, 16-bit mask)` pairs `(1,16383), (2,62805), (4,61030), (8,59881), (14,59035), (11,55989), (7,56154), (13,54702), (0,27030), (0,38505)` attain equality for every $n \in \{7,8,9,10\}$ and are independently verified $C_4$-free in `verify.py` Suite 3. $\square$

---

## 6. Lean 4 Formalization Inventory

Two self-contained Lean 4 (`v4.35.0`) modules are included and verified via `lake build Conjectures ProofAudit` and `leanchecker` with zero `sorry`, zero custom axioms (`propext`, `Classical.choice`, `Quot.sound` only), and zero `native_decide`:

- **`lean/Conjectures/Erdos86FlagAlgebra.lean` (46 proved theorems):** Formalizes $Q_n$, $C_4$-freeness, $\operatorname{ex}(Q_n, C_4)$, subcube averaging (`subcube_averaging`, `exC4_facets`), monotone convergence of extremal density to $\pi_e(C_4)$ (`extremalDensity_succ`, `density_limit`), exact flag overlap probabilities and PSD moment soundness (`Flags.overlap_probability`, `Flags.overlap_step_one`, `Flags.overlap_step_two`, `Flags.rooted_sos_nonneg`), finite lattice cuts (`lattice_nonneg`, `extension_lattice_nonneg`, `split_extension_lattice_cut`, `vertex_lattice_nonneg`), and nested-coordinate / rooted $B_5$ / edge-book marginal coupling identities (`Incidence.mean_nested_coordinates`, `Incidence.edgeBook_three_of_four_marginal`, `ball₂_marginal`).
- **`lean/Conjectures/Erdos86Obstructions.lean` (34 proved theorems):** Formalizes the square-defect identity (`squareDefectIdentity`), the $3 \times 3$-block Hamilton-fibre obstruction on $Q_9$ (`hamiltonFibreObstruction`), and the odd-dimension $3$-edge-defect theorem (`threeEdgeDefect`).

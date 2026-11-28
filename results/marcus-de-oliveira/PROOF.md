# Structural Resolutions and Reductions for the Marcus–de Oliveira Determinantal Conjecture

## 1. Problem Statement and Honest Status

Let $n \ge 1$ and let $A, B \in M_n(\mathbb{C})$ be normal matrices with eigenvalue lists $a = (a_1, \dots, a_n)$ and $b = (b_1, \dots, b_n)$ counted with multiplicity. The **Marcus–de Oliveira Determinantal Conjecture** (Marcus 1973; de Oliveira 1982; see `SOURCE.tex`, Rodtes 2020) asserts that

$$
\det(A + B) \in \mathcal{P}(a, b) := \operatorname{conv}\!\left\{ z_\sigma := \prod_{i=1}^n (a_i + b_{\sigma(i)}) \;:\; \sigma \in S_n \right\}.
$$

Equivalently, fixing $A = \operatorname{diag}(a_1, \dots, a_n)$ and $B = \operatorname{diag}(b_1, \dots, b_n)$, the determinantal range

$$
\Delta_{U(n)}(a, b) := \left\{ \det(A + U B U^{\ast}) \;:\; U \in U(n) \right\} \subset \mathbb{C}
$$

is contained in the permutation polygon $\mathcal{P}(a, b)$. We write $(A, B) \in \mathrm{MOC}$ when this inclusion holds for all $U \in U(n)$ (or for a fixed pair $A, B$, as clear from context).

> **Honest status (🟢 Exact Compute + Audited; Lean 4 helpers).** The unrestricted Marcus–de Oliveira conjecture remains open for $n \ge 4$. Theorems A and B establish spectral sufficient conditions; Theorem C reduces the order-four problem to $SO(4)$; Theorems D–F treat specific determinant families, the collision-free singular boundary, and compound polytopes. Section 8 distinguishes the paper proofs from the exact computations and Lean theorems.

### Summary of Main Theorems and Prior-Art Baseline

| Result | Scope | Relationship to Prior Art | Verification Tier |
| :--- | :--- | :--- | :--- |
| **Theorem A** | Separate-circle one-outlier (all $n$); $n=4$ with $\ge 1$ concyclic spectrum (incl. Hermitian $A$ + arbitrary normal $B$); all $n$ Hermitian $A$ + $\le 4$ nonreal eigenvalues of $B$ | Extends Fiedler (1971), BKP (1994), Drury (2006, 2007) (two circles, $0$ outliers) and Shitov (2025) (Hermitian + $\le 3$ nonreal) | Audited paper proof + Lean 4 (`Matching`, `Arrowhead`, `MinorBridge`, `AllCompounds`, `Projective`, `Displacement`, `Stationary`, `Cut`) + `verify.py` §1 |
| **Theorem B** | All $n$ rank-excess $\le 2$ ($\operatorname{rank}(A-cI)+\operatorname{rank}(B+cI)\le n+2$, no concyclicity); $n=4$ Cross-Spectral Collision | Extends Kovačec (1994) (rank-2 / multiplicity $\ge n-2$) to all rank pairs $(p,q)$ with $p+q \le n+2$, closing $(4,4;6)$ | Audited paper proof + end-to-end Lean 4 for $n=4$ collision (`Collision`) + `verify.py` §2 |
| **Theorem C** | Universal $U(4) \to SO(4)$ simultaneous 70-minor real-chord reduction; $\operatorname{conv}\Delta_{U(4)}(a,b)=\operatorname{conv}\Delta_{SO(4)}(a,b)$ for every $4\times 4$ pair | New universal structural reduction for unrestricted $n = 4$ (eliminates complex conjugators without constraining either spectrum) | Audited paper proof + `verify.py` §3 |
| **Theorem D** | Continuous disjoint two-nonconcyclic $n=4$ two-tetrahedron family ($\lambda^3 \in \mathbb{R}$) over all $U(4)$; 48-vertex Shor and $P(\delta)$ failure; $\Pi_4$-escaped irreducible KKT saddles | Treats disjoint, collision-free, doubly nonconcyclic $n=4$ pairs over $U(4)$; compare Mulero-Martínez (2026) first-order analysis | Exact 151-SOS rational atlas (`two_tetrahedron_sos.json`) + `verify.py` §4 + Lean 4 (`Facet`) |
| **Theorem E** | All $n$ collision-free singular-boundary classification & inward transverse Hessian ($h(D''(0)) \ge 0$) | Extends Drury–Cload (1992) ($0 \in \Delta \implies 0 \in \mathcal{P}$) to full second-order geometry at supporting lines through $0$ | Audited paper proof + `verify.py` §5 |
| **Theorem F** | Exact 82-facet $\Pi_4$, sharp $O(4)=U(4)$ Orbit-2 breach $\gamma \approx -0.1348845$, $V_4$ Hadamard protection; Tao $6\times 6$ Hadamard 45-zero escape, $\ell_\infty$ distance $1/40$, and positive slices | Completes Drury (1992)'s $\Pi_4$ obstruction with exact facet H-rep, algebraic $\mathbb{Q}(\rho)$ optimum, and order-6 Hadamard escape geometry | Exact $\mathbb{Q}(\rho)$ SOS (`orbit2_u4_sos.json`) + `verify.py` §6–§7 + Lean 4 (`Facet`, `Hadamard`, `TaoForbidden`) |

Previously established baseline theorems (cited and not claimed as new): $n \le 3$ (Bebiano 1986; Bebiano–Merikoski–da Providência 1987); two generalized circles and Möbius reduction (Fiedler 1971; Bebiano–Kovačec–da Providência 1994; Drury 2006, 2007); zero determinant $0 \in \Delta \implies 0 \in \mathcal{P}$ (Drury–Cload 1992); $\Pi_4$ obstruction (Drury 1992); rank-2 / multiplicity $\ge n-2$ (Kovačec 1994); external vertices for $n=4$ (Drury 2004); Hermitian $A$ + $\le 3$ nonreal eigenvalues of $B$ and the lifting theorem $A(m,k) \implies A(n,k)$ for $n \ge m \ge k \ge 3$ (Shitov 2025, Izv. Math. 89, 862–869, Theorem 19).

---

## 2. Theorem A: Separate-Circle One-Outlier, Order-Four Concyclic, and All-Order Four-Outlier Theorems

### Statements

**Theorem A (Separate-Circle One-Outlier Theorem, All $n$).** Let $A, B \in M_n(\mathbb{C})$ be normal matrices. Suppose the spectrum $\sigma(A)$ lies on a generalized circle $C_1 \subset \widehat{\mathbb{C}}$ (a Euclidean circle or straight line), and all but at most one eigenvalue of $B$ (counted with multiplicity) lie on a possibly different generalized circle $C_2 \subset \widehat{\mathbb{C}}$. Then $(A, B) \in \mathrm{MOC}$.

**Corollary A1 ($n = 4$ Concyclic-by-Arbitrary-Normal).** For $n = 4$, if either $\sigma(A)$ or $\sigma(B)$ lies on a generalized circle — in particular, if $A$ is Hermitian and $B$ is an arbitrary $4 \times 4$ normal matrix — then $(A, B) \in \mathrm{MOC}$.

Proof of Corollary A1 from Theorem A. Any three points in $\mathbb{C}$ (including collinear or repeated points) lie on a generalized circle, so an arbitrary 4-point spectrum $\sigma(B)$ automatically has at most one outlier off a generalized circle. Moreover, at $n = 4$, the eigenbasis phase of the proof below admits a completely standalone finite integer-polynomial proof requiring zero external literature. $\square$

**Corollary A2 (All $n$ Four-Outlier Theorem).** Let $n \ge 4$. If $A \in M_n(\mathbb{C})$ is Hermitian and $B \in M_n(\mathbb{C})$ is normal with at most $4$ nonreal eigenvalues (counted with multiplicity), then $(A, B) \in \mathrm{MOC}$. More generally, $(A, B) \in \mathrm{MOC}$ whenever there is a **common** generalized circle $C \subset \widehat{\mathbb{C}}$ containing $\sigma(A)$ and all but at most $4$ elements of $-\sigma(B)$ (counted with multiplicity).

Scope precision: Unlike the one-outlier Theorem A (which permits two independent generalized circles $C_1, C_2$), the projective form of Corollary A2 requires a **common** generalized circle for $\sigma(A)$ and the non-outlier part of $-\sigma(B)$, because a Möbius map sending $C_1$ to $\mathbb{R}$ need not preserve a second independent circle $C_2$.

### Proof of Theorem A

**Step 1 (Projective $\mathrm{PGL}_2(\mathbb{C})$ reduction).** Let $f(z) = (pz+q)/(rz+s)$ with $ps - qr \ne 0$ be a fractional linear transformation whose pole $-s/r$ lies on $C_1$ outside the finite set $\sigma(A) \cup (-\sigma(B))$, mapping $C_1$ to $\widehat{\mathbb{R}}$. Transform the combined signed eigenvalue list $(a, -b)$ by $f$: set $a_i' = f(a_i) \in \mathbb{R}$ and $b_j' = -f(-b_j)$. For any unitary $U$, $\det(\operatorname{diag}(a) + U \operatorname{diag}(b) U^{\ast}) = \det(M) / \det(U)$ where $M_{ij} = (a_i + b_j) U_{ij}$. Under $(a, b) \mapsto (a', b')$,

$$
a_i' + b_j' = f(a_i) - f(-b_j) = \frac{(ps - qr)(a_i + b_j)}{(r a_i + s)(s - r b_j)}.
$$

Thus every entry of $M$ is scaled by row factor $(ps-qr)/(r a_i + s)$ and column factor $1/(s - r b_j)$, multiplying both $\det(A' + U B' U^{\ast})$ and every permutation product $z_\sigma'$ by the same nonzero complex constant $\prod_i (ps-qr)/(r a_i + s) \cdot \prod_j 1/(s - r b_j)$ (formalized for arbitrary $n$ in `MOCProjective.mobius`). Hence $(A, B) \in \mathrm{MOC} \iff (A', B') \in \mathrm{MOC}$, reducing to the case where $A$ is Hermitian and all but at most one eigenvalue of $B$ lie on a generalized circle $C$.

**Step 2 (Density perturbation).** Fix $B = \operatorname{diag}(b_1, \dots, b_n)$ with $b_2, \dots, b_n \in C$ and $b_1$ the possible outlier. If $b_1 \in C$, both spectra are concyclic and MOC holds by the two-circle theorem (Bebiano–Kovačec–da Providência 1994; Drury 2006, 2007). Otherwise $\operatorname{dist}(b_1, C) > 0$. By compactness of the finite simplex of convex weights, strict separation $\operatorname{Re}(\zeta \det(A + U B U^{\ast})) > \max_{\sigma \in S_n} \operatorname{Re}(\zeta z_\sigma)$ (for some $|\zeta| = 1$) is an open condition in $(a, b)$ with $U$ fixed. If $C$ is a horizontal line, rotate $C$ together with $b_2, \dots, b_n$ by an arbitrarily small angle while keeping $b_1 \notin C$. Now $C$ meets every horizontal line in at most two points. Perturb $b_2, \dots, b_n$ sequentially along $C$ within arbitrarily small neighborhoods so that all $y_j = \operatorname{Im}(b_j)$ ($j \ge 2$) are nonzero and pairwise distinct, and then perturb $b_1$ within $\frac{1}{2}\operatorname{dist}(b_1, C)$ so that $y_1 = \operatorname{Im}(b_1)$ is nonzero and distinct from $y_2, \dots, y_n$ (preserving $b_1 \notin C$). If the theorem holds for all such perturbed tuples, it holds at the original tuple by taking a convergent subsequence of convex weights.

**Step 3 (Support maximizer, nonsingularity, and first-order stationarity).** Suppose for contradiction that $(A, B) \notin \mathrm{MOC}$ for the perturbed data. Choose $|\zeta| = 1$ strictly separating $\Delta_{U(n)}(a, b)$ from $\mathcal{P}(a, b)$:

$$
c := \max_{U \in U(n)} \operatorname{Re}\!\left(\zeta \det(U A U^{\ast} + B)\right) > \max_{\sigma \in S_n} \operatorname{Re}(\zeta z_\sigma).
$$

If $c = 0$ and a maximizer $A_0 = U A U^{\ast}$ has $\det(A_0 + B) = 0$, then Drury–Cload (1992) places $0 \in \mathcal{P}(a, b)$, contradicting $0 = c > \max_\sigma \operatorname{Re}(\zeta z_\sigma)$. If $c = 0$ and $\det(A_0 + B) \ne 0$, rotating $\zeta$ slightly increases $\operatorname{Re}(\zeta \det(A_0 + B))$ strictly above $0$ while preserving strict separation; re-maximizing gives $c \ne 0$. Thus we may assume $c \ne 0$, so $H := A_0 + B$ is invertible.

Let $R := H^{-1}$, $s := \zeta \det(H)$ (with $\operatorname{Re}(s) = c \ne 0$), and define the Hermitian matrix

$$
D := \operatorname{Herm}(s R) = \frac{1}{2}(s R + \bar s R^{\ast}).
$$

For any Hermitian $G \in M_n(\mathbb{C})$, differentiating $\operatorname{Re}(\zeta \det(e^{itG} A_0 e^{-itG} + B))$ at $t = 0$ yields

$$
0 = \operatorname{Re}\!\left(\operatorname{tr}(s R \cdot i[G, A_0])\right) = \operatorname{tr}\!\left(D \cdot i[G, A_0]\right) = \operatorname{tr}\!\left(i[A_0, D] \, G\right).
$$

Since $i[A_0, D]$ is Hermitian and $G$ is arbitrary Hermitian, $[A_0, D] = 0$.

**Step 4 (Resolvent displacement identities and the star matrix $N$).** Since $A_0$ is Hermitian and $[A_0, D] = 0$, we have $H^{\ast} D H = H D H^{\ast}$ and both equal $\frac{1}{2}(s H^{\ast} + \bar s H)$ (verified at the matrix level in `MOCStationary.stationary_entries`). Setting $G := A_0 D$ and $E := A_0^2 D - c A_0$ with $c = \operatorname{Re}(s) = \frac{1}{2}(s + \bar s)$, expanding $H^{\ast} D H = \frac{1}{2}(s H^{\ast} + \bar s H)$ and $H D H^{\ast} = \frac{1}{2}(s H^{\ast} + \bar s H)$ using $H = A_0 + B$, $H^{\ast} = A_0 + B^{\ast}$, and $[A_0, D] = 0$ moves $c A_0$ to the left-hand side and leaves purely diagonal right-hand sides:

$$
E + G B + B^{\ast} G + B^{\ast} D B = \frac{1}{2}(s B^{\ast} + \bar s B),
$$

$$
E + B G + G B^{\ast} + B D B^{\ast} = \frac{1}{2}(s B^{\ast} + \bar s B).
$$

Since $B = \operatorname{diag}(b_j)$ with $b_j = x_j + i y_j$, subtracting the two identities at any off-diagonal entry $(j, k)$ ($j \ne k$) eliminates $E_{jk}$ and gives

$$
(b_k - \bar b_k - b_j + \bar b_j) G_{jk} + (\bar b_j b_k - b_j \bar b_k) D_{jk} = 0,
$$

which divides by $2i(y_k - y_j) \ne 0$ (from Step 2) to express $G_{jk}$ and then $E_{jk}$ as exact real-slope multiples of $D_{jk}$ (`MOCDisplacement.slopes`):

$$
D_{jk} = (d_j - d_k) K_{jk}, \qquad G_{jk} = (p_j - p_k) K_{jk}, \qquad E_{jk} = (q_j - q_k) K_{jk},
$$

where $K_{jk} := \frac{y_j y_k}{y_k - y_j} D_{jk}$ is skew-Hermitian ($K_{kj} = -\overline{K_{jk}}$), and the three real spectral potentials are

$$
d_j = \frac{1}{y_j}, \qquad p_j = -\frac{x_j}{y_j}, \qquad q_j = \frac{|b_j|^2}{y_j}.
$$

Because $b_2, \dots, b_n$ lie on a generalized circle $C : \alpha |z|^2 + \beta \operatorname{Re}(z) + \gamma \operatorname{Im}(z) + \delta = 0$ ($\alpha, \beta, \gamma, \delta \in \mathbb{R}$) while $b_1 \notin C$, the linear combination

$$
\phi_j := \alpha q_j - \beta p_j + \gamma + \delta d_j = \frac{\alpha |b_j|^2 + \beta x_j + \gamma y_j + \delta}{y_j}
$$

vanishes for every $j \ge 2$ and is nonzero at $j = 1$. Rescaling $(\alpha, \beta, \gamma, \delta)$ so that $\phi_1 = 1$, define the Hermitian matrix

$$
N := \alpha E - \beta G + \gamma I + \delta D.
$$

Because $A_0$ commutes with $D$, $N = (\alpha A_0^2 - \beta A_0 + \delta I) D - \alpha c A_0 + \gamma I$ commutes with $A_0$ (`MOCDisplacement.commuting_star`). Moreover, for every off-diagonal $(j, k)$,

$$
N_{jk} = (\phi_j - \phi_k) K_{jk},
$$

so $N_{jk} = 0$ whenever $j, k \ge 2$ ($j \ne k$)! Thus $N$ is a **Hermitian arrowhead (star) matrix** centered at index $1$, with real peripheral diagonal entries $h_j := N_{jj}$ ($j \ge 2$) and star couplings $N_{1j} = K_{1j}$.

**Step 5 (Active-set graph cut and block splitting).** Because $[A_0, D] = 0$, we also have $[D, N] = 0$. Let $\mathcal{A} := \{ j \ge 2 : K_{1j} \ne 0 \}$ be the set of active peripheral vertices, and $\mathcal{I} := \{2, \dots, n\} \setminus \mathcal{A}$ the inactive vertices. For any $j, k \ge 2$ ($j \ne k$), expanding $[D, N]_{jk} = 0$ gives

$$
(d_j - d_k)\!\left[(h_k - h_j) K_{jk} + K_{j1} K_{1k}\right] = 0.
$$

Since $y_j \ne y_k$, we have $d_j \ne d_k$, hence $(h_k - h_j) K_{jk} + K_{j1} K_{1k} = 0$.
1. For distinct $j, k \in \mathcal{A}$, $K_{j1} K_{1k} \ne 0$, so $h_j \ne h_k$ (all active peripheral poles are pairwise distinct) and $K_{jk} = K_{j1} K_{1k} / (h_j - h_k)$.
2. For $j \in \mathcal{A}$ and $r \in \mathcal{I}$, $K_{1r} = 0$ gives $(h_r - h_j) K_{jr} = 0$. Since the $h_j$ ($j \in \mathcal{A}$) are pairwise distinct, each $r \in \mathcal{I}$ can satisfy $K_{jr} \ne 0$ for at most one $j \in \mathcal{A}$. Then the $(1, r)$ entry of $[D, N] = 0$ reduces to $-(d_j - d_r) K_{1j} K_{jr} = 0$, forcing $K_{jr} = 0$ as well (since $d_j \ne d_r$ and $K_{1j} \ne 0$)!

Let $P$ be the diagonal coordinate projection onto $\{1\} \cup \mathcal{A}$. Since $K_{jr} = 0$ for all $j \in \{1\} \cup \mathcal{A}$ and $r \in \mathcal{I}$, every off-diagonal block of $D$, $G = A_0 D$, and $E = A_0^2 D - c A_0$ vanishes across the cut, giving $[P, D] = [P, A_0 D] = [P, A_0^2 D - c A_0] = 0$. Since $[A_0, D] = 0$, a purely algebraic calculation recovers $[P, A_0^2 D] = 0$:

$$
P (A_0^2 D) = P A_0 (D A_0) = (P A_0 D) A_0 = (A_0 D P) A_0 = A_0 (P D) A_0 = A_0 (P A_0 D) = (A_0^2 D) P.
$$

Subtracting $[P, A_0^2 D - c A_0] = 0$ gives $[P, c A_0] = 0$, and dividing by $c \ne 0$ yields $[P, A_0] = 0$ **without assuming $D$ is invertible** and without any pseudoinverse or spectral projection (formalized verbatim in `MOCCut.recover_cut`).

Thus $A_0$ and $B$ simultaneously split into block-diagonal form on $(\{1\} \cup \mathcal{A}) \oplus \mathcal{I}$. On $\mathcal{I}$, all eigenvalues of $B_{\mathcal{I}}$ lie on the single generalized circle $C$, so $(A_{0,\mathcal{I}}, B_{\mathcal{I}}) \in \mathrm{MOC}$ by the two-circle theorem. By multiplicativity of determinants and product probability weights (`SOURCE.tex`, Lemma 1), it remains only to prove $(A_{0,\text{act}}, B_{\text{act}}) \in \mathrm{MOC}$ (denoting the $\{1\} \cup \mathcal{A}$ active block by subscript $\text{act}$).

**Step 6 (Interlacing arrowhead eigenbasis and noncrossing matching law).** Let $m = 1 + |\mathcal{A}|$. If $m = 1$, the active block is $1 \times 1$ and trivial. For $m \ge 2$, rephase the peripheral coordinates by diagonal unitaries (which preserve $B$ and conjugate $A_0$ into a unitarily equivalent Hermitian matrix) so that every active coupling $\gamma_j := N_{1j} > 0$ ($j = 2, \dots, m$), and reorder $\mathcal{A}$ so that the distinct peripheral poles satisfy $h_2 < h_3 < \dots < h_m$. The characteristic polynomial of the Hermitian arrowhead $N_0 := N_{\{1\} \cup \mathcal{A}}$ is

$$
\det(\lambda I - N_0) = \left( \lambda - N_{11} - \sum_{j=2}^m \frac{\gamma_j^2}{\lambda - h_j} \right) \prod_{j=2}^m (\lambda - h_j).
$$

No pole $h_j$ is an eigenvalue of $N_0$ (the $j$-th eigenvector equation $\gamma_j v_1 = 0$ forces $v_1 = 0$, then $(h_k - h_j) v_k = 0$ kills $v_k$ for $k \ne j$, and the first row kills $v_j$). Between consecutive poles as well as on $(-\infty, h_2)$ and $(h_m, +\infty)$, the secular function $\lambda - N_{11} - \sum_{j=2}^m \gamma_j^2/(\lambda - h_j)$ is strictly increasing from $-\infty$ to $+\infty$, so $N_0$ has $m$ simple real eigenvalues $\lambda_1 < h_2 < \lambda_2 < h_3 < \dots < h_m < \lambda_m$ strictly interlacing the poles.

Because $[A_{0,\text{act}}, N_0] = 0$ and $N_0$ has simple spectrum, $A_{0,\text{act}}$ is diagonalized by the unitary eigenvector matrix $W \in U(m)$ of $N_0$ (even if $A_0$ has repeated eigenvalues). For each $\lambda_r$, the eigenvector $v^{(r)}$ of $N_0$ satisfies $v_j^{(r)} / v_1^{(r)} = \gamma_j / (\lambda_r - h_j)$ for $j \ge 2$. Introducing the degree $(m-1)$ polynomial vector

$$
\psi(t) := \left( \prod_{j=2}^m (t - h_j),\; \gamma_2 \prod_{k \ne 2} (t - h_k),\; \dots,\; \gamma_m \prod_{k \ne m} (t - h_k) \right)^\top,
$$

we see that $\psi(\lambda_r)$ is a nonzero scalar multiple of the $r$-th column of $W$, $\psi(h_j)$ is a nonzero multiple of the $j$-th standard basis vector $e_j$ ($j \ge 2$), and the leading coefficient $\psi(\infty) := \lim_{t \to \infty} t^{-(m-1)} \psi(t) = e_1$ is the first standard basis vector. Expressing these $2m$ vectors in the standard monomial basis $(1, t, \dots, t^{m-1})$ via the invertible $m \times m$ polynomial change-of-basis matrix $M$, the $m \times 2m$ matrix with columns ordered by the $2m$ alternating boundary points

$$
\lambda_1 < h_2 < \lambda_2 < \dots < h_m < \lambda_m < \infty
$$

is $M$ times the ordered Vandermonde matrix (with final column $e_m = (0, \dots, 0, 1)^\top$ at $\infty$). Every ordered maximal $m \times m$ minor of this Vandermonde matrix is strictly positive, so the $m \times 2m$ frame lies in the totally positive Grassmannian $\mathrm{Gr}_{>0}(m, 2m)$!

For any equal-size subsets $R, C \subset \{1, \dots, m\}$, orthogonality of $W$ gives $|\det W_{R, C}| = |\det W_{R^c, C^c}|$, and taking the product of the two complementary maximal minors of the $m \times 2m$ frame pairs every column scale factor once and $|\det M|^2$ uniformly, giving

$$
|\det W_{R, C}|^2 = \frac{\Delta(I_{R, C}) \, \Delta(I_{R, C}^c)}{\Delta(I_{\text{poles}}) \, \Delta(I_{\text{roots}})},
$$

where $I_{\text{poles}}$ indexes the $m$ pole and $\infty$ columns, $I_{\text{roots}}$ indexes the $m$ root columns, and $I_{R, C}$ replaces the pole columns $R$ by the root columns $C$.

By T. Lam, Dimers, webs, and positroids (J. London Math. Soc. 92 (2015), 633–656), **Theorem 2.1** (p. 637) realizes every point of the affine nonnegative Grassmann cone by boundary measurements of a planar bipartite network, and **Theorem 3.1** (p. 641) expands the product $\Delta(I) \Delta(J)$ of any two $m$-Plücker coordinates as a nonnegative sum over Temperley–Lieb noncrossing matchings pairing $I \setminus J$ with $J \setminus I$. Specializing to $J = I^c$ pairs all $2m$ cyclic nodes; every noncrossing chord cuts off an even number of boundary vertices and therefore pairs one pole with one root, i.e. defines a **noncrossing permutation** $\pi \in S_m$. Setting $I = I_{\text{poles}}$ shows that the nonnegative matching weights sum to $\Delta(I_{\text{poles}}) \Delta(I_{\text{roots}})$, and normalizing gives a single spectrum-independent probability distribution $\{w_\pi \ge 0\}$ supported on noncrossing permutations such that

$$
|\det W_{R, C}|^2 = \sum_{\pi \in S_m,\, \pi(R) = C} w_\pi \qquad \forall\, R, C \subset \{1, \dots, m\},\; |R| = |C|.
$$

By Cauchy–Binet, $\det(A_{0,\text{act}} + B_{\text{act}}) = \sum_{\pi \in S_m} w_\pi \prod_{i \in \{1\} \cup \mathcal{A}} (a_i + b_{\pi(i)})$, contradicting strict separation and completing the proof of Theorem A. $\square$

### Standalone Finite Proof at $n = 4$ (Zero External Literature, Lean 4 Verified)

At $n = 4$, there are $C_4 = \frac{1}{5}\binom{8}{4} = 14$ noncrossing permutations on the $8$ alternating nodes $\lambda_1 < h_2 < \lambda_2 < h_3 < \lambda_3 < h_4 < \lambda_4 < \infty$. Writing the $6$ strictly positive consecutive gaps $g_1, \dots, g_6 > 0$, each of the 14 Temperley–Lieb matching weights $w_\pi(g) = N_\pi(g) / D(g)$ is an explicit homogeneous degree $9$ polynomial in $g_1, \dots, g_6$ with **strictly positive integer coefficients** (802 monomials across the 14 weights). All 70 normalized complementary Vandermonde identities (`MOCMatching.all_marginals`, `MOCMatching.positive_law`), the direct signed-Leibniz-to-positive-matching Cauchy determinant identity (`MOCCauchy.arrowhead_identity`), the extraction of all 70 squared-minor marginals (`MOCMinorBridge.all_minors`), and the end-to-end implication from an actual $4 \times 4$ Hermitian arrowhead eigenvector equation to the 14-permutation law (`MOCArrowheadBasis.eigenbasis_law`, `eigenbasis_moc`, `eigenbasis_all_minors`, `noncrossing`, `distinct_support`) are kernel-verified in Lean 4 and cross-checked in `verify.py` §1.

### Proof of Corollary A2 (Self-Contained Cauchy-Interlacing Lift)

The case $n = 4$ is Corollary A1. For $n > 4$, induct on $n$. (Alternatively, Corollary A1 directly supplies the base case $A(4, 4)$ for Shitov 2025, Theorem 19, yielding $A(n, 4)$ for all $n \ge 4$.) We give a short self-contained proof.

Without loss of generality $A$ is Hermitian and $B = \operatorname{diag}(b_1, \dots, b_n)$ has $b_1 \in \mathbb{R}$ and at most $4$ nonreal entries among $b_2, \dots, b_n$. By density within the class (keeping real entries real), assume $b_j \ne b_1$ for all $j > 1$ and $H := A + b_1 I$ is invertible. Put $D := \operatorname{diag}(b_2 - b_1, \dots, b_n - b_1)$ and let $V : \mathbb{C}^{n-1} \to \mathbb{C}^n$ be the inclusion of coordinates $2, \dots, n$. By the Sylvester determinant identity,

$$
\det(A + B) = \det(H + V D V^{\ast}) = \det(H) \det(D) \det(D^{-1} + V^{\ast} H^{-1} V).
$$

Here $V^{\ast} H^{-1} V$ is $(n-1) \times (n-1)$ Hermitian and $D^{-1}$ is diagonal with at most $4$ nonreal entries. By the induction hypothesis at order $n - 1$, $\det(D^{-1} + V^{\ast} H^{-1} V)$ is a convex combination of products $\prod_{j=1}^{n-1} (\eta_j + \beta_j)$ where $\eta_1 \le \dots \le \eta_{n-1}$ are the eigenvalues of $V^{\ast} H^{-1} V$ and $(\beta_1, \dots, \beta_{n-1})$ is a permutation of $\operatorname{diag}(D^{-1})$.

By Cauchy's interlacing theorem, the eigenvalues $x_1 \le \dots \le x_n$ of $H^{-1}$ weakly interlace $\eta$: $x_j \le \eta_j \le x_{j+1}$ for all $1 \le j \le n-1$. We claim that for every $\beta \in \mathbb{C}^{n-1}$, $\prod_{j=1}^{n-1} (\eta_j + \beta_j)$ lies in the convex hull of $\prod_{j=1}^{n-1} (x_{\iota(j)} + \beta_j)$ over injections $\iota : \{1, \dots, n-1\} \hookrightarrow \{1, \dots, n\}$. Indeed, write $\eta_{n-1} = (1-t) x_{n-1} + t x_n$ ($t \in [0,1]$). By linearity in the last factor, the product is the $(1-t, t)$-convex combination of the two products with $\eta_{n-1}$ replaced by $x_{n-1}$ (deleting $x_{n-1}$ from $x$) or $x_n$ (deleting $x_n$ from $x$). In both branches the remaining prefix $(\eta_1, \dots, \eta_{n-2})$ still weakly interlaces the remaining $(n-1)$-element list of $x$ (deleting $x_{n-1}$ only widens the last bracket $[x_{n-2}, x_{n-1}]$ to $[x_{n-2}, x_n]$), so induction on list length proves the claim.

Finally, multiplying each injection product by the fixed scalar $\det(H)\det(D) = \prod_{i=1}^n (a_i + b_1) \prod_{j=2}^n (b_j - b_1)$ produces an exact vertex of $\mathcal{P}(a, b)$: each matched pair $(i, j)$ contributes

$$
(a_i + b_1)(b_j - b_1)\!\left(\frac{1}{a_i + b_1} + \frac{1}{b_j - b_1}\right) = a_i + b_j,
$$

and the unique unmatched index $i_0$ contributes $a_{i_0} + b_1$. Closure of the compact simplex handles degeneracies. The common-circle projective statement follows by applying Step 1 to the common generalized circle $C$. $\square$

---

## 3. Theorem B: All-Order Rank-Excess-Two Theorem and Order-Four Cross-Spectral Collision

### Statements

**Theorem B1 (Quadratic Monic Frame Theorem).** Let $p, q \ge 2$, let $x \in \mathbb{C}^p$ and $y \in \mathbb{C}^q$, and let $V \in \mathbb{C}^{p \times 2}, W \in \mathbb{C}^{q \times 2}$ be complex isometries ($V^{\ast} V = W^{\ast} W = I_2$). Set $X = V^{\ast} \operatorname{diag}(x) V$ and $Y = W^{\ast} \operatorname{diag}(y) W$. Then there exist nonnegative weights $w_{ikjl} \ge 0$ summing to $1$ (supported on pairs $i \ne k$, $j \ne l$) such that as monic quadratic polynomials in $t$,

$$
\det(t I_2 + X + Y) = \sum_{i \ne k,\, j \ne l} w_{ikjl} \, (t + x_i + y_j)(t + x_k + y_l).
$$

**Theorem B2 (All $n$ Rank-Excess-Two Theorem — No Concyclicity).** Let $A, B \in M_n(\mathbb{C})$ be arbitrary normal matrices. If there exists $c \in \mathbb{C}$ such that

$$
\operatorname{rank}(A - c I_n) + \operatorname{rank}(B + c I_n) \le n + 2,
$$

then $(A, B) \in \mathrm{MOC}$. In particular, MOC holds for arbitrary nonconcyclic spectra in the $(4,4;6)$ rank stratum and in every rank-excess $\le 2$ configuration.

**Corollary B3 ($n = 4$ Cross-Spectral Collision Theorem — End-to-End Lean 4 Verified).** For $n = 4$ and arbitrary $a, b \in \mathbb{C}^4$, if there exist indices $i_0, j_0 \in \{1, 2, 3, 4\}$ with $a_{i_0} + b_{j_0} = 0$, then $(A, B) \in \mathrm{MOC}$ with spectrum-independent convex weights depending only on $U \in U(4)$ and $(i_0, j_0)$ (formalized end-to-end in `MOCCollision.collision`).

### Proof of Theorems B1 and B2

**Step 1 (Short-frame base cases: $\le 3$ occupied labels or normal compression).** Let $E_i = v_i^{\ast} v_i$ and $F_j = w_j^{\ast} w_j$ be the rank at most $1$ Hermitian effects from the rows of $V, W$, satisfying $\sum_i E_i = \sum_j F_j = I_2$. Put $\alpha_i = \operatorname{tr} E_i$, $\beta_j = \operatorname{tr} F_j$, $\lambda_{ik} = \det(E_i + E_k)$, $\mu_{jl} = \det(F_j + F_l)$, and $H_{ij} = \operatorname{tr}(\operatorname{adj}(E_i) F_j) \ge 0$. Expanding $\det(X + Y)$ gives pure coefficients $\lambda_{ik}, \mu_{jl}$ and mixed coefficients $H_{ij}$, with row sums $\sum_j H_{ij} = \alpha_i$ and column sums $\sum_i H_{ij} = \beta_j$.

- Case $\le 3$ occupied rows on one side (say $p \le 3$): We claim there is a coupling assigning each unordered column pair $\{j, l\}$ (sampled with mass $\mu_{jl}$) to an ordered distinct row pair $(i, k)$ so that the unconditional marginal mass at cell $(i, j)$ equals $H_{ij}$. Test an arbitrary real payoff matrix $f_{ij}$: let $r_j$ be a maximizing row in column $j$, $s_j = f_{r_j, j}$, and $d_j = s_j - \max_{i \ne r_j} f_{ij} \ge 0$ the gap to the second-best row. Assigning distinct rows to $\{j, l\}$ incurs zero loss when $r_j \ne r_l$ and exact minimum loss $\min(d_j, d_l)$ when $r_j = r_l$. On the other hand, the loss of $H$ relative to $\sum_j \beta_j s_j$ is at least $\sum_j d_j (\beta_j - H_{r_j, j})$. For each row $i$ and threshold $t > 0$, set $T = \{j : r_j = i,\, d_j \ge t\}$ and $F_T = \sum_{j \in T} F_j \le I_2$. Since $I_2 - \operatorname{adj}(E_i)$ has eigenvalues $1$ and $1 - \alpha_i \ge 0$, it dominates a rank-1 orthogonal projection, so

$$
\sum_{j \in T} (\beta_j - H_{ij}) = \operatorname{tr}\!\left((I_2 - \operatorname{adj} E_i) F_T\right) \ge \lambda_{\min}(F_T) \ge \det(F_T) = \sum_{\{j,l\} \subset T} \mu_{jl}.
$$

Integrating over $t > 0$ yields $\sum_j d_j (\beta_j - H_{r_j, j}) \ge \sum_{j < l : r_j = r_l} \mu_{jl} \min(d_j, d_l)$, proving attainability by Hahn–Banach separation. Assigning $(x_i + y_l)(x_k + y_j)$ to each sampled $(i, k; j, l)$ matches all mixed $H_{ij}$ and pure $\mu_{jl}$ coefficients, and for $p = 3$ the probability that a pair omits row $r$ is $1 - \alpha_r = \det(I_2 - E_r) = \lambda_{ik}$ (while for $p = 2$ the unique pair has mass $1$). Thus all coefficients of $\det(tI + X + Y)$ match simultaneously with **spectrum-independent** weights!

- Case $X$ (or $Y$) normal: Diagonalize $X = \operatorname{diag}(d_1, d_2)$. Applying the $p = 2$ case to the two coordinate projections expresses $\det(X + Y)$ as a convex combination of $(d_1 + y_j)(d_2 + y_l) = \det(X + \operatorname{diag}(y_j, y_l))$ ($j \ne l$); applying the $q = 2$ case to each term expresses it in $Q := \operatorname{conv}\{(x_i + y_j)(x_k + y_l) : i \ne k,\, j \ne l\}$ without adjoining $0$.

**Step 2 (Generic minimal-support invertible minimizer & Pauli $SO(3)$ alignment).** Suppose the determinant inclusion $\det(X + Y) \in Q$ fails for some $(x, y; V, W)$. Choose $|\zeta| = 1$ with $h(z) := \operatorname{Re}(\zeta z)$ strictly lower at $\det(X + Y)$ than on $Q$. Strict separation survives small independent perturbations of $x, y$ with $V, W$ fixed, so we may impose the open dense generic conditions: (i) no three distinct points of $x$ or $y$ are collinear; (ii) for every quadruple from $x$ and quadruple from $y$, any nonzero shared quadratic leading form $P(s, t)$ of conics through them (with independent affine parts) is nondegenerate. (Open density is witnessed by $\{\pm(1,0), \pm(0,1)\}$ and $\{\pm(3/5,4/5), \pm(-4/5,3/5)\}$, whose unique shared leading form is $s^2 + t^2$, verified in `verify.py` §2.)

To ensure invertibility of $S = X + Y$ without adjoining $0$ to $Q$, translate $x \mapsto x + d \mathbf{1}$ by a small $d \in \mathbb{C}$. The shifted global minimum $m(d) = \min_{V, W} h(\det(S + dI))$ satisfies

$$
m(d) - h(d^2) = \min_{V, W} \left\{ h(\det S) + h(d \operatorname{tr} S) \right\},
$$

which is a concave function of $(\operatorname{Re} d, \operatorname{Im} d)$. Since $-h(d^2)$ has indefinite Hessian, $m(d)$ cannot vanish on any open disk. Choose a small $d$ preserving strict separation with $m(d) \ne 0$, rename $x + d\mathbf{1} \to x$, and pick a global minimizer $(V, W)$ on the compact product of complex Stiefel manifolds having the **fewest occupied rows** ($v_i \ne 0$, $w_j \ne 0$). Then $S = X + Y$ is invertible, both $X$ and $Y$ are nonnormal, and each side has at least $4$ occupied labels by Step 1.

Write $X = x_0 I_2 + u \cdot \sigma$ and $Y = y_0 I_2 + v \cdot \sigma$ in Pauli coordinates ($u, v \in \mathbb{C}^3$). Nonnormality means $(\operatorname{Re} u, \operatorname{Im} u)$ and $(\operatorname{Re} v, \operatorname{Im} v)$ are each $\mathbb{R}$-linearly independent in $\mathbb{R}^3$. Changing the basis of $W$ by $U \in SU(2)$ acts on $v$ by any $R \in SO(3)$, changing $\det(X + Y) = (x_0 + y_0)^2 - (u + R v) \cdot (u + R v)$. Global minimality forces $I_3$ to maximize $\operatorname{Re}(\zeta u \cdot R v) = \operatorname{tr}(C^\top R)$ over $SO(3)$, where $C = \operatorname{Re}(\zeta u v^\top) \in \mathbb{R}^{3 \times 3}$ has rank $2$. Because $C$ is singular, the unused singular direction allows adjusting the determinant sign, so $\operatorname{tr}(C) = \max_{R \in SO(3)} \operatorname{tr}(C^\top R) = \lVert C \rVert_{\ast}$. In an SVD $C = \sum_{k=1}^2 s_k l_k r_k^\top$, equality forces $r_k = l_k$, so the real planes spanned by $(\operatorname{Re} u, \operatorname{Im} u)$ and by $(\operatorname{Re} v, \operatorname{Im} v)$ coincide! A simultaneous $SU(2)$ rotation maps this common plane to the real-symmetric Pauli plane $\operatorname{span}(\sigma_1, \sigma_3)$, making $X, Y$, and $Z := \zeta \operatorname{adj}(S)$ all **complex symmetric**.

Put $T(z) := \operatorname{Herm}(z Z)$, a real symmetric $2 \times 2$ matrix for every $z \in \mathbb{C}$. Unrestricted complex Stiefel stationarity gives Hermitian Lagrange multipliers $L_x, L_y$ such that

$$
v_i M_i = 0, \qquad M_i := T(x_i) - L_x,
$$

and similarly $w_j (T(y_j) - L_y) = 0$. Summing $v_i^{\ast} v_i M_i = 0$ gives $L_x = \frac{1}{2}(X Z + X^{\ast} Z^{\ast})$ (the entrywise real part of $X Z$), which is real symmetric because $X$ and $Z$ are symmetric; hence $L_x, L_y$, and all $M_i$ are real symmetric. The leading quadratic $P(s, t) := \det T(s + it)$ is not identically zero (its complexification at $(1, -i)$ equals $\det Z \ne 0$). All occupied $x_i$ satisfy $\det(T(x_i) - L_x) = 0$. No occupied $M_i$ can vanish: otherwise $P(x_k - x_i) = \det(T(x_k) - T(x_i)) = 0$ on at least three distinct real directions $x_k - x_i$ (by no-three-collinear genericity), forcing $P \equiv 0$. Hence every occupied $M_i$ has a 1D **real** kernel; rephasing each row individually makes every row of $V$ and $W$ real while keeping them global complex Stiefel minimizers.

**Step 3 (Branch 1: Definite matrix in the pencil — flat row deletion).** By genericity, $P(s, t)$ is nondegenerate. If $P(s_0, t_0) > 0$ for some $(s_0, t_0)$, then $T(s_0 + i t_0)$ is definite; whitening it and orthogonally diagonalizing the other generator gives a real invertible $R \in GL_2(\mathbb{R})$ such that $G := R^\top Z R = \operatorname{diag}(z_1, z_2)$ with $z_1, z_2 \in \mathbb{C}$ linearly independent over $\mathbb{R}$. Since each group has $\ge 4$ real symmetric effects in $S_2(\mathbb{R})$ ($\dim = 3$), there exist nonzero real vectors $a, b$ supported on occupied rows with $\sum a_i E_i = 0$ and $\sum b_j F_j = 0$. Set $D_x = \sum a_i x_i E_i$ and $D_y = \sum b_j y_j F_j$. Contracting stationarity with $a_i E_i$ yields entrywise real parts $\operatorname{Re}(D_x Z) = 0$ and $\operatorname{Re}(D_y Z) = 0$. For any real combination $D = \alpha D_x + \beta D_y$, $D' := R^{-1} D R^{-\top}$ is symmetric and satisfies entrywise $\operatorname{Re}(D' G) = 0$. Since $z_1, z_2$ are $\mathbb{R}$-linearly independent, $D_{12}' = 0$ and $\operatorname{Re}(D_{11}' z_1) = 0$. Choosing a nonzero $(\alpha, \beta) \in \mathbb{R}^2$ to kill the single remaining real coordinate $\operatorname{Im}(D_{11}' z_1)$ makes $D_{11}' = 0$, hence $\det D = 0$. Scaling effects by $1 + t \alpha a_i$ and $1 + t \beta b_j$ preserves isometry until the first multiplier hits $0$, sends $S \mapsto S + t D$, and keeps $h(\det(S + t D)) = h(\det S) + t \operatorname{Re}(\operatorname{tr}(D Z)) + t^2 h(\det D) = h(\det S)$ constant. Killing a row at finite $t$ contradicts minimal occupied support!

**Step 4 (Branch 2: Everywhere-indefinite pencil — imaginary tangent test & covariance contradiction).** Otherwise $P(s, t) < 0$ for all $(s, t) \ne (0, 0)$. The 2D subspace $T(\mathbb{C}) \subset S_2(\mathbb{R})$ has a positive definite trace-orthogonal normal $P_0 = R R^\top$ (in an eigenbasis of a nonzero normal $\operatorname{diag}(p_1, p_2)$, $p_1 p_2 \le 0$ would allow a nonzero PSD matrix in $T(\mathbb{C})$, contradicting $P < 0$). Set $G = R^\top Z R$, $U(z) = \operatorname{Herm}(z G)$, $S' = R^{-1} S R^{-\top}$, and $C_0 = R^{-1} R^{-\top}$. Then $U : \mathbb{C} \to S_2(\mathbb{R})$ is injective and traceless, so $\operatorname{tr} G = 0$ and $\operatorname{tr} S' = 0$. Writing $E_i' := R^{-1} E_i R^{-\top} = b_i P_i$ ($b_i > 0$, $P_i$ real rank-1 orthogonal projection) and $M_i' := R^\top M_i R$, we have $M_i' P_i = 0$ and constant trace $\operatorname{tr}(M_i') = -\operatorname{tr}(R^\top L_x R) =: d_x \ne 0$, hence $M_i' = d_x (I_2 - P_i)$ (and similarly $d_y (I_2 - Q_j)$ on the $y$-side).

Sign forcing ($d_x > 0$ and $d_y > 0$): Suppose $d_x < 0$, so every occupied $M_i$ is nonzero negative semidefinite. On the real minimizer $V$, consider the **purely imaginary** Stiefel tangent $\dot v_i = i t_i v_i J$ with $t_i \in \mathbb{R}$ and $J$ the $90^\circ$ rotation matrix with rows $(0, 1)$ and $(-1, 0)$. Because $E_i J + J E_i = \|v_i\|^2 J$, the first variation of $V^{\ast} V$ is $i (\sum t_i \|v_i\|^2) J$ and the first variation of $S$ is $i (\sum t_i \|v_i\|^2 x_i) J$. With $\ge 4$ occupied rows and only $3$ real linear constraints $\sum t_i \|v_i\|^2 = 0$, $\sum t_i \|v_i\|^2 x_i = 0$, there is a nonzero real vector $t$ yielding a valid complex Stiefel tangent with $\delta S = 0$. The second variation of the constrained Lagrangian along $\dot V$ is therefore purely the quadratic multiplier term

$$
\delta^2 \mathcal{L} = 2 \sum_i \dot v_i M_i \dot v_i^{\ast} = 2 \sum_i t_i^2 (v_i J) M_i (v_i J)^{\ast} < 0,
$$

because $v_i J \perp \ker M_i$ on every varying row, contradicting minimality! Hence $d_x > 0$ and symmetrically $d_y > 0$.

Covariance contradiction: In order two, $\operatorname{tr} S' = 0$ gives $\operatorname{adj}(S') = -S'$, so $G = \zeta (\det R)^2 \operatorname{adj}(S') = -\zeta (\det R)^2 S'$. Let $B_0 = \operatorname{tr} C_0$, $\mu_g = \frac{1}{B_0} \sum_{i \in g} b_i s_i$, and $\delta_i = s_i - \mu_g$ (pooling both groups $g \in \{x, y\}$). Since $\sum b_i P_i = C_0$ per group and $\operatorname{tr} S' = 0$, we have $\mu_x + \mu_y = 0$. Subtracting the group mean from $U(s_i) = R^\top L_g R + d_g (I_2 - P_i)$ gives $U(\delta_i) = -d_g (P_i - C_0 / B_0)$. Therefore, for every $z \in \mathbb{C}$,

$$
U(z) = \operatorname{Herm}\!\left(-\zeta (\det R)^2 z S'\right) = -(\det R)^2 \sum_{i} b_i \operatorname{Re}(\zeta z \delta_i) (P_i - C_0 / B_0) = (\det R)^2 \sum_i \frac{b_i}{d_g} \operatorname{Re}(\zeta z \delta_i) \, U(\delta_i).
$$

Canceling the injective $\mathbb{R}$-linear map $U$ and pairing both sides with $z$ via $(z, w) \mapsto \operatorname{Re}(\zeta z w)$ gives

$$
\operatorname{Re}(\zeta z^2) = (\det R)^2 \sum_i \frac{b_i}{d_g} \left(\operatorname{Re}(\zeta z \delta_i)\right)^2 \ge 0 \qquad \forall\, z \in \mathbb{C},
$$

which is absurd upon choosing $z^2 = -1/\zeta$! Thus $\det(X + Y) \in Q$.

**Step 5 (Monic quadratic polynomial lift and reduction to Theorem B2).** To upgrade to the monic quadratic polynomial identity in Theorem B1, any real linear separator on $(\det S, \operatorname{tr} S)$ tests $\operatorname{Re}(\alpha \det S + \beta \operatorname{tr} S)$. For $\alpha \ne 0$, shifting $x \mapsto x + (\beta/\alpha)\mathbf{1}$ absorbs $\beta \operatorname{tr} S$ into $\alpha \det(S + (\beta/\alpha)I)$ minus the same constant $\beta^2/\alpha$ on both sides; $\alpha = 0$ follows by taking $\alpha \to 0$.

For Theorem B2, replace $(A, B)$ by $(A - cI, B + cI)$ so that $A$ has $p$ nonzero eigenvalues $a_1, \dots, a_p$ on an orthonormal support frame $E \in \mathbb{C}^{n \times p}$ and $B$ has $q$ nonzero eigenvalues $b_1, \dots, b_q$ on $F \in \mathbb{C}^{n \times q}$, with $p + q \le n + 2$. If $\operatorname{col}[E, F] \ne \mathbb{C}^n$, then $\det(A + B) = 0$ and a zero permutation product exists (since $p + q - 1 \le n + 1$ cannot avoid a $(0,0)$ match when the sum is singular; or by Drury–Cload 1992). Otherwise $k := p + q - n \in \{0, 1, 2\}$. Put $C := \prod_{i=1}^p a_i \prod_{j=1}^q b_j$ and let $T = \ker([E, F]) \cong \mathbb{C}^k$ via $(E^{\ast} w, -F^{\ast} w)/\sqrt{2}$. By Jacobi's complementary minor theorem,

$$
\det(A + B) = C \cdot \tau \cdot \det(V^{\ast} \operatorname{diag}(a^{-1}) V + W^{\ast} \operatorname{diag}(b^{-1}) W),
$$

where $V \in \mathbb{C}^{p \times k}, W \in \mathbb{C}^{q \times k}$ are isometries and $0 < \tau := 2^{-k} \det(E E^{\ast} + F F^{\ast}) \le 1$. For $k = 2$, multiplying the vertices of $Q$ by $C$ produces exact nonzero permutation products of $\mathcal{P}(a, b)$ (every 2-matching extends to a full permutation using the $n - p$ and $n - q$ zeros). If both $p < n$ and $q < n$, then $0$ is itself a permutation product of $\mathcal{P}(a, b)$, absorbing the mass $1 - \tau$. If one support is full (say $p = n$), then $q = 2$, so $\tau = 1$ and $Y$ is normal — covered without adjoining $0$. The cases $k = 1$ (scalar convex average) and $k = 0$ (empty determinant $1$, $\tau \in (0, 1]$) are immediate. $\square$

### Standalone Division-Free Proof of Corollary B3 (`MOCCollision.collision`)

At $n = 4$ with $a_0 + b_0 = 0$, shift by opposite scalars to $a_0 = b_0 = 0$. Expanding $\det(A + U B U^{\ast})$ by row/column masks keeps only terms with row set containing $0$ and column set omitting $0$. Define the $4 \times 4$ nonnegative matrix $T$ by $T_{00} = 0$, $T_{i0} = |u_{i0}|^2$ ($i > 0$), $T_{0j} = |u_{0j}|^2$ ($j > 0$), and $T_{ij} = |\det U_{\{0,i\}, \{1,2,3\} \setminus \{j\}}|^2$ ($i, j > 0$). By row and column unitarity of $U$, every row and column sum of $T$ equals $h := 1 - |u_{00}|^2 \in [0, 1]$. For $h = 0$, $\det(A + U B U^{\ast}) = 0 = z_{\mathrm{id}}$. For $h > 0$, Birkhoff's theorem decomposes $T / h$ into permutation matrices supported on permutations $\pi$ with $\pi(0) \ne 0$. Replacing each such $\pi$ by $\tilde\pi$ that swaps the images of the two nonzero indices $i \ne 0$ with $\pi(i) \ne 0$ matches every monomial of $\det(A + U B U^{\ast})$ identically, while the remaining mass $1 - h$ sits on the zero vertex $z_{\mathrm{id}} = 0$. No division by any nonzero spectral entry is used, and the complete theorem for arbitrary collision indices $(i_0, j_0)$ is proved in `MOCCollision.collision`. $\square$

---

## 4. Theorem C: Universal $U(4) \to SO(4)$ Simultaneous 70-Minor Real-Chord Reduction

### Statement

**Theorem C (Universal $U(4) \to SO(4)$ Real-Chord Reduction).** For every unitary matrix $U \in U(4)$, there exist diagonal unitary matrices $D_1, D_2$, real orthogonal matrices $O_1, O_2 \in O(4)$, and an angle $t \in \mathbb{R}$ such that

$$
D_1 U D_2 = O_1 \operatorname{diag}(e^{it}, 1, 1, 1) O_2.
$$

Consequently, there exist $O_+, O_- \in SO(4)$ and a single spectrum-independent scalar $s = \frac{1 + \cos t}{2} \in [0, 1]$ such that for **all 70** equal-size row and column subsets $I, J \subset \{1, 2, 3, 4\}$ ($|I| = |J|$) simultaneously,

$$
|\det U_{I, J}|^2 = s \, |\det (O_+)_{I, J}|^2 + (1 - s) \, |\det (O_-)_{I, J}|^2.
$$

**Corollaries.**
1. **Exact reduction to $SO(4)$:** For **every** pair of $4 \times 4$ normal matrices $(A, B)$ with arbitrary spectra $(a, b)$, we have $\operatorname{conv} \Delta_{U(4)}(a, b) = \operatorname{conv} \Delta_{SO(4)}(a, b)$. Unrestricted $n = 4$ MOC thus collapses completely from 16-dimensional $U(4)$ to 6-dimensional $SO(4) \cong (SO(3) \times SO(3)) / \mathbb{Z}_2$, with no constraint on either spectrum.
2. No strict isolated non-dephasably-real extrema: Along $V(t) = O_1 \operatorname{diag}(e^{it}, 1, 1, 1) O_2$, every real support objective is affine in $\cos t$. At any non-dephasably-real unitary ($\sin t \ne 0$), stationarity forces the objective constant along the entire circle $t \in [0, 2\pi]$, which reaches real orthogonal endpoints $t = 0, \pi$. Hence no non-dephasably-real $U \in U(4)$ can be a strict isolated local extremum on the phase-equivalence quotient.

### Proof

**Lemma C1 (Phase balancing on $T^m$).** Let $w_j = (u_j, v_j) \in \mathbb{C}^2$ ($1 \le j \le m$) satisfy the polygon inequalities $|u_j| \le \sum_{k \ne j} |u_k|$ for all $j$. Then there exist unit phases $\zeta_1, \dots, \zeta_m \in S^1$ such that $\sum_{j=1}^m \operatorname{Re}(\zeta_j w_j) = (0, 0)$.

Proof. Suppose $F(\theta_1, \dots, \theta_m) := \sum_{j=1}^m \operatorname{Re}(e^{i\theta_j} w_j) \in \mathbb{R}^2 \setminus \{0\}$ never vanishes on $T^m$. The winding number $W_j \in \mathbb{Z}$ of the $j$-th coordinate loop $\theta_j \mapsto F(\theta)$ about $0$ is independent of the fixed angles $\{\theta_k : k \ne j\}$ by homotopy. Choose $\{\theta_k : k \ne j\}$ so that $\operatorname{Re}(e^{i\theta_k} u_k) = +|u_k|$ for every $k \ne j$. Then the first coordinate of $F$ along the $j$-th loop is $\ge \sum_{k \ne j} |u_k| - |u_j| \ge 0$, so the loop stays in the closed right half-plane avoiding $0$ and admits a continuous argument in $[-\pi/2, \pi/2]$; hence $W_j = 0$ for every $j$. On the other hand, the diagonal loop $f(t) = F(t, \dots, t)$ satisfies $f(t + \pi) = -f(t)$, so its winding number is odd. Yet in $\pi_1(T^m)$ the diagonal loop equals the sum of the $m$ coordinate loops, giving odd $= \sum_{j=1}^m W_j = 0$, a contradiction. $\square$

**Lemma C2 (Balancing diagonal & equal matching products).** Normalize $\det U = 1$ by a scalar phase and index rows/columns by $0, 1, 2, 3$. Write $p_{K, I} := \det U_{K, I}$ in increasing index order. For any column pair $I$ and $J = I^c$, complementary minors of $SU(4)$ satisfy $p_{K^c, I} = (-1)^{\sum K^c + \sum I} \overline{p_{K, J}}$ and $p_{K^c, J} = (-1)^{\sum K^c + \sum J} \overline{p_{K, I}}$. Because $0 + 1 + 2 + 3 = 6$ is even, the signs cancel in the product $\overline{p_{K^c, I}} p_{K^c, J} = \overline{p_{K, I}} p_{K, J}$. Orthogonality of the $I$ and $J$ columns of $\wedge^2 U$ therefore collapses to the three-term sum

$$
\sum_{j=1}^3 \overline{p_{0j, I}} \, p_{0j, J} = 0,
$$

so the three moduli $|p_{0j, I} p_{0j, J}|$ ($j = 1, 2, 3$) satisfy the triangle inequalities! Apply Lemma C1 to $w_j = (p_{0j, 01} p_{0j, 23},\; p_{0j, 02} p_{0j, 13}) \in \mathbb{C}^2$ ($j = 1, 2, 3$) to obtain unit phases $\zeta_1, \zeta_2, \zeta_3$ with $\sum_{j=1}^3 \operatorname{Re}(\zeta_j w_j) = (0, 0)$. Choose unimodular $g_0$ with $g_0^2 = \zeta_1 \zeta_2 \zeta_3$ and set $g_j = \zeta_j / g_0$ ($j = 1, 2, 3$), so $\prod_{i=0}^3 g_i = 1$. Let $D = \operatorname{diag}(g_0, g_1, g_2, g_3)$ and define the symmetric unitary matrix $M := U^\top D U$. By Cauchy–Binet and $g_{K^c} = \overline{g_K}$,

$$
\det M_{I, I^c} = 2 \operatorname{Re} \sum_{j=1}^3 \zeta_j \, p_{0j, I} p_{0j, I^c} = 0 \qquad \text{for } I \in \{\{0,1\}, \{0,2\}\}.
$$

Equivalently, the three off-diagonal matching products of $M$ are all equal:

$$
M_{01} M_{23} = M_{02} M_{13} = M_{03} M_{12}.
$$

**Lemma C3 (Rank-one diagonal unitary completion).** Every $4 \times 4$ symmetric unitary matrix $M$ with $M_{01} M_{23} = M_{02} M_{13} = M_{03} M_{12}$ satisfies $\operatorname{rank}(M - D') \le 1$ for some diagonal unitary $D'$.

*Proof.*
- If the common product is nonzero, every $M_{ij} \ne 0$ ($i \ne j$), and setting $c_0^2 = M_{01} M_{02} / M_{12}$, $c_j = M_{0j} / c_0$ gives $M_{ij} = c_i c_j$ for all $i \ne j$.
- If the common product is $0$, the graph of nonzero off-diagonal entries has no two disjoint edges, so it is either empty, a single edge, a star with $\ge 2$ leaves, or a triangle plus an isolated vertex. A star with $\ge 2$ leaves is impossible because two leaf rows share exactly one common nonzero column and cannot be orthogonal. In the triangle case, the same square-root formula factors $M_{ij} = c_i c_j$ on the triangle with $c = 0$ at the isolated vertex.
- In both the full and triangle factorizations, write $M = \Delta + c c^\top$ with $\Delta = \operatorname{diag}(d_i)$. On the support of $c$ (size $\ge 3$), put $a_i := d_i \bar c_i / c_i$. The off-diagonal equations of $M M^{\ast} = I$ divided by $c_i \bar c_j$ give $a_i + \bar a_j = -\|c\|^2$ for all distinct active $i, j$. With $\ge 3$ active vertices, all $a_i$ are equal with $2 \operatorname{Re} a_i = -\|c\|^2$; the diagonal equations $|d_i|^2 + |c_i|^2 (2 \operatorname{Re} a_i + \|c\|^2) = 1$ then force $|d_i| = 1$ (and isolated vertices already have $|d_i| = 1$), so $D' = \Delta$ is diagonal unitary!
- In the single-edge case, $M$ is block diagonal with a $2 \times 2$ symmetric unitary block; subtracting an eigenvalue $\lambda$ ($|\lambda| = 1$) of that block on the $2 \times 2$ block and the original unimodular diagonal on the isolated vertices yields $\operatorname{rank}(M - D') \le 1$. Diagonal $M$ takes $D' = M$. $\square$

**Completion of Theorem C.** Let $V := D^{1/2} U (D')^{-1/2} \in U(4)$. By Lemma C3, $\operatorname{rank}(V^\top V - I) = \operatorname{rank}((D')^{-1/2}(M - D')(D')^{-1/2}) \le 1$. Right-multiplying by $V^{\ast}$ gives $\operatorname{rank}(V^\top - \overline{V}^\top) \le 1$, so $\operatorname{Im} V$ has real rank $\le 1$. Taking a real SVD $O_1^\top V O_2^\top = A + i s_0 E_{11}$ ($O_1, O_2 \in O(4)$, $A \in \mathbb{R}^{4\times 4}$, $s_0 \in \mathbb{R}$), unitarity yields $A^\top (s_0 E_{11}) = (s_0 E_{11})^\top A$ and $A (s_0 E_{11})^\top = (s_0 E_{11}) A^\top$. If $s_0 \ne 0$, the first row and column of $A$ have zero off-diagonals, so $A + i s_0 E_{11} = \operatorname{diag}(e^{it}, O')$ with $O' \in O(3)$; absorbing $O'$ into $O_2$ gives $D_1 U D_2 = O_1 \operatorname{diag}(e^{it}, 1, 1, 1) O_2$.

Now consider the rank-1 pencil $V(z) := O_1 \operatorname{diag}(z, 1, 1, 1) O_2$. By multilinearity in columns, every minor $\det(V(z)[I, J])$ is affine in $z$ with **real** coefficients: $\det(V(z)[I, J]) = b_{IJ} + a_{IJ} z$ ($a_{IJ}, b_{IJ} \in \mathbb{R}$). Therefore, for any $|z| = 1$,

$$
|\det V(z)_{I, J}|^2 = a_{IJ}^2 + b_{IJ}^2 + 2 a_{IJ} b_{IJ} \operatorname{Re} z = \frac{1 + \operatorname{Re} z}{2} |b_{IJ} + a_{IJ}|^2 + \frac{1 - \operatorname{Re} z}{2} |b_{IJ} - a_{IJ}|^2.
$$

Setting $O_\pm = V(\pm 1)$ (adjusting a row sign to lie in $SO(4)$, which preserves every squared minor) proves the simultaneous 70-minor chord identity. Because $\det(A + U B U^{\ast})$ is a complex linear combination of the 70 squared minors $|\det U_{I, J}|^2$, the same chord yields $\operatorname{conv}\Delta_{U(4)}(a, b) = \operatorname{conv}\Delta_{SO(4)}(a, b)$. (Exact algebraic identities and a concrete rational unitary witness are verified in `verify.py` §3.) $\square$

---

## 5. Theorem D: Disjoint Two-Tetrahedron $n = 4$ Family, Level-1 Shor Obstruction, and Escaped KKT Saddles

### Theorem D1: Continuous Disjoint Nonconcyclic Two-Tetrahedron Family Over All $U(4)$

**Statement.** Suppose that after a common Möbius transformation of the combined signed spectrum $(a, -b)$ (with $\omega^2 + \omega + 1 = 0$), the 8 projective nodes are

$$
a \sim (0, 1, \omega, \omega^2), \qquad -b \sim (\infty, \lambda, \lambda \omega, \lambda \omega^2) \qquad (\lambda \in \mathbb{R}, \text{ equivalently } \lambda^3 \in \mathbb{R}).
$$

Then $(A, B) \in \mathrm{MOC}$ over the **entire** unitary group $U(4)$. For every $\lambda \in \mathbb{R} \setminus \{0, 1\}$, all 8 nodes are distinct, there is no cross-spectral collision, and **both** quadruples are strictly nonconcyclic (finite affine charts avoiding all 8 nodes exist for every $\lambda$).

**Proof (Exact Klein $SO(6)$ Lift + 151 Rational Quartic SOS Certificates).** Using homogeneous projective brackets (which coincide with $\det(\operatorname{diag} a + U \operatorname{diag} b U^{\ast})$ up to a single $U$-independent nonzero constant), each permutation product $z_p$ minus the common term $-\lambda^3$ has $2(z_p + \lambda^3) = A_p + (B_p + i\sqrt{3}\,D_p)\lambda + (C_p + i\sqrt{3}\,E_p)\lambda^2$ with integer coefficients $(A_p, B_p, D_p, C_p, E_p)$ taking $10$ distinct rows across $p \in S_4$.

Normalize $\det U = 1$. In the Hodge-paired basis $(e_{0a}, \varepsilon_a e_{(0a)^c})$ ($a = 1, 2, 3$) of $\wedge^2 \mathbb{C}^4$, the exterior square $R = \wedge^2 U \in SU(6)$ satisfies $\overline{R_{a+, b+}} = R_{a-, b-}$ and $\overline{R_{a+, b-}} = R_{a-, b+}$ (an $SO(6)$ matrix in a complex torus basis). Setting $t_{ab}^{\pm} = |R_{a+, b\pm}|^2$, $Q = t^{+} + t^{-}$, and $d = t^{+} - t^{-}$, $Q$ is $3 \times 3$ doubly stochastic and $S = |U|^2$ is recovered from $\operatorname{diag}(1, d)$ by the $4 \times 4$ Walsh transform. Every 1-, 2-, and 3-minor probability — and hence every spectral support functional — is affine in the 14 coordinates $(1, Q_{11}, Q_{12}, Q_{21}, Q_{22}, d_{11}, \dots, d_{33})$, which have exact rank $14$ on $S_4$. Thus every support functional on the 10 vertices lifts uniquely to a degree $2$ polynomial $q_r(R)$ on $SO(6)$.

Represent each vertex in $\mathbb{R}^2$ via $(\operatorname{Re}, \operatorname{Im}/\sqrt{3})$. For each of the $\binom{10}{2} = 45$ vertex pairs and both orientations, the oriented edge support functional $g(\lambda)$ has degree $\le 4$ in $\lambda$. Compactifying both real rays by $\lambda = \pm s/(1-s)$ ($s \in [0, 1]$) and clearing denominators gives Bernstein control vectors; 36 exact binary de Casteljau subdivisions partition the 180 oriented/chart roots into **216 exact leaf cones**. Intersecting each leaf's nonnegative Bernstein orthant with the 10 supporting-edge inequalities yields a pointed rational polyhedral cone whose extreme rays are enumerated by exact double description. Every nonzero ray $r$ is certified nonnegative on $SO(6)$ by one of **151 exact rational quartic SOS identities** (stored in `two_tetrahedron_sos.json`),

$$
6 \, q_r(R) = \sum_j u_j \sum_{g \in G} \left| \sum_m a_{jm} (g R)^m \right|^2 \pmod{\mathcal{I}_{\text{unitary}, \le 4} + \mathcal{I}_{\text{Hodge}, \le 4}}, \qquad u_j \in \mathbb{Q}_{>0},\; a_{jm} \in \mathbb{Z},
$$

averaged over the $6$-element dihedral symmetry group $G$ and reduced modulo row/column unitarity quadrics and the $\det R = +1$ Hodge complementary-minor equations of sizes $3$ and $4$ through total degree $4$. All 216 leaf cones, all double-description rays, and all 151 exact SOS identities (plus mutation rejection) are verified with zero floating-point arithmetic in `verify.py` §4. $\square$

### Theorem D2: Complete 48-Vertex Classification of the Level-1 Shor Relaxation and Failure of $P(\delta)$

**Statement.** Before imposing entrywise $S \ge 0$, the level-1 Klein/Shor relaxation of $O(6)$ projects onto

$$
P_{\text{outer}} := \left\{ (Q, d) \;:\; Q \in B_3,\; |d_{ab}| \le Q_{ab} \right\},
$$

whose extreme points are precisely the **48** signed permutation matrices $(P_\pi, \operatorname{diag}(\varepsilon) P_\pi)$ ($\pi \in S_3$, $\varepsilon \in \{\pm 1\}^3$): the 24 true permutations ($\varepsilon_1 \varepsilon_2 \varepsilon_3 = +1$) and their 24 barycentric reflections $2\,\mu_{\text{fiber}}(z) - z_p$ (with $\varepsilon_1 \varepsilon_2 \varepsilon_3 = -1$, realized inside $O(6) \setminus SO(6)$ as orientation-reversing blocks). Imposing the linear constraint $S \ge 0$ intersects $P_{\text{outer}}$ with that constraint; the reflected vertices themselves have negative entries in $S$. Neither $P_{\text{outer}}$ nor its single-facet truncation $P(\delta) := P_{\text{outer}} \cap \{F_\alpha \ge -\delta\}$ certifies MOC for all spectra, for any $\delta > 0$, even after imposing $S \ge 0$. Here $F_\alpha$ is the Orbit-2 facet from Section 7.

**Proof.** Nonnegativity of $t_{ab}^{\pm} = \frac{1}{2}(Q_{ab} \pm d_{ab})$ forces $|d_{ab}| \le Q_{ab}$. Conversely, Birkhoff decomposition of $Q \in B_3$ combined with choosing signs $\varepsilon_i$ of mean $d_{ij}/Q_{ij}$ whenever row $i$ maps to $j$ realizes every point of $P_{\text{outer}}$ as a convex combination of the 48 vertices. The signed permutation coordinates are realized by permuting the three planes and preserving or reversing each plane's orientation, so all 48 vertices are feasible in the unrestricted relaxation. Negating $d$ keeps $Q$ fixed and replaces $S$ by $J_4/2-S$, where $J_4$ is the all-ones matrix. The following disjoint nonconcyclic examples separate the relaxations from the permutation polygon; the first and an independent truncation witness are checked in `verify.py` §4:
1. $a = (0, 1, i, 2+2i)$, $b = (2, 1+i, 3+i, 2i)$: $\max_{p \in S_4} \operatorname{Re}(z_p) = -40$, whereas the reflected vertex achieves $-34 > -40$.
2. To witness failure even with $S \ge 0$, use $a = ((3+3i)/2, 1, -2+i, 1+2i)$, $b = (1, 1+2i, -i, 1+i)$ and $h(z) = \operatorname{Re}((-1+i)z)$. The maximum of $h(z_p)$ over the $24$ permutations is $40$, attained in particular by the four permutations with one-line forms $(0,3,1,2)$, $(1,2,0,3)$, $(2,1,3,0)$ and $(3,0,2,1)$. They all have $F_\alpha = 0$ and their average has diagonal entries $1/4$ in $S$. The reflected identity has $S=J_4/2-I_4$, $Q=I_3$, $F_\alpha=-2$, and score $42$: the four scores in the identity fiber are $4,38,30,20$, so the reflection gives $(4+38+30+20)/2-4=42$. Mixing this reflection into the average with weight $\theta = \min(\delta/2,1/3)$ keeps $S \ge 0$ and $F_\alpha \ge -\delta$ and yields score $40+2\theta>40$. This is a failure of the relaxation, not a unitary counterexample. $\square$

### Theorem D3 ($\Pi_4$-Escaped Irreducible KKT Saddles)

Let $K$ be the skew-symmetric conference matrix

$$
K = \begin{pmatrix} 0 & 1 & 1 & 1 \\ -1 & 0 & 1 & -1 \\ -1 & -1 & 0 & 1 \\ -1 & 1 & -1 & 0 \end{pmatrix}, \qquad K^\top = -K, \quad K^2 = -3 I_4.
$$

The rational special orthogonal matrix $U = \frac{1}{7}(I_4 + 4K) \in SO(4)$ has all entries nonzero (hence is irreducible for simple spectra) and strictly escapes $\Pi_4$ with Orbit-2 facet value $F(U) = -316/2401$ (verified in `MOCFacet.special_orthogonal`, `MOCFacet.facet_breach`, `MOCFacet.permutations_nonnegative`). For the rank-2 bracket table $C = \sqrt{3}\,I_4 + i K$ (whose row and column cross-ratios are nonreal, hence disjoint doubly nonconcyclic), $U$ is an exact KKT stationary point of $\operatorname{Re}(\zeta \det(A + U B U^{\ast}))$ with $\zeta = i \overline{Z'(1/4)}$: exact arithmetic in `verify.py` §4 confirms zero gradient across all 12 off-diagonal anti-Hermitian tangent directions, and exact Hessian block inertias $(3, 0, 3)$ on the real-skew block and $(0, 3, 3)$ on the imaginary-symmetric block (saddle point strictly inside the permutation hull). A nonempty relatively open family of genuinely complex (non-real plaquette $-5408/3236205$), $\Pi_4$-escaped ($-1482968/17105655$) irreducible KKT saddles is also verified in `verify.py` §4.

---

## 6. Theorem E: All-Order Collision-Free Singular-Boundary Classification and Transverse Curvature

### Statement

**Theorem E (Collision-Free Singular-Boundary Classification & Inward Curvature, All $n$).** Use the difference convention $C = -U B U^{\ast}$, $H = A - C$, with disjoint spectral lists $\sigma(A) \cap \sigma(C) = \varnothing$ (no cross-spectral collision). Assume $H$ is singular ($\det H = 0$) and there exists a nonzero real linear functional $h(z) = \operatorname{Re}(\zeta z)$ such that $h(z_\sigma) \ge 0$ for all $\sigma \in S_n$ — that is, $0$ lies on a supporting line of $\mathcal{P}(a, -c)$. Then **no negative second-order direction exists**: for every Hermitian $K \in M_n(\mathbb{C})$ and $D(t) = \det(A - e^{itK} C e^{-itK})$, we have $h(D'(0)) = 0$ and $h(D''(0)) \ge 0$. More precisely:
1. Either all $2n$ points $\sigma(A) \cup \sigma(C)$ lie on a single generalized circle ($h(D) \equiv 0$), or one of the two spectra has at most $2$ distinct values (where the two-value identity below gives MOC for arbitrary multiplicities);
2. Or **$H$ has corank exactly $1$** and admits a simultaneous reducing $2 \times 2$ block of $(A, C)$ whose $4$ within-block eigenvalues are simple and alternate by color around a generalized circle $S$, while on the $(n-2)$-dimensional complement either one residual operator is scalar or all residual eigenvalues lie on a second generalized circle $T \ne S$ whose two open arcs cut out by $S$ separate the off $S$ residual colors. For simple spectra with residual values off $S \cap T$, the transverse Hessian is strictly positive definite away from active circle intersections (and positive semidefinite in general).

### Proof

**Two-value case (arbitrary multiplicities).** Suppose $A$ has eigenvalues $\alpha,\beta$, with $\alpha$ of multiplicity $m$. In an orthonormal eigenbasis of $C$ write $C=\operatorname{diag}(c_j)$ and $A=\beta I+(\alpha-\beta)XX^{\ast}$, where the columns of $X$ are an orthonormal basis of the $\alpha$-eigenspace. Put $L=\beta I-C$. When $L$ is invertible, the determinant identity $\det(I+ST)=\det(I+TS)$ and $X^{\ast}X=I_m$ give

$$
\det(A-C)=\det L\,\det\!\left(X^{\ast}\operatorname{diag}\!\left(\frac{\alpha-c_j}{\beta-c_j}\right)X\right).
$$

For $J\subseteq\{1,\ldots,n\}$ of size $m$, let $X_J$ denote the submatrix of rows indexed by $J$ in increasing order. Cauchy–Binet gives

$$
\det(A-C)=\sum_{|J|=m} |\det X_J|^2
  \prod_{j\in J}(\alpha-c_j)\prod_{j\notin J}(\beta-c_j).
$$

The weights are nonnegative and sum to $\det(X^{\ast}X)=1$, again by Cauchy–Binet. Each product pairs the $m$ copies of $\alpha$ with $J$ and the other copies with its complement, so is a permutation product. The identity extends to singular $L$ by continuity, shifting all $c_j$ by the same small scalar with the eigenbasis fixed. A scalar spectrum gives a single product. If $C$ instead has at most two values, exchange $A,C$ and multiply both determinant and products by $(-1)^n$. Thus MOC holds on the whole unitary orbit in this branch. In particular, $h(D(t))\ge0=h(D(0))$ for all real $t$; the first derivative vanishes and the second is nonnegative at $0$.

**Step 1 (Minimal $2+2$ alternating circuit).** Let $v \ne 0$ satisfy $A v = C v$ ($\|v\| = 1$). Then the spectral probability distributions $\mu_A, \mu_C$ of $v$ with respect to $A$ and $C$ share the three real moments $\operatorname{Re} z, \operatorname{Im} z, |z|^2$ (since $\langle v, A v \rangle = \langle v, C v \rangle$ and $\|A v\|^2 = \|C v\|^2$). Choose a nonzero positive relation $\sum_{i \in I} p_i \tilde a_i = \sum_{j \in J} q_j \tilde c_j$ of minimal support between the paraboloid lifts $\tilde z = (1, \operatorname{Re} z, \operatorname{Im} z, |z|^2) \in \mathbb{R}^4$ of distinct eigenvalues. By Carathéodory/rank ($\dim = 4$), $|I| + |J| \le 5$, and by strict convexity of the paraboloid and disjointness, $|I| \ge 2, |J| \ge 2$.

We rule out $|I| + |J| = 5$ (say $|I| = 2, |J| = 3$ with values $r_1, r_2$ and $s_1, s_2, s_3$). The Gram-matching $3 \times 3$ unitary $W$ realizing the zero determinant on $\{r_1, r_2, r_3\} \times \{s_1, s_2, s_3\}$ (for any third padded value $r_3$) has **no zero entries**: its first two rows have entry moduli proportional to $\sqrt{q_j} |s_j - r_2|$ and $\sqrt{q_j} |s_j - r_1| > 0$, and its orthogonal third row has entry moduli proportional to $\sqrt{q_k q_l} |s_k - s_l| > 0$. In order $3$, every $3 \times 3$ doubly stochastic matrix with strictly positive entries admits a Birkhoff decomposition with all $6$ permutation weights strictly positive, and $\det(A_3 - W C_3 W^{\ast})$ equals that convex mixture of the $6$ products. Multiplying by any nonzero complement assignment forces all $6$ products onto the supporting line $h = 0$ (since their positive mixture is $0$ and $h \ge 0$). Ratios of products differing by a transposition are therefore real, meaning every cross-ratio among $\{r_1, r_2, s_1, s_2, s_3\}$ is real — so all $5$ points lie on one generalized circle, their lifts are coplanar, and the $5$-term relation was not minimal!

Hence $|I| = |J| = 2$: there is a $2+2$ circuit $\{a_1, a_2\}, \{c_1, c_2\}$ whose four lifts are coplanar with crossing chords, meaning $a_1, c_1, a_2, c_2$ alternate around a generalized circle $S$. On this $2 \times 2$ block, $0$ is a strictly positive combination of the two nonzero permutation products, so for every complement assignment the two products fixing this block are opposite nonzero numbers on $h = 0$.

**Step 2 (Swap-test separation and corank $1$ block split).** Take any pair of residual eigenvalue occurrences $a,c$ in a complement assignment, allowing repetitions of the circuit values. If both lie on $S$, there is no side condition to check. Otherwise, exchange the two colors if necessary (which multiplies the determinants and permutation products by $(-1)^n$ and transforms $h$ accordingly) so that $c \notin S$. Swapping $(a, c)$ with $(a_i, c_j)$ multiplies the corresponding product on $h = 0$ by $r_{ij} = \frac{(a_i - c)(a - c_j)}{(a_i - c_j)(a - c)}$. The four unswapped products have checkerboard signs along $h=0$, so $h \ge 0$ forces the four numbers $(-1)^{i+j}\operatorname{Im} r_{ij}$ to be all nonnegative or all nonpositive. For $w(z) = (z - a)/(z - c)$, the image $w(S)$ is a finite circle, and

$$
r_{ij} = -\frac{w(c_j)}{w(a_i)-w(c_j)}, \qquad
\operatorname{Im} r_{ij} = -\frac{\operatorname{Im}(\overline{w(a_i)}w(c_j))}{|w(a_i)-w(c_j)|^2}.
$$

In the alternating order $w(a_1),w(c_1),w(a_2),w(c_2)$, the oriented edge tests for $0$ have a common weak sign. Their sum is twice the signed area, so the common sign is the interior sign. Thus $0$ belongs to the convex quadrilateral. If it lies in the open circumdisk, $a$ and $c$ lie on opposite open sides of $S$. Otherwise $0$ is a vertex, so $a$ is one of the two active eigenvalues of its own color (disjointness excludes the opposite color).

If both spectra lie on $S$, this is the common-circle case. If only one color has off $S$ points, every value of the other color must be one of its two active values (apply the two-value identity above). Otherwise the swap test shows that $S$ weakly separates the spectra, and the only values on $S$ are the four active ones. Because the defining equation of $S$ is an affine functional of the lift $\tilde z$, equality of moments of any kernel vector $v$ forces $v$ to be supported strictly on the four circuit values! Consequently $\operatorname{span}(v, A v) = \operatorname{span}(v, C v)$ is a 2D reducing subspace of both $A$ and $C$ carrying a rank $1$ singular $2 \times 2$ block. Moreover, every complement permutation product lies on a single line through $0$; if neither residual operator is scalar, pairwise transpositions force all residual eigenvalues onto a single generalized circle $T \ne S$ (real cross-ratios). A second kernel vector in the complement would again require all four circuit values, contradicting $T \ne S$ (or disjointness if one residual operator is scalar). Thus $\operatorname{corank}(H) = 1$.

**Step 3 (Transverse Hessian in the two-circle chart).** Block-preserving variations keep $h(D) \equiv 0$, and phase symmetry kills cross-block first derivatives and mixed Hessian terms. If a residual operator is scalar, diagonalizing the complement decouples the normal Hessian into independent $3 \times 3$ blocks, each PSD by $n = 3$ MOC. Otherwise $S$ and $T$ intersect at two points. When neither intersection is spectral, a Möbius map sends $S \cap T$ to $\{0, \infty\}$, $T$ to $\mathbb{R}$, and $S$ to $\xi \mathbb{R}$ ($|\xi| = 1$, $\operatorname{Im} \xi \ne 0$), giving

$$
A = \xi a_0 \oplus P, \qquad C = \xi c_0 \oplus (-Q), \qquad P, Q > 0,\quad a_0, c_0 \text{ Hermitian } 2 \times 2,
$$

with alternating eigenvalues $s_1, s_2$ of $a_0$ and $t_1, t_2$ of $c_0$, $G := P + Q > 0$, $\lambda := \operatorname{tr}(a_0 - c_0) \ne 0$, and $a_0 v = c_0 v$ ($\|v\| = 1$). For an off-diagonal skew-Hermitian cross-block generator $X(T_0)$ with upper-right block $T_0$ and lower-left block $-T_0^{\ast}$, put $u = T_0^{\ast} v$ and $z = T_0^{\ast} c_0 v$. Expanding the top $2 \times 2$ Schur complement to order $\varepsilon^2$ and dividing by $\xi^2$ gives the exact transverse quadratic form

$$
\left.\frac{1}{2}\frac{d^2}{d\varepsilon^2}\right|_{\varepsilon=0} \operatorname{Im}\!\left(\frac{D(\varepsilon)}{\xi^2}\right) = -\lambda \det(G) \operatorname{Im}(\xi) \left[ z^{\ast} G^{-1} z + u^{\ast} (Q - Q G^{-1} Q) u \right].
$$

Since $G > Q > 0$, we have $Q - Q G^{-1} Q > 0$, and $v, c_0 v$ are linearly independent (otherwise $a_0 v = c_0 v$ would be a collision), so the bracket is strictly positive definite on the full transverse space. Checking a single swap of an ordered pair $(s_i, t_i)$ with $s_i t_i \ge 0$ against a residual pair $(p, -q)$ shows that the inward support sign matches $-\operatorname{sign}(\lambda \operatorname{Im} \xi)$. If an active eigenvalue lies at a circle intersection, perturbing slightly along $S$ and $T$ while preserving the singular $2 \times 2$ block and sign-tracking via a strictly inward row-swap rotation yields PSD in the limit. Exact symbolic checks for $n = 4, \dots, 8$ (plus a corank $2$ reducing-plane collision remark) are verified in `verify.py` §5. $\square$

---

## 7. Theorem F: Exact $\Pi_4$ Geometry, Sharp $O(4) = U(4)$ Breach, $V_4$ Protection, and Tao $6 \times 6$ Escape

### Theorem F1 (Exact 82-Facet $\Pi_4$, Sharp $O(4) = U(4)$ Orbit-2 Breach, and $V_4$ Hadamard Protection)

Let $S_{ij} = |U_{ij}|^2$ and $Q_{ij} = |\det U_{R_i, R_j}|^2 + |\det U_{R_i, R_j^c}|^2$ ($R_i = \{0, i+1\}$, $0 \le i, j \le 2$), and let $\Pi_4 := \operatorname{conv}\{(S(P), Q(P)) : P \in S_4\} \subset B_4 \times B_3$ be the 13-dimensional order $4$ coupled permutation compound polytope.

1. **Exact H-representation:** Exact rational double description (`verify.py` §6) proves that $\Pi_4$ has **exactly 82 facets** in 3 orbits under $S_4 \times S_4$ and transposition:
   - $16$ singleton nonnegativity facets $S_{ij} \ge 0$ (18 tight vertices each),
   - $18$ complementary-pair minor facets $Q_{ij} \ge 0$ (20 tight vertices each),
   - $48$ exceptional **Orbit-2 (conference) facets**, represented by $F(U) := \operatorname{tr} S + \frac{1}{3} \sum_{i=0}^2 (Q_{i, i+1} - Q_{i+1, i}) \ge 0$ (indices mod $3$), with slack multiset $\{0^{13}, 2^{10}, 4^1\}$ on $S_4$ (verified in `MOCFacet.permutations_nonnegative`).

2. **Sharp $O(4) = U(4)$ Orbit-2 breach:** The first two orbits have minimum $0$ on $U(4)$. On the 48 Orbit-2 facets, let $\rho \in (0, 1)$ be the unique real root of $\rho^3 + \rho^2 + 3\rho - 1 = 0$ ($\rho \approx 0.2955977425$). Then

$$
\min_{U \in U(4)} F(U) = \min_{U \in O(4)} F(U) = \gamma := \frac{4\rho^2}{3 + \rho^2} - \frac{8\rho}{(3 + \rho^2)^2} = -0.1348844977362459\ldots,
$$

attained at the real special orthogonal conference matrix $U_\rho = (\rho I_4 + K_{\text{conf}}) / \sqrt{3 + \rho^2}$ (where $K_{\text{conf}}^\top = -K_{\text{conf}}$, $K_{\text{conf}} K_{\text{conf}}^\top = 3 I_4$).

- **Exact algebraic proof on $U(4)$:** Degree-6 Hermitian moment-SOS certificate over $\mathbb{Q}(\rho)$ (`orbit2_u4_sos.json`, verified in `verify.py` §6 on all 261 free invariant moments with rational root isolation):

$$
F(U J) - \gamma = \sum_{\ell=1}^{23} \lambda_\ell \cdot \frac{1}{24} \sum_{g \in G} \left| \sum_i c_{\ell i} h_i(g U) \right|^2 \pmod{\mathcal{I}_{U(4), \le 6}}, \qquad \lambda_\ell \in \mathbb{Q}(\rho)_{>0}.
$$

   - Independent analytic proof on $O(4)$: Representing $U \in SO(4)$ via unit quaternions $z \mapsto p z q$ yields $F = 4 \sum p_i^2 q_i^2 - 8 \prod p_i + 8 \prod q_i$. Putting $x_i = p_i^2$, $y_i = q_i^2$, $X = \sqrt{\prod x_i}$, $Y = \sqrt{\prod y_i}$, minimizing $x \cdot y - 2X - 2Y$ over the product of two simplices rules out negative interior stationary points (subtracting two stationarity equations forces a $2+2$ split $(a,a,b,b)$ and $(b,b,a,a)$, giving $F \ge 0$), so the minimum lies on the boundary $Y = 0$ with $y$ concentrated at $\min_i x_i$ and the remaining three coordinates equal by AM–GM; writing $\rho = \sqrt{x_{\min}/x_{\max}}$ yields $4\rho^2/(3+\rho^2) - 8\rho/(3+\rho^2)^2$, whose derivative has the sign of $\rho^3 + \rho^2 + 3\rho - 1$. (And Theorem C independently guarantees $\min_{U(4)} F = \min_{O(4)} F$!)
   - Reminder: Escaping $\Pi_4$ is an obstruction to spectrum-independent convex weights (Drury 1992), **not** a counterexample to MOC.
3. **Klein-four ($V_4$) protection of all $4 \times 4$ complex Hadamard matrices:** Every $4 \times 4$ complex Hadamard matrix ($|U_{ij}| = 1/2$) satisfies $(S(U), Q(U)) = (J_4/4, Q(U)) \in \Pi_4$, hence satisfies MOC for **every** pair of $4 \times 4$ spectra! Proof: The surjective homomorphism $S_4 \to S_3$ on the three pair partitions has regular kernel $V_4$, so each uniform coset projects to a $3 \times 3$ permutation matrix $P_\pi$ while averaging to $J_4/4$ in the $S$-component; Birkhoff decomposition of $Q(U) \in B_3$ yields $(J_4/4, Q(U)) \in \Pi_4$ (formalized end-to-end in `MOCKlein.hadamard`).

### Theorem F2 (Tao's $6 \times 6$ Complex Hadamard Exact $\Pi_6$-Escape and Positive Spectral Slices)

In contrast to order $4$, Tao's $6 \times 6$ complex Hadamard matrix $U_{ij} = \omega^{e_{ij}} / \sqrt{6}$ ($\omega^3 = 1, \omega \ne 1$, exponent table in `TaoForbidden.lean` and `verify.py` §7) escapes the full order $6$ compound polytope $\Pi_6$ by an exact rational distance:

1. **45 exact zero $2 \times 2$ minors (`TaoForbidden.every_permutation`):** The zero set $Z = \{(ik, jl) : e_{ij} + e_{kl} \equiv e_{il} + e_{kj} \pmod 3\}$ has exact size $45$ (3 forbidden column pairs per row pair). Every $\sigma \in S_6$ hits $Z$ either $r(\sigma) = 1$ time (360 permutations) or $r(\sigma) = 5$ times (360 permutations); none has $r(\sigma) = 0$. Hence $\sum_{(I,J) \in Z} M_{I,J} \ge 1$ on $\Pi_6$ while vanishing on Tao's matrix.
2. **Optimal signed interpolation and exact $\ell_\infty$ distance $1/40$ (`verify.py` §7):** Assigning signed weights $w_\sigma = +5/1440$ for $r(\sigma) = 1$ and $w_\sigma = -1/1440$ for $r(\sigma) = 5$ matches **every** squared minor $M_{I,J}(U)$ of every order $k = 0, \dots, 6$ simultaneously, yielding the exact universal identity $\det(A + U B U^{\ast}) = (5 \bar z_1 - \bar z_5)/4$ for all $a, b \in \mathbb{C}^6$, where $\bar z_r$ is the arithmetic mean of $\{z_\sigma : r(\sigma) = r\}$. The negative mass $N = 1/4$ is optimal ($0 = \sum w_\sigma r(\sigma) \ge (1 + N) \cdot 1 - 5 N \implies N \ge 1/4$). Moreover, the $40$ order $3$ minors with $M_{I,J}(U) = 1/8$ sum to $5$ on Tao's matrix and to at most $4$ on every permutation ($4$ on $r=1$, $0$ on $r=5$), giving $\ell_\infty(M(U), \Pi_6) \ge (5-4)/40 = 1/40$, attained identically by the uniform probability measure on $\{r = 1\}$.
3. **Universal positive spectral slices (`verify.py` §7):** Fixing Tao's $6 \times 6$ Hadamard conjugator (or any diagonal-phase / row-column permutation equivalent), MOC holds with **exact positive spectrum-independent weights** for arbitrary complex spectra whenever either:
   - (Repeated eigenvalue) at least one eigenvalue repeats within $\sigma(A)$ or $\sigma(B)$: realized by the uniform distribution on the $192$ permutations whose every forbidden hit has exactly one row label in the repeated pair; or
   - (Cross-spectral collision) $a_i + b_j = 0$ for any $(i, j)$: realized by an explicit 41-term positive distribution with denominator $96$ (transitivity of the 45-mask automorphism group transports both laws to all 15 pairs and all 36 cross positions).

   Consequently, any counterexample using Tao's $6 \times 6$ matrix must have all $12$ labeled values $a_1, \dots, a_6, -b_1, \dots, -b_6$ pairwise distinct.

---

## 8. Verification Manifest and Formalization Boundary

### Exact Zero-Float Python Verifier (`results/marcus-de-oliveira/verify.py`)

Run `python3 results/marcus-de-oliveira/verify.py` (standard Python + exact rational/symbolic SymPy; zero floating-point arithmetic anywhere in the trust path; runtime ~12 seconds). Every section includes an explicit mutation test verifying that a corrupted certificate or weight is rejected:

- **Section 1 (Theorem A):** Regenerates all 70 compound identities and cleared Cauchy-pencil determinant identities for $n = 4$ over $\mathbb{Z}[g_1, \dots, g_6]$ (14 positive noncrossing weights, 802 monomials).
- **Section 2 (Theorem B):** Checks the rank-excess-2 genericity witness, definite-pencil flat deletion, imaginary tangent sign-forcing, covariance identity, and a concrete $6 \times 6$ nonnormal rank $(4, 4)$ unitary lift over all $720$ permutation products.
- **Section 3 (Theorem C):** Verifies $SU(4)$ complementary-minor pairing, the rational balancing phase bracket, and all 70 simultaneous squared-minor chord identities on an exact non-dephasably-real unitary witness.
- **Section 4 (Theorem D):** Independently checks all 216 exact Bernstein/de Casteljau leaf cones, double-description extreme rays, and all 151 exact rational quartic $SO(6)$ SOS certificates (`two_tetrahedron_sos.json`), the 48-vertex Shor and $P(\delta)$ obstruction witnesses, and both the rational and complex $\Pi_4$-escaped irreducible KKT saddles.
- **Section 5 (Theorem E):** Symbolically verifies the collision-free corank $1$ transverse Hessian formula and strict positive definiteness for $n = 4, \dots, 8$, plus exact corank $2$ collision fixtures.
- **Section 6 (Theorem F1):** Recomputes all 82 facets of $\Pi_4$ by exact rational double description (16 / 18 / 48 orbits), checks exact conference attainment, and verifies the 23-orbit-averaged $\mathbb{Q}(\rho)$ SOS certificate (`orbit2_u4_sos.json`) on all 261 free moments with exact rational root isolation.
- **Section 7 (Theorem F2):** Exhaustively verifies Tao's $6 \times 6$ 45-zero $2 \times 2$ mask, all $36 + 225 + 400$ squared-minor identities for the $(5/1440, -1/1440)$ signed law, exact $\ell_\infty$ distance $1/40$, mask automorphism transitivity, and both positive slice laws (192-uniform and 41/96).

### Lean 4 (`v4.35.0`) Formalization Suite (`lean/Conjectures/MarcusDeOliveira/`)

All 12 modules use strictly narrow Mathlib imports (zero `import Mathlib`), compile under `lean -j1 -M4500`, pass independent kernel replay via `leanchecker`, and pass `ProofAudit.lean` using only the standard Lean axioms `{propext, Classical.choice, Quot.sound}`:

| Module | Key Verified Declarations | Mathematical Content |
| :--- | :--- | :--- |
| `Matching.lean` | `MOCMatching.all_marginals`, `positive_law`, `support_checked` | All 70 normalized complementary Vandermonde identities with 14 positive noncrossing weights in 6 gap coordinates |
| `Arrowhead.lean` | `MOCCauchy.arrowhead_identity`, `arrowhead` | Exact signed-Leibniz-to-positive-matching Cauchy determinant identity for $n = 4$ |
| `MinorBridge.lean` | `MOCMinorBridge.all_minors` | Extraction of all squared-minor marginals from a spectrum-independent determinant identity |
| `AllCompounds.lean` | `MOCArrowheadBasis.eigenbasis_law`, `eigenbasis_moc`, `eigenbasis_all_minors`, `noncrossing`, `distinct_support` | Actual $4 \times 4$ interlacing Hermitian arrowhead eigenvector equation $\implies$ single 14-noncrossing-permutation law reproducing all 70 squared minors and all complex determinant pencils |
| `Collision.lean` | `MOCCollision.collision` | **End-to-end $n = 4$ Cross-Spectral Collision Theorem** for arbitrary $a, b \in \mathbb{C}^4$ with $a_{i_0} + b_{j_0} = 0$ and arbitrary $U \in U(4)$ |
| `Displacement.lean` | `MOCDisplacement.slopes`, `commuting_star` | Off-diagonal resolvent elimination and commutation $[A, N] = 0$ |
| `Stationary.lean` | `MOCStationary.stationary_entries` | Matrix-level two-sided resolvent + Hermitian stationarity commutator $\implies$ sandwich identities and slope equations |
| `Cut.lean` | `MOCCut.recover_cut` | Algebraic cut recovery $[P, A] = 0$ at $c \ne 0$ without assuming $D$ invertible |
| `Projective.lean` | `MOCProjective.mobius`, `scale_table` | Arbitrary-order $\mathrm{PGL}_2(\mathbb{C})$ invariance of MOC |
| `Hadamard.lean` | `MOCKlein.hadamard`, `section_flat`, `compound_bistochastic` | Klein-four protection placing every $4 \times 4$ complex Hadamard matrix inside $\Pi_4$ |
| `Facet.lean` | `MOCFacet.special_orthogonal`, `facet_breach`, `permutations_nonnegative` | Exact rational $SO(4)$ witness $(I+4K)/7$ with $F = -316/2401$ and $F(P) \ge 0$ for all $P \in S_4$ |
| `TaoForbidden.lean` | `TaoForbidden.every_permutation`, `tuple_obstruct` | Exact 45-zero $2 \times 2$ minor obstruction hitting every $\sigma \in S_6$ |

**Explicit Formalization Boundary.** `MOCCollision.collision`, `MOCProjective.mobius`, `MOCKlein.hadamard`, `MOCFacet.special_orthogonal`, `MOCFacet.facet_breach`, `MOCFacet.permutations_nonnegative`, `TaoForbidden.every_permutation`, and the $n = 4$ interlacing arrowhead eigenbasis theorems `MOCArrowheadBasis.eigenbasis_law`, `MOCArrowheadBasis.eigenbasis_moc`, `MOCArrowheadBasis.eigenbasis_all_minors` are end-to-end Lean 4 kernel theorems. The analytic support-maximizer, KKT, density, and topological arguments for the full all $n$ one-outlier theorem (Theorem A), rank-excess $2$ theorem (Theorem B2), universal $U(4) \to SO(4)$ reduction (Theorem C), and singular-boundary classification (Theorem E) are audited paper proofs, while the 151-SOS two-tetrahedron atlas (Theorem D1), 82-facet $\Pi_4$ / 23-square $\mathbb{Q}(\rho)$ Orbit-2 optimum (Theorem F1), and Tao signed/slice laws (Theorem F2) are exact zero-float algebraic proofs replayed by `verify.py`.

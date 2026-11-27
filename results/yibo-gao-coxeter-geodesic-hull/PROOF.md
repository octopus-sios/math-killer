# Disproof of Gaetz–Gao's Strong Hull Property Conjecture (`arXiv:2012.06841`)

## 1. Conjecture and Main Results

In *The hull metric on Coxeter groups* (Christian Gaetz and Yibo Gao, `arXiv:2012.06841v2`, Definition 1.1 and Conjecture 1.2), let $G$ be a connected undirected graph with shortest-path metric $d$. A subset $C \subseteq V(G)$ is **convex** if $w \in C$ whenever $u, v \in C$ and $d(u, w) + d(w, v) = d(u, v)$; the **convex hull** $\operatorname{Conv}(X)$ of $X \subseteq V(G)$ is the intersection of all convex sets containing $X$.

- $G$ has the **hull property** if for all $u, v, w \in V(G)$,

$$
|\operatorname{Conv}(u, v)| \cdot |\operatorname{Conv}(v, w)| \ge |\operatorname{Conv}(u, w)|,
$$

  equivalently, $\log |\operatorname{Conv}(-,-)|$ defines a metric on $V(G)$.

- $G$ has the **strong hull property** if for all $u, v, w \in V(G)$,

$$
|\operatorname{Conv}(u, v)| \cdot |\operatorname{Conv}(v, w)| \ge |\operatorname{Conv}(u, v, w)|.
$$

**Conjecture 1.2 (Gaetz–Gao, `arXiv:2012.06841v2`).** For every Coxeter group $(W, S)$, the undirected right Cayley graph $\operatorname{Cay}(W, S)$ has the strong hull property.

We **disprove** Conjecture 1.2 — and in fact refute the weaker **hull property** as well, showing that $\log |\operatorname{Conv}(-,-)|$ is not a metric on Coxeter groups in general.

**Theorem 1 (Concrete and asymptotic disproof in type $\widetilde{A}_3$).** Let $W = W(\widetilde{A}_3)$ be the affine Coxeter group of type $\widetilde{A}_3$ (rank $4$, with simple reflections $S = \{s_0, s_1, s_2, s_3\}$ forming a $4$-cycle of edges labeled $3$ and opposite pairs labeled $2$). Let

$$
t_1 = (s_0 s_3 s_1 s_2)^2, \qquad t_2 = (s_2 s_0 s_3 s_1)^2.
$$

Then $\operatorname{Cay}(W(\widetilde{A}_3), S)$ fails both the **hull property** and the **strong hull property**:

**1. Asymptotic separation.** For every integer $m \ge 1$, setting $u_m = t_1^{6m}$ and $v_m = t_2^{12m}$,

$$
|\operatorname{Conv}(e, u_m)| \le 48(6m + 2), \qquad |\operatorname{Conv}(e, v_m)| \le 48(12m + 2), \qquad |\operatorname{Conv}(u_m, v_m)| \ge (m + 1)^3.
$$

More sharply, $|\operatorname{Conv}(e, t_1^L)| = 12L$ and $|\operatorname{Conv}(e, t_2^L)| = 12L + 1$ for all $L \ge 1$, while $|\operatorname{Conv}(t_1^{L}, t_2^{2L})| = \Theta(L^3)$. Hence

$$
\frac{|\operatorname{Conv}(u_m, v_m)|}{|\operatorname{Conv}(e, u_m)| \cdot |\operatorname{Conv}(e, v_m)|} = \Theta(m) \longrightarrow \infty \quad (m \to \infty).
$$

**2. Explicit small counterexample to the ordinary hull property (hence also strong hull).** With $u = t_1^5$ ($\ell(u) = 40$) and $v = t_2^{10}$ ($\ell(v) = 80$, $\ell(u^{-1}v) = 100$):

$$
|\operatorname{Conv}(e, u)| = 60, \qquad |\operatorname{Conv}(e, v)| = 121, \qquad |\operatorname{Conv}(u, v)| = 7921 > 7260 = 60 \cdot 121.
$$

Thus $\log |\operatorname{Conv}(u, v)| > \log |\operatorname{Conv}(e, u)| + \log |\operatorname{Conv}(e, v)|$, violating the triangle inequality for $\log |\operatorname{Conv}(-,-)|$.

**3. Explicit symmetric counterexample to the strong hull property.** With $u = t_1^8$ and $v = t_2^8$ (both of length $64$):

$$
|\operatorname{Conv}(e, u)| = 96, \qquad |\operatorname{Conv}(e, v)| = 97, \qquad |\operatorname{Conv}(e, u, v)| = 9825 > 9312 = 96 \cdot 97.
$$

**Theorem 2 (Sharp dichotomy for irreducible affine Coxeter groups).** Every irreducible affine Coxeter group $W_{\mathrm{aff}}$ of rank at least $4$ — namely $\widetilde{A}_n$ ($n \ge 3$), $\widetilde{B}_n$ ($n \ge 3$), $\widetilde{C}_n$ ($n \ge 3$), $\widetilde{D}_n$ ($n \ge 4$), $\widetilde{F}_4$, $\widetilde{E}_6$, $\widetilde{E}_7$, and $\widetilde{E}_8$ — fails both the hull property and the strong hull property.

Combined with Gaetz–Gao's verification for $I_2(\infty) = W(\widetilde{A}_1)$ (`arXiv:2012.06841v2`) and Ziming Liu's proof for $\widetilde{A}_2, \widetilde{C}_2, \widetilde{G}_2$ (`arXiv:2505.15871v4`), this yields a complete classification for irreducible affine Coxeter groups: **both the hull and strong hull properties hold if and only if the Coxeter rank is at most $3$.**

---

## 2. Proof of Theorem 1 via an Isometric $\ell_1$-Embedding of $W(\widetilde{A}_3)$

Our proof of Theorem 1 is completely self-contained and is formalized end-to-end in Lean 4 (`lean/Conjectures/YiboGaoCoxeterGeodesicHull.lean`). It does not require citing Tits' convexity theorem or root-system machinery externally; instead it establishes an exact isometric embedding of $\operatorname{Cay}(W(\widetilde{A}_3), S)$ into $(\mathbb{Z}^6, \lVert\cdot\rVert_1)$.

### 2.1. The affine permutation model $\mathrm{AffPerm}_4 \cong W(\widetilde{A}_3)$

Let $Q(A_3) = \{ a = (a_0, a_1, a_2, a_3) \in \mathbb{Z}^4 : a_0 + a_1 + a_2 + a_3 = 0 \}$ and form the semidirect product

$$
\mathrm{AffPerm}_4 := Q(A_3) \rtimes S_4, \qquad (a, \sigma) \cdot (b, \tau) = (a + \sigma \cdot b,\ \sigma \tau), \qquad (\sigma \cdot b)_i = b_{\sigma^{-1}(i)}.
$$

Each $f = (a, \sigma) \in \mathrm{AffPerm}_4$ acts on $\mathbb{Z}$ as a $4$-periodic bijection: writing $x = r + 4q$ with $r \in \{0, 1, 2, 3\}$ and $q = \lfloor x / 4 \rfloor$,

$$
f(x) = \sigma(r) + 4\bigl(a_{\sigma(r)} + q\bigr), \qquad f^{-1}(y) = \sigma^{-1}(r') + 4\bigl(q' - a_{r'}\bigr) \quad (y = r' + 4q').
$$

Clearly $(fg)(x) = f(g(x))$ and $f(x + 4k) = f(x) + 4k$ for all $k \in \mathbb{Z}$.

Define four elements $g_0, g_1, g_2, g_3 \in \mathrm{AffPerm}_4$ by:

- $g_0 = ((1, 0, 0, -1),\ (0\ 3))$, which swaps $4q + 3 \leftrightarrow 4q + 4$ (equivalently $-1 \leftrightarrow 0 \pmod 4$),
- $g_1 = (0,\ (0\ 1))$, $g_2 = (0,\ (1\ 2))$, $g_3 = (0,\ (2\ 3))$, swapping $4q + (k-1) \leftrightarrow 4q + k$.

Direct calculation shows $g_i^2 = 1$, $(g_i g_{i+1 \bmod 4})^3 = 1$, and $(g_0 g_2)^2 = (g_1 g_3)^2 = 1$. Hence the universal property of Coxeter groups gives a homomorphism $\rho : W(\widetilde{A}_3) \to \mathrm{AffPerm}_4$ with $\rho(s_i) = g_i$.

**Lemma 2.1.** The homomorphism $\rho : W(\widetilde{A}_3) \to \mathrm{AffPerm}_4$ is a group isomorphism.

*Proof.* Define elements $T_1, T_2, T_3 \in W(\widetilde{A}_3)$ by

$$
T_1 = s_2 s_3 s_0 s_3 s_2 s_1, \qquad T_2 = s_3 s_0 s_1 s_0 s_3 s_2, \qquad T_3 = s_0 s_1 s_2 s_1 s_0 s_3.
$$

Using only the Coxeter relations of $\widetilde{A}_3$, one verifies directly (and mechanically in Lean via explicit Coxeter rewrite certificates) that:

1. $T_1, T_2, T_3$ pairwise commute, and $T_1 T_2 T_3 = s_0 s_1 s_2 s_3 s_2 s_1$;
2. conjugation by $s_1, s_2, s_3$ acts on $T_1, T_2, T_3$ via:
   - $s_1 T_1 s_1 = T_1^{-1}$, $s_1 T_2 s_1 = T_1 T_2$, $s_1 T_3 s_1 = T_3$;
   - $s_2 T_1 s_2 = T_1 T_2$, $s_2 T_2 s_2 = T_2^{-1}$, $s_2 T_3 s_2 = T_2 T_3$;
   - $s_3 T_1 s_3 = T_1$, $s_3 T_2 s_3 = T_2 T_3$, $s_3 T_3 s_3 = T_3^{-1}$.

The parabolic subgroup $\langle s_1, s_2, s_3 \rangle$ receives a homomorphism $\varphi : S_4 \to W(\widetilde{A}_3)$ sending $(0\ 1) \mapsto s_1$, $(1\ 2) \mapsto s_2$, $(2\ 3) \mapsto s_3$. Define

$$
\psi_{\mathrm{trans}}(a) := T_1^{a_0} T_2^{a_0 + a_1} T_3^{a_0 + a_1 + a_2} \quad (a \in Q(A_3)), \qquad \psi(a, \sigma) := \psi_{\mathrm{trans}}(a)\,\varphi(\sigma).
$$

Relations (1)–(2) give $\varphi(\sigma) \psi_{\mathrm{trans}}(a) \varphi(\sigma)^{-1} = \psi_{\mathrm{trans}}(\sigma \cdot a)$, so $\psi$ is a group homomorphism from $\mathrm{AffPerm}_4$ to $W(\widetilde{A}_3)$. One checks $\psi(\rho(s_i)) = s_i$ for $i = 0, 1, 2, 3$ (for $i = 0$, $\psi(g_0) = T_1 T_2 T_3 s_1 s_2 s_3 s_2 s_1 = s_0$) and

$$
\rho(T_1) = t_{(1,-1,0,0)}, \qquad \rho(T_2) = t_{(0,1,-1,0)}, \qquad \rho(T_3) = t_{(0,0,1,-1)},
$$

hence $\psi \circ \rho = \mathrm{id}$ on $W(\widetilde{A}_3)$ and $\rho \circ \psi = \mathrm{id}$ on $\mathrm{AffPerm}_4$. $\square$

### 2.2. Exact $\ell_1$ distance formula and box characterization of $\operatorname{Conv}(u, v)$

For each $f \in \mathrm{AffPerm}_4$ and $0 \le i < j \le 3$, define the integer threshold coordinate

$$
\Phi_{ij}(f) := \left\lfloor \frac{f^{-1}(i) - f^{-1}(j)}{4} \right\rfloor \in \mathbb{Z}.
$$

Since $f^{-1}(i) = \sigma^{-1}(i) - 4a_i$, we have the exact formula

$$
\Phi_{ij}(f) = \begin{cases} a_j - a_i - 1 & \text{if } \sigma^{-1}(i) < \sigma^{-1}(j), \\ a_j - a_i & \text{if } \sigma^{-1}(i) > \sigma^{-1}(j). \end{cases}
$$

In particular, $a_j - a_i - 1 \le \Phi_{ij}(f) \le a_j - a_i$ always, and for a pure translation $t_a = (a, \mathrm{id})$ we have $\Phi_{ij}(t_a) = a_j - a_i - 1$ for all $i < j$ (so $\Phi_{ij}(\mathrm{id}) = -1$).

Define the $\ell_1$ distance on $\mathrm{AffPerm}_4$ by

$$
d_{\ell_1}(f, g) := \sum_{0 \le i < j \le 3} |\Phi_{ij}(f) - \Phi_{ij}(g)|.
$$

**Proposition 2.2 (Isometric $\ell_1$-embedding into $\mathbb{Z}^6$).** For all $u, v \in W(\widetilde{A}_3)$,

$$
d_{\operatorname{Cay}}(u, v) = \ell(u^{-1} v) = d_{\ell_1}(\rho(u), \rho(v)).
$$

*Proof.* First, fix $f = (a, \sigma)$ in $\mathrm{AffPerm}_4$ and $k \in \{0, 1, 2, 3\}$. Set $r_1 = (k - 1) \bmod 4$ and $r_2 = k$. Since $(f g_k)^{-1}(y) = g_k(f^{-1}(y))$, the generator $g_k$ moves residue $r_1$ by $+1$, moves residue $r_2$ by $-1$, and fixes the other two residues. Because $f^{-1}(i) \not\equiv f^{-1}(j) \pmod 4$ for $i \ne j$, changing at most one of $f^{-1}(i), f^{-1}(j)$ by $\pm 1$ never crosses a multiple of $4$ (crossing would force the new difference to be $\equiv 0 \pmod 4$, impossible since $(fg_k)^{-1}$ is a $4$-periodic bijection). Only the unique pair $\{c, d\} = \{\sigma(r_1), \sigma(r_2)\}$ has both residues shifted in opposite directions:

$$
\Phi_{ij}(f g_k) = \begin{cases} \Phi_{ij}(f) + 1 & \text{if } (i, j) = (c, d), \\ \Phi_{ij}(f) - 1 & \text{if } (i, j) = (d, c), \\ \Phi_{ij}(f) & \text{otherwise.} \end{cases}
$$

Hence $d_{\ell_1}(f, f g_k) = 1$. By the triangle inequality on $d_{\ell_1}$ and induction on a reduced word for $u^{-1} v$, we obtain $d_{\ell_1}(\rho(u), \rho(v)) \le \ell(u^{-1} v)$.

For the reverse inequality $\ell(u^{-1} v) \le d_{\ell_1}(\rho(u), \rho(v))$, we argue by induction on $n = d_{\ell_1}(f, g)$ where $f = \rho(u)$, $g = \rho(v)$. Set $h = f^{-1} g$, so $h(x) = f^{-1}(g(x))$. If $f \ne g$, we claim there is $u_0 \in \{0, 1, 2, 3\}$ with $h(u_0) > h(u_0 + 1)$. Indeed, if $h(0) \le h(1) \le h(2) \le h(3) \le h(4) = h(0) + 4$, then injectivity of $h$ forces $h(r) = h(0) + r$ for $r \in \{0, 1, 2, 3\}$, so

$$
4 h(0) + 6 = \sum_{r=0}^3 h(r) = \sum_{r=0}^3 \sigma_h(r) + 4 \sum_{r=0}^3 (a_h)_{\sigma_h(r)} = 6 + 0 = 6,
$$

yielding $h(r) = r$ for $r \in \{0, 1, 2, 3\}$, hence $h = \mathrm{id}$ and $f = g$, a contradiction.

Pick $k \in \{0, 1, 2, 3\}$ so that $(u_0, u_0 + 1)$ matches $(r_1, r_2)$ ($u_0 = 3$ for $k = 0$, $u_0 = k - 1$ for $k \in \{1, 2, 3\}$), and write $g(u_0) = c + 4q_0$, $g(u_0 + 1) = d + 4q_1$ with $c = \sigma_g(r_1)$, $d = \sigma_g(r_2)$. Then $g^{-1}(c) - g^{-1}(d) = 4(q_1 - q_0) - 1$, giving $\Phi_{cd}(g) = q_1 - q_0 - 1$ and $\Phi_{dc}(g) = q_0 - q_1$. Meanwhile $f^{-1}(g(u_0)) > f^{-1}(g(u_0 + 1))$ translates directly to $f^{-1}(c) - f^{-1}(d) > 4(q_1 - q_0)$, which implies $\Phi_{cd}(g) < \Phi_{cd}(f)$ (if $c < d$) and $\Phi_{dc}(f) < \Phi_{dc}(g)$ (if $d < c$). In either case the single coordinate of $\Phi$ changed by multiplying $g$ on the right by $g_k$ moves strictly closer to $\Phi(f)$ by $1$, so

$$
d_{\ell_1}(f, g g_k) = d_{\ell_1}(f, g) - 1.
$$

When $n = 0$ this forces $f = g$, so $u = v$ by Lemma 2.1 and $\ell(u^{-1} v) = 0$. When $n > 0$ the induction hypothesis gives $\ell(u^{-1} v s_k) \le n - 1$, hence $\ell(u^{-1} v) \le \ell(u^{-1} v s_k) + 1 \le n$. $\square$

**Corollary 2.3 (Exact box characterization of two-point hulls).** For all $u, v \in W(\widetilde{A}_3)$,

$$
\operatorname{Conv}(u, v) = \Bigl\{ w \in W(\widetilde{A}_3) : \forall\, 0 \le i < j \le 3,\ \min(\Phi_{ij}(\rho u), \Phi_{ij}(\rho v)) \le \Phi_{ij}(\rho w) \le \max(\Phi_{ij}(\rho u), \Phi_{ij}(\rho v)) \Bigr\}.
$$

*Proof.* By Proposition 2.2 and the $1$-dimensional identity $|x - z| + |z - y| = |x - y| \iff z \in [\min(x, y), \max(x, y)]$, an element $w$ satisfies $d(u, w) + d(w, v) = d(u, v)$ if and only if $w$ belongs to the right-hand coordinate box $\mathrm{Box}(u, v)$. The box $\mathrm{Box}(u, v)$ is immediately convex — if $x, y \in \mathrm{Box}(u, v)$ and $z \in \mathrm{Box}(x, y)$ then $z \in \mathrm{Box}(u, v)$ — and contains $\{u, v\}$, so $\operatorname{Conv}(u, v) \subseteq \mathrm{Box}(u, v)$. Conversely, every $w \in \mathrm{Box}(u, v)$ lies on a shortest path from $u$ to $v$, hence lies in $\operatorname{Conv}(u, v)$. $\square$

### 2.3. Completion of the proof of Theorem 1

For $m \ge 1$, let $L = 6m$ and define the two pure translations

$$
u_m = \psi\bigl(t_{(6m, 6m, -6m, -6m)}\bigr) = t_1^{6m}, \qquad v_m = \psi\bigl(t_{(12m, -12m, 12m, -12m)}\bigr) = t_2^{12m},
$$

where $\rho(t_1) = t_{(1, 1, -1, -1)}$ and $\rho(t_2) = t_{(1, -1, 1, -1)}$ (matching $t_1 = (s_0 s_3 s_1 s_2)^2$ and $t_2 = (s_2 s_0 s_3 s_1)^2$).

**Step 1 (Linear upper bound on $|\operatorname{Conv}(e, u_m)|$).** Since $\Phi(\mathrm{id}) = (-1, -1, -1, -1, -1, -1)$ and

$$
\Phi(\rho(u_m)) = (-1,\ -12m - 1,\ -12m - 1,\ -12m - 1,\ -12m - 1,\ -1),
$$

every $w \in \operatorname{Conv}(e, u_m)$ with $\rho(w) = (a, \sigma)$ satisfies $\Phi_{01}(a, \sigma) = -1$ and $\Phi_{23}(a, \sigma) = -1$. From $a_j - a_i - 1 \le \Phi_{ij} \le a_j - a_i$, this forces

$$
\delta_1 := a_0 - a_1 \in \{0, 1\}, \qquad \delta_2 := a_2 - a_3 \in \{0, 1\}.
$$

Since $a_0 + a_1 + a_2 + a_3 = 0$, we have $2(a_0 + a_2) = \delta_1 + \delta_2$, which forces $\delta_1 = \delta_2 =: \delta \in \{0, 1\}$ and completely determines $a$ from $(a_0, \delta)$:

$$
a_1 = a_0 - \delta, \qquad a_2 = -a_0 + \delta, \qquad a_3 = -a_0.
$$

Finally, $-12m - 1 \le \Phi_{02}(a, \sigma) \le -1$ together with $a_2 - a_0 - 1 \le \Phi_{02} \le a_2 - a_0$ gives $-12m - 1 \le -2a_0 + \delta$ and $-2a_0 + \delta - 1 \le -1$, hence $0 \le a_0 \le 6m + 1$. Thus the map $w \mapsto (\sigma, \delta, a_0)$ injects $\operatorname{Conv}(e, u_m)$ into $S_4 \times \{0, 1\} \times \{0, 1, \dots, 6m + 1\}$, giving

$$
|\operatorname{Conv}(e, u_m)| \le 24 \cdot 2 \cdot (6m + 2) = 48(6m + 2).
$$

**Step 2 (Linear upper bound on $|\operatorname{Conv}(e, v_m)|$).** Symmetrically,

$$
\Phi(\rho(v_m)) = (-24m - 1,\ -1,\ -24m - 1,\ 24m - 1,\ -1,\ -24m - 1).
$$

For $w \in \operatorname{Conv}(e, v_m)$ with $\rho(w) = (a, \sigma)$, the frozen coordinates $\Phi_{02} = \Phi_{13} = -1$ force $\delta := a_0 - a_2 = a_1 - a_3 \in \{0, 1\}$ and $a_2 = a_0 - \delta$, $a_1 = -a_0 + \delta$, $a_3 = -a_0$; the bound $-24m - 1 \le \Phi_{01} \le -1$ gives $0 \le a_0 \le 12m + 1$. Hence

$$
|\operatorname{Conv}(e, v_m)| \le 24 \cdot 2 \cdot (12m + 2) = 48(12m + 2).
$$

**Step 3 (Cubic lower bound on $|\operatorname{Conv}(u_m, v_m)|$).** For every $(p, q, r) \in \{0, 1, \dots, m\}^3$, consider the pure translation $w_{p,q,r} := \psi(t_a)$ with

$$
a = (9m + p,\ -3m + q,\ 3m + r,\ -9m - p - q - r) \in Q(A_3).
$$

Its six coordinates $\Phi_{ij}(t_a) = a_j - a_i - 1$ satisfy:

- $\Phi_{01} = -12m + q - p - 1 \in [-24m - 1,\ -1]$,
- $\Phi_{02} = -6m + r - p - 1 \in [-12m - 1,\ -1]$,
- $\Phi_{03} = -18m - 2p - q - r - 1 \in [-24m - 1,\ -12m - 1]$,
- $\Phi_{12} = 6m + r - q - 1 \in [-12m - 1,\ 24m - 1]$,
- $\Phi_{13} = -6m - p - 2q - r - 1 \in [-12m - 1,\ -1]$,
- $\Phi_{23} = -12m - p - q - 2r - 1 \in [-24m - 1,\ -1]$.

Each coordinate lies in the interval between $\Phi_{ij}(\rho u_m)$ and $\Phi_{ij}(\rho v_m)$, so $w_{p,q,r} \in \operatorname{Conv}(u_m, v_m)$ by Corollary 2.3. Since $(p, q, r) \mapsto w_{p,q,r}$ is injective (recovering $p, q, r$ from $a_0, a_1, a_2$), we obtain

$$
|\operatorname{Conv}(u_m, v_m)| \ge (m + 1)^3.
$$

**Step 4 (Contradiction).** At $m = 200000$,

$$
|\operatorname{Conv}(e, u_m)| \cdot |\operatorname{Conv}(e, v_m)| \le 48(1200002) \cdot 48(2400002) = 6{,}635{,}536{,}588{,}809{,}216 < 8{,}000{,}120{,}000{,}600{,}001 = (m + 1)^3 \le |\operatorname{Conv}(u_m, v_m)|.
$$

Thus $\operatorname{Cay}(W(\widetilde{A}_3), S)$ fails the hull property and consequently fails the strong hull property.

**Step 5 (Exact small-scale witnesses).** Exact connected BFS enumeration of the $\Phi$-boxes (independently verified against brute-force geodesic closure in `verify.py`) yields the exact linear counts $|\operatorname{Conv}(e, t_1^L)| = 12L$ and $|\operatorname{Conv}(e, t_2^L)| = 12L + 1$ for $L \ge 1$, giving the concrete witnesses $(t_1^5, t_2^{10})$ with $60 \cdot 121 = 7260 < 7921 = |\operatorname{Conv}(t_1^5, t_2^{10})|$ (ordinary hull failure) and $(t_1^8, t_2^8)$ with $96 \cdot 97 = 9312 < 9825 = |\operatorname{Conv}(e, t_1^8, t_2^8)|$ (symmetric strong hull failure). $\square$

---

## 3. Proof of Theorem 2 (All Irreducible Affine Coxeter Groups of Rank $\ge 4$)

Let $(W_{\mathrm{aff}}, S)$ be any irreducible affine Coxeter group of rank $n + 1 \ge 4$, so its finite crystallographic root system $\Phi$ has rank $n \ge 3$ in Euclidean space $E \cong \mathbb{R}^n$, with simple roots $\Delta = \{\alpha_1, \dots, \alpha_n\}$, positive roots $\Phi^+$, Cartan matrix $C_{ij} = \langle \alpha_i, \alpha_j^\vee \rangle$, coroot lattice $Q^\vee = \bigoplus_{i=1}^n \mathbb{Z}\alpha_i^\vee$, and fundamental coweights $\omega_1^\vee, \dots, \omega_n^\vee$ satisfying $\langle \alpha_i, \omega_j^\vee \rangle = \delta_{ij}$. Then $W_{\mathrm{aff}} \cong Q^\vee \rtimes W_0$ acts faithfully and simply transitively on the alcoves of the affine hyperplane arrangement $\mathcal{H} = \{ H_{\alpha, k} : \alpha \in \Phi^+,\ k \in \mathbb{Z} \}$, where $H_{\alpha, k} = \{ x \in E : \langle \alpha, x \rangle = k \}$ and the fundamental alcove is $A_0 = \{ x \in E : \forall \alpha \in \Phi^+,\ 0 < \langle \alpha, x \rangle < 1 \}$.

By Tits' convexity theorem (Theorem 2.4 / Proposition 2.5 of Gaetz–Gao), for any $u, v \in W_{\mathrm{aff}}$, an element $w \in W_{\mathrm{aff}}$ belongs to $\operatorname{Conv}(u, v)$ if and only if no affine hyperplane $H_{\alpha, k}$ separates $w(A_0)$ from both $u(A_0)$ and $v(A_0)$. Equivalently, letting $I_\alpha(x) := \lfloor \langle \alpha, x(A_0) \rangle \rfloor$ denote the integer strip index $\langle \alpha, x(A_0) \rangle \subset (I_\alpha(x), I_\alpha(x) + 1)$, we have

$$
w \in \operatorname{Conv}(u, v) \iff \forall \alpha \in \Phi^+,\ \min(I_\alpha(u), I_\alpha(v)) \le I_\alpha(w) \le \max(I_\alpha(u), I_\alpha(v)).
$$

For a pure translation $t_q$ ($q \in Q^\vee$), we have $I_\alpha(t_q) = \langle \alpha, q \rangle$ for every $\alpha \in \Phi^+$.

**Universal interior-node construction.** Since the Dynkin diagram of $\Phi$ is a connected tree on $n \ge 3$ vertices, it has a vertex $b \in \{1, \dots, n\}$ of degree $\deg(b) \ge 2$ (and $\deg(b) = 3$ for $D_n$ ($n \ge 4$), $E_6, E_7, E_8$). Set $c_0 := |\det C| \in \mathbb{Z}_{>0}$, so $d_1 := c_0 \omega_b^\vee \in Q^\vee$, and set

$$
d_2 := s_b(d_1) = d_1 - c_0 \alpha_b^\vee \in Q^\vee.
$$

For every positive root $\alpha = \sum_{i=1}^n c_i \alpha_i \in \Phi^+$ ($c_i \in \mathbb{Z}_{\ge 0}$):

1. $\langle \alpha, d_1 \rangle = c_0 c_b$, so $\Phi_{d_1}^\perp := \{ \alpha \in \Phi : \langle \alpha, d_1 \rangle = 0 \}$ is the parabolic root subsystem spanned by $\Delta \setminus \{\alpha_b\}$, which has rank $n - 1$. Likewise $\Phi_{d_2}^\perp = s_b(\Phi_{d_1}^\perp)$ has rank $n - 1$.
2. $\langle \alpha, d_2 \rangle = \langle s_b(\alpha), d_1 \rangle = c_0 \bigl(-c_b + \sum_{j \sim b} (-C_{jb}) c_j\bigr)$, where $j \sim b$ ranges over the $\deg(b)$ neighbors of $b$ in the Dynkin diagram and every $-C_{jb} \in \{1, 2, 3\}$ is strictly positive.
3. Since $c_i \ge 0$, a positive root $\alpha$ lies in $\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp$ if and only if $c_b = 0$ and $\sum_{j \sim b} (-C_{jb}) c_j = 0$, which holds if and only if $c_b = 0$ and $c_j = 0$ for every neighbor $j \sim b$. Thus $\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp$ lies in the span of $\Delta \setminus (\{b\} \cup N(b))$, so

$$
\operatorname{rank}(\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp) \le n - 1 - \deg(b) \le n - 3.
$$

Consequently, the free subspace $F := (\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp)^\perp \subseteq E$ has dimension

$$
\dim F = n - \operatorname{rank}(\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp) \ge \deg(b) + 1 \ge 3.
$$

Fix the integer constant $K := 1 + \max_{\alpha \in \Phi^+} |\langle \alpha, d_1 \rangle|$. Then for every $\alpha \in \Phi^+ \setminus (\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp)$, we have $\langle \alpha, K d_2 - d_1 \rangle \ne 0$: if $\langle \alpha, d_2 \rangle \ne 0$ then $|\langle \alpha, K d_2 - d_1 \rangle| \ge K - (K - 1) = 1$, while if $\langle \alpha, d_2 \rangle = 0$ then $\langle \alpha, d_1 \rangle \ne 0$.

Now let $u_L := t_{L d_1}$ and $v_L := t_{K L d_2}$ for integers $L \ge 1$.

**Linear upper bounds $|\operatorname{Conv}(e, u_L)| = O(L)$ and $|\operatorname{Conv}(e, v_L)| = O(L)$.** Every $w \in \operatorname{Conv}(e, u_L)$ satisfies $I_\alpha(w) = 0$, i.e. $0 < \langle \alpha, w(A_0) \rangle < 1$, for all $n - 1$ linearly independent roots $\alpha \in \Delta \setminus \{\alpha_b\}$, and $0 < \langle \alpha_b, w(A_0) \rangle < c_0 L + 1$. Thus the union of alcoves $\bigcup_{w \in \operatorname{Conv}(e, u_L)} w(A_0)$ is contained in a parallelotope of Euclidean volume $O(L)$. Since every alcove has the same positive volume $\operatorname{vol}(A_0)$, we obtain $|\operatorname{Conv}(e, u_L)| = O(L)$, and identically $|\operatorname{Conv}(e, v_L)| = O(L)$.

**Lower bound $|\operatorname{Conv}(u_L, v_L)| = \Omega(L^{\dim F}) \ge \Omega(L^3)$.** Because $F$ is defined over $\mathbb{Q}$ by integer linear equations $\langle \alpha, x \rangle = 0$, $Q^\vee \cap F$ is a lattice of full rank $\dim F$ in $F$. Consider the scaled convex polytope in $F$ centered at the midpoint $x_L = \frac{1}{2} L (d_1 + K d_2) \in F$:

$$
P_L := \bigl\{ x \in F : \forall \alpha \in \Phi^+ \setminus (\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp),\ \min(\langle \alpha, L d_1 \rangle, \langle \alpha, K L d_2 \rangle) \le \langle \alpha, x \rangle \le \max(\langle \alpha, L d_1 \rangle, \langle \alpha, K L d_2 \rangle) \bigr\}.
$$

For every $\alpha \in \Phi^+ \setminus (\Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp)$, the midpoint $x_L$ lies at signed distance $\frac{1}{2} L |\langle \alpha, K d_2 - d_1 \rangle| \ge \frac{1}{2} L$ from both boundary hyperplanes. Hence $P_L$ contains an $F$-ball of radius $r_0 L$ around $x_L$ for a constant $r_0 > 0$ depending only on $\Phi$, and therefore contains $\Omega(L^{\dim F})$ lattice points $q \in Q^\vee \cap F$. For every such $q$, we have $I_\alpha(t_q) = \langle \alpha, q \rangle = 0 = I_\alpha(u_L) = I_\alpha(v_L)$ for $\alpha \in \Phi_{d_1}^\perp \cap \Phi_{d_2}^\perp$ and $\langle \alpha, q \rangle$ lies between $\langle \alpha, L d_1 \rangle$ and $\langle \alpha, K L d_2 \rangle$ for all other $\alpha \in \Phi^+$; thus $t_q \in \operatorname{Conv}(u_L, v_L)$.

Therefore $|\operatorname{Conv}(e, u_L)| \cdot |\operatorname{Conv}(e, v_L)| = O(L^2)$ while $|\operatorname{Conv}(u_L, v_L)| = \Omega(L^{\dim F}) \ge \Omega(L^3)$, violating the ordinary hull property (and hence the strong hull property) for all sufficiently large $L$. (Notice that Theorem 1 for $\widetilde{A}_3$ is precisely this universal construction at the middle node $b = 2$ of $A_3$, where $d_1 = 2 \omega_2^\vee = (1, 1, -1, -1)$ and $d_2 = s_2(d_1) = (1, -1, 1, -1)$.) $\square$

---

## 4. Literature and Prior-Art Check

We checked arXiv (`2020–2026-11`) for all papers citing or extending Gaetz–Gao (`arXiv:2012.06841v2`):

- **Gaetz–Gao (`arXiv:2012.06841v2`, 2020/2022):** Proved Conjecture 1.2 for $S_n$ ($A_{n-1}$), $B_n$, dihedral groups $I_2(m)$ (including $I_2(\infty) = \widetilde{A}_1$), and all right-angled Coxeter groups; computer-verified $G_2, H_3, D_4, F_4$.
- **Ziming Liu (`arXiv:2505.15871v4`, May 2025, *Strong hull property of affine Coxeter groups of rank 3*):** Proved Conjecture 1.2 for all irreducible affine Coxeter groups of rank $3$ ($\widetilde{A}_2, \widetilde{C}_2, \widetilde{G}_2$).
- **Gaetz–Gao (`arXiv:2610.22857v1`, Oct 2026, *Separable elements and Bruhat orders*):** Proved the special case of the hull inequality when $\operatorname{Conv}(u, v) = W$ (finite $W$) and cited Conjecture 1.2 of `arXiv:2012.06841` as open in general.

No counterexample to either the strong hull property or the hull property in any Coxeter group appeared in the literature prior to this disproof. Note that the conjecture remains open for **finite** Coxeter groups outside types $A_n, B_n, I_2(m), H_3, D_4, F_4$ (e.g., $D_n$ for $n \ge 5$, $H_4, E_6, E_7, E_8$).

---

## 5. Verification Summary

### 5.1. End-to-End Lean 4 Verification (`lean/Conjectures/YiboGaoCoxeterGeodesicHull.lean`)

The entire proof of Theorem 1 (disproving both `HasStrongHullProperty` and `HasHullProperty` for the undirected right Cayley graph `cayleyGraph cs3` of `W(A₃~) := A3TildeMatrix.Group`) is formalized from Mathlib's `SimpleGraph.dist`, `Set.encard`, and `CoxeterMatrix.toCoxeterSystem` with zero `sorry`, zero `native_decide`, and only standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

- `YiboGaoCoxeterGeodesicHull.cayleyGraph_dist_eq_l1Dist`: exact isometric embedding of `Cay(W(A₃~), S)` into `(ℤ⁶, ℓ₁)`.
- `YiboGaoCoxeterGeodesicHull.convexHull_pair_eq_phiBox`: exact $\Phi$-box characterization of two-point geodesic convex hulls.
- `YiboGaoCoxeterGeodesicHull.AffPerm4.encard_convexHull_one_uFamily_le`, `encard_convexHull_one_vFamily_le`, `le_encard_convexHull_uFamily_vFamily`: symbolic $O(m)$ upper bounds and $(m+1)^3$ lower bound for all $m \in \mathbb{N}$.
- `YiboGaoCoxeterGeodesicHull.not_hasHullProperty_A3Tilde : ¬ HasHullProperty (cayleyGraph cs3)`.
- `YiboGaoCoxeterGeodesicHull.not_hasStrongHullProperty_A3Tilde : ¬ HasStrongHullProperty (cayleyGraph cs3)`.
- `YiboGaoCoxeterGeodesicHull.counterexample_exists`: existential refutation of Conjecture 1.2 and the hull property.

**Scope note:** Theorem 1 (full refutation of Conjecture 1.2 and the hull property in type $\widetilde{A}_3$) is completely verified in Lean 4; Theorem 2 (the general affine dichotomy in rank at least $4$) and the exact small-scale counts at $L = 8$ and $(L_1, L_2) = (5, 10)$ are proved in Sections 2–3 above and cross-checked with exact zero-float arithmetic in `verify.py`.

### 5.2. Exact Zero-Float Script (`results/yibo-gao-coxeter-geodesic-hull/verify.py`)

`verify.py` uses only exact integer and `fractions.Fraction` arithmetic to check:

1. Equivalence of `AffPerm4` and the exact integer $4 \times 4$ Tits reflection representation of $W(\widetilde{A}_3)$ on the full radius $6$ Cayley ball ($195$ elements) plus $1000$ pairwise $\ell_1$ distance checks.
2. Exact agreement between independent iterative geodesic closure and $\Phi$-box enumeration at $L = 1$ ($|\operatorname{Conv}(e, t_1, t_2)| = 53$).
3. Exact concrete counterexamples in $W(\widetilde{A}_3)$: $(t_1^5, t_2^{10})$ ($60 \cdot 121 = 7260 < 7921$) and $(t_1^8, t_2^8)$ ($96 \cdot 97 = 9312 < 9825$).
4. The universal interior-node criterion ($\dim F = \deg(b) + 1 \ge 3$) across $12$ irreducible affine root systems ($\widetilde{A}_3, \widetilde{A}_4, \widetilde{B}_3, \widetilde{B}_4, \widetilde{C}_3, \widetilde{C}_4, \widetilde{D}_4, \widetilde{D}_5, \widetilde{F}_4, \widetilde{E}_6, \widetilde{E}_7, \widetilde{E}_8$).
5. Negative and mutation-rejection controls: exhaustive verification of the strong hull property on all $576$ pairs $(e, u, v)$ in finite $W(A_3) = S_4$, non-violation at $L = 1$ in $W(\widetilde{A}_3)$, and rejection of a corrupted $s_0$ generator by the Coxeter-relation checker.

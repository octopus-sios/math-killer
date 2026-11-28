# Manickam–Miklós–Singhi Conjecture: Universal $n \ge 7k$, Full Resolution of Milojević–Sudakov Conjectures 1 & 3 on $[0, 1/3]$, and Exact $k = 8$ Certificates

## Summary of Results

Let $n, k \in \mathbb Z_{\ge 1}$ with $k \le n$. For a real vector $x = (x_1, \dots, x_n) \in \mathbb{R}^n$ with $\sum_{i=1}^n x_i \ge 0$, let $g(x; k) = \left|\left\{ S \in \binom{[n]}{k} : \sum_{i \in S} x_i \ge 0 \right\}\right|$, and let $g(n, k) = \min_{\sum x_i \ge 0} g(x; k)$. The **Manickam–Miklós–Singhi (MMS) Conjecture** (1988; Conjecture 1.1 in `SOURCE.tex`, [Chowdhury–Sarkis–Shahriari, arXiv:1403.1844v4](https://arxiv.org/abs/1403.1844)) states that $g(n, k) = \binom{n-1}{k-1}$ whenever $n \ge 4k$, with equality attained by the star vector $(n-1, -1, \dots, -1)$.

This package establishes three independent breakthroughs across the universal linear regime, the June 2026 weighted Bernoulli exceedance conjectures of [Milojević–Sudakov (arXiv:2606.30287v1)](https://arxiv.org/abs/2606.30287), and the first open small $k$ frontier $k = 8$:

| Pillar | Result Established | Previous World Record | Verification Tier |
| :--- | :--- | :--- | :--- |
| **I. Universal Linear MMS** | $g(n, k) = \binom{n-1}{k-1}$ for **all** $n \ge 7k$, $k \ge 1$ (no finite $k$ cutoff, no divisibility or support restriction), plus equality characterization (top star) and a 10-line elementary backup for $n \ge 3k^2$. | Linear: $n > 10^{46} k$ ([Pokrovskiy, JCTA 2015 / arXiv:1308.2176](https://arxiv.org/abs/1308.2176)). Quadratic: $n \ge 8k^2$ ([Chowdhury–Sarkis–Shahriari, arXiv:1403.1844v4](https://arxiv.org/abs/1403.1844)). | **Unconditional Lean 4 `v4.35.0` kernel-verified** (`ManickamMiklosSinghi.mms_seven_k`, 29 `SevenK*` modules, zero `sorry`, standard axioms only) + independent exact rational replay (`verify_universal.py`, `<0.3s`, zero floats); equality characterization and $n \ge 3k^2$ backup proved analytically in Sections 1.5–1.6. |
| **II. Milojević–Sudakov Conjectures 1 & 3 (June 2026)** | **Complete resolution** of Conjecture 1 (`conj:prob`): for all $w_i \ge 0$, $\sum w_i = 1$, independent $v_i \sim \mathrm{Ber}(p)$, $\Pr\!\left(\sum w_i v_i \ge p\right) \ge p$ for **all** $p \in [0, 1/3]$ (sharp: fails for $p > 1/3$), with strict surplus $\Pr(X > p) > p$ whenever $p \in (0, 1/3)$ and $\max_i w_i \le p$. **Complete resolution** of Conjecture 3 (`q:MMS_variant`): bounded-support restricted MMS holds for all $\varepsilon > 0$, $C > 0$, and $n \ge \max((3+\varepsilon)k, n_0(C,\varepsilon))$. | $p \le 10^{-46}$ and $c = 10^{46}$ ([Milojević–Sudakov, June 2026, arXiv:2606.30287v1](https://arxiv.org/abs/2606.30287), via Pokrovskiy 2015). | $[0, 1/7]$ and all unit fractions $p = 1/q$ (including endpoint $p = 1/3$) **100% Lean 4 kernel-verified** (`BernoulliOneSeventh.lean`); $[1/7, 1/3)$ certified by zero-float integer / `int128` replay (`bernoulli_constants.py`, `bernoulli_extension.py` + `prefix.cpp`, `~41s`). |
| **III. Exact $k = 8$ Frontier** | Sharp lower bound $f(8) \ge 26$ via $(3^{22}, (-22)^3)$ ($319{,}770 < \binom{24}{7} = 346{,}104$); exact rational Farkas certificates for $g(18,8)=12{,}870$, $g(28,8)=888{,}030$, $g(30,8)=1{,}560{,}780$, $g(32,8)=2{,}629{,}575$; new sign-stratified spectral (`SPEC1`) certificate for **$g(33,8) = \binom{32}{7} = 3{,}365{,}856$** (propagating to all $n \equiv 1 \pmod 8$, $n \ge 33$). | $k \le 7$ settled by [Hartke–Stolee (EJC 2014 / arXiv:1302.3636)](https://arxiv.org/abs/1302.3636); even $n \ge 28$ at $k=8$ proved in [Džavoronok (arXiv:2605.22708v2)](https://arxiv.org/abs/2605.22708), Prop. 4.4. First odd base $n=33$ for $k=8$ newly certified here. | `f(8) >= 26`, Chowdhury step, and Farkas tree soundness **Lean 4 kernel-verified** (`Foundation.lean`); all 5 exact $k=8$ certificates replayed in `<0.7s` (zero floats) by `verify_cert.py` and `cover_exact.py`. |

**Scope honesty.** Pillar I does **not** claim the full conjectured threshold $n \ge 4k$ for unrestricted real vectors (it establishes $n \ge 7k$, reducing the best known linear constant from $10^{46}$ to $7$). Pillar III does **not** claim all residue classes for $k = 8$: our certified star bases $n \in \{28, 30, 32, 33\}$ close $n \equiv 0, 1, 4, 6 \pmod 8$ for $n \ge 28$ (with $n = 33$ newly certified here via `SPEC1`), leaving the four residue classes $n \equiv 2, 3, 5, 7 \pmod 8$ below the universal $n \ge 56$ threshold ($n \in \{26, 27, 29, 31, 34, 35, 37, 39, 42, 43, 45, 47, 50, 51, 53, 55\}$) open by self-contained certificates in this package (with $n \in \{34, 42, 50\}$ already covered externally by [Džavoronok, arXiv:2605.22708v2](https://arxiv.org/abs/2605.22708), Prop. 4.4). Pillar II **completely resolves** both Conjecture 1 and Conjecture 3 of Milojević–Sudakov over their entire sharp domains.

---

## Part I: Universal Manickam–Miklós–Singhi Theorem for All $n \ge 7k$

**Theorem I.1 (Universal $n \ge 7k$ MMS and Equality).** Let $n, k \in \mathbb Z_{\ge 1}$ with $n \ge 7k$. For every $x = (x_1, \dots, x_n) \in \mathbb{R}^n$ with $\sum_{i=1}^n x_i \ge 0$, at least $\binom{n-1}{k-1}$ of the $k$-element subsets of $[n]$ have nonnegative sum. Moreover, if equality holds, then the family of nonnegative $k$-subsets is the star $\{S \in \binom{[n]}{k} : i_0 \in S\}$ centered at some maximum coordinate $x_{i_0} = \max_i x_i$.

**Proof overview.** Instead of discarding a single fixed negative star set and paying an exponential in $k^2/n$ counting loss, we couple **all** negative star sets to nonnegative sets off the star via uniform disjoint sampling on the Johnson scheme. An approximate MMS lower bound in the complement together with the second singular value of the disjoint-pair operator forces a positive density of negative sets in the top star. Conditional variance then caps the largest positive coordinate $A = \max_i x_i$, while convexity bounds the most negative coordinate $-h = \min_i x_i$. Evaluating a family of lower quartics $L(s) \le \mathbf 1_{s \ge 0}$ against the exact four slice moments upgrades the star-normalized density $R = \Pr(Y \ge 0) / (k/n)$ in three steps:

$$
n \ge 5k \implies R > \frac{69}{100}, \qquad n \ge 6k \implies R \ge \frac{87}{100}, \qquad n \ge 7k \implies R \ge 1.
$$

All terminating decimals in the certificate tables below denote exact rationals.

### 1.1 Normalization and Exact Slice Moments

Replacing $x_i$ by $x_i - \frac{1}{n}\sum_{j=1}^n x_j$ does not increase any $k$-subset sum, so we may assume $\sum_{i=1}^n x_i = 0$. The case $x = 0$ is immediate (all $\binom{n}{k}$ sums are $0$), as is $k = 1$ (some $x_i \ge 0$ gives $\ge 1 = \binom{n-1}{0}$ nonnegative $1$-subsets). Assume $k \ge 2$ and $n \ge 5k$, and rescale so that $\sum_{i=1}^n x_i^2 = 1$. Order $x_1 \ge \dots \ge x_n$, set $A = x_1 > 0$ and $-h = x_n < 0$, and write $S_j = \sum_{i=1}^n x_i^j$ and $p = k/n$. Let $Y = \sum_{i \in S} x_i$ for a uniformly random $S \in \binom{[n]}{k}$, and define

$$
v = \frac{n-k}{n-1}, \qquad g = \frac{n-2k}{n-2}, \qquad w = \frac{(k-1)(n-k-1)}{(n-2)(n-3)}, \qquad R = \frac{\Pr(Y \ge 0)}{p}.
$$

**Lemma I.2 (Exact Slice Moments).** For every $k \ge 2$, $n \ge 4$, and centered unit vector $x$ ($S_1 = 0, S_2 = 1$),

$$
\mathbb{E}[Y] = 0, \qquad \mathbb{E}[Y^2] = pv, \qquad \mathbb{E}[Y^3] = pvg S_3, \qquad \mathbb{E}[Y^4] = pv B, \qquad B = 3w + (1 - 6w) S_4. \tag{1}
$$

Moreover, for every $i \in [n]$, $\mathbb{E}[Y \cdot \mathbf 1_{i \in S}] = pv x_i$.

*Proof.* For $1 \le j \le 4$, any $j$ distinct coordinates are simultaneously included in $S$ with probability $\pi_j = (k)\mathstrut_j / (n)\mathstrut_j$, where $(m)\mathstrut_j = m(m-1)\cdots(m-j+1)$. Expanding $(\sum_{i \in S} x_i)^r$ and simplifying with $S_1 = 0$ and $S_2 = 1$:
- $\mathbb{E}[Y] = \pi_1 S_1 = 0$ and $\mathbb{E}[Y \cdot \mathbf 1_{i \in S}] = \pi_1 x_i + \pi_2 \sum_{j \neq i} x_j = (\pi_1 - \pi_2) x_i = pv x_i$.
- $\mathbb{E}[Y^2] = \pi_1 S_2 + \pi_2 (S_1^2 - S_2) = \pi_1 - \pi_2 = pv$.
- $\mathbb{E}[Y^3] = (\pi_1 - 3\pi_2 + 2\pi_3) S_3 = pvg S_3$.
- For $\mathbb{E}[Y^4]$, expanding by partition type of $4$-tuples of indices gives:
  - $1$ distinct index: $\pi_1 S_4$;
  - $2$ distinct indices ($3+1$ and $2+2$): $\pi_2 (4(-S_4) + 3(1 - S_4)) = \pi_2 (3 - 7S_4)$;
  - $3$ distinct indices ($2+1+1$): $6\pi_3 (2S_4 - 1) = \pi_3 (12 S_4 - 6)$;
  - $4$ distinct indices: $\pi_4 (3 - 6S_4)$.
  Summing yields constant term $3(\pi_2 - 2\pi_3 + \pi_4) = 3pvw$ and $S_4$-coefficient $(\pi_1 - \pi_2) - 6(\pi_2 - 2\pi_3 + \pi_4) = pv(1 - 6w)$. Note that $\pi_3 = \pi_4 = 0$ for $k = 2$ and $\pi_4 = 0$ for $k = 3$, so all identities hold for $k \ge 2$. $\square$

We use the elementary parameter bounds $1 - p \le v \le 1$ and $0 \le w \le p(1-p) \le 4/25 < 1/6$ for $p \le 1/5$. Indeed, $w \le p(1-p)$ clears to $p(1-p)(5n - 6) \le n - 1$, which holds since $p(1-p) \le 4/25 < 1/5$ and $5n - 6 < 5(n-1)$.

### 1.2 Starting Density: $R > 69/100$ for All $n \ge 5k$

**Lemma I.3.** For $k \ge 2$ and $n \ge 5k$, every vector with $\sum_{i=1}^n x_i \ge 0$ satisfies $R > 69/100$.

*Proof.* Assume $x$ is centered and unit-norm (the constant case gives $R = 1/p \ge 5$). Set $Y_+ = \max(Y, 0)$, $Y_- = \max(-Y, 0)$, $m = \mathbb{E}[Y_+] = \mathbb{E}[Y_-]$, $V = \mathbb{E}[Y^2] = pv$, and $a = \mathbb{E}[Y_+^2] / V \in (0, 1)$. For each $i \in [n]$,

$$
pv x_i = \mathbb{E}[Y \mathbf{1}_{i \in S}] \le \mathbb{E}[Y_+] = m, \qquad -pv x_i = \mathbb{E}[(-Y) \mathbf{1}_{i \in S}] \le \mathbb{E}[Y_-] = m,
$$

so $pv H \le m$ where $H = \max_i |x_i|$. By Cauchy–Schwarz, $m^2 = (\mathbb{E}[Y_+ \mathbf 1_{Y \ge 0}])^2 \le \Pr(Y \ge 0) \mathbb{E}[Y_+^2] = R p \cdot a V$, hence $H^2 \le (R/v) a = s a$ where $s = R/v$, and therefore $S_4 = \sum x_i^4 \le H^2 \sum x_i^2 = H^2 \le s a$.

By Hölder's inequality for any $Z \ge 0$, $(\mathbb{E}[Z^2])^3 \le (\mathbb{E}[Z])^2 \mathbb{E}[Z^4]$. Applying this to $Y_+$ and $Y_-$ and summing gives

$$
V^3 \bigl(a^3 + (1-a)^3\bigr) \le m^2 \bigl(\mathbb{E}[Y_+^4] + \mathbb{E}[Y_-^4]\bigr) = m^2 \mathbb{E}[Y^4] \le (R p \cdot a V)(V B) = s a B V^3.
$$

Dividing by $a^2 V^3$ and substituting $B = 3w + (1 - 6w) S_4 \le 3w + (1 - 6w) s a$ yields, with $z = 1/a > 0$,

$$
z^2 - 3z + 3 = \frac{a^3 + (1-a)^3}{a^2} \le \frac{s B}{a} \le 3w s z + (1 - 6w) s^2.
$$

Completing the square in $z$ (minimum at $z = (3 + 3ws)/2$) gives the necessary condition

$$
\left(1 - 6w + \frac{9}{4} w^2\right) s^2 + \frac{9}{2} w s \ge \frac{3}{4}. \tag{2}
$$

The left-hand side is increasing in $s \ge 0$ and convex in $w \in [0, 1/6]$ (its second $w$-derivative is $\frac{9}{2} s^2 \ge 0$). At $s = 69/80$, the endpoint values at $w = 0$ and $w = 1/6$ are $(69/80)^2 = 4761/6400 < 4800/6400 = 3/4$ and $\frac{1}{16}(69/80)^2 + \frac{3}{4}(69/80) = 70881/102400 < 76800/102400 = 3/4$. Hence $s > 69/80$, and since $v \ge 1 - p \ge 4/5$, we obtain $R = v s > (4/5)(69/80) = 69/100$. $\square$

### 1.3 Disjoint-Pair Mixing on the Johnson Scheme

**Lemma I.4 (Disjoint-Pair Mixing).** On an $m_0$-element ground set, let $(U, D)$ be a uniformly random ordered disjoint pair of subsets of sizes $a_0, b_0 \ge 1$ with $a_0 + b_0 \le m_0$. For any families $\mathcal{B} \subseteq \binom{[m_0]}{a_0}$ and $\mathcal{E} \subseteq \binom{[m_0]}{b_0}$ of densities $b, e \in [0, 1]$,

$$
\Pr(U \in \mathcal{B},\, D \in \mathcal{E}) \le b e + \rho \sqrt{b(1-b)e(1-e)}, \qquad \rho^2 = \frac{a_0 b_0}{(m_0 - a_0)(m_0 - b_0)}. \tag{3}
$$

*Proof.* Let $K : L^2\!\left(\binom{[m_0]}{b_0}\right) \to L^2\!\left(\binom{[m_0]}{a_0}\right)$ send $f(D)$ to $\mathbb{E}[f(D) \mid U]$ under uniform probability measures. For any $J \subseteq [m_0]$ of size $j \le b_0$,

$$
(K \mathbf{1}_{J \subseteq D})(U) = \frac{(b_0)_j}{(m_0 - a_0)_j} \mathbf{1}_{J \cap U = \emptyset} = \frac{(b_0)_j}{(m_0 - a_0)_j} \sum_{L \subseteq J} (-1)^{|L|} \mathbf{1}_{L \subseteq U}.
$$

Modulo the span $\mathcal F_{j-1}$ of inclusion indicators of degree $\le j-1$, only the term $L = J$ survives (and vanishes if $j > a_0$). Applying $K^{\ast}$ similarly shows that the self-adjoint operator $K^{\ast} K$ preserves the degree filtration $\mathcal F_0 \subset \mathcal F_1 \subset \dots \subset \mathcal F_{b_0} = L^2\!\left(\binom{[m_0]}{b_0}\right)$, acting on $\mathcal F_j / \mathcal F_{j-1}$ by the scalar

$$
\lambda_j = \frac{(a_0)_j (b_0)_j}{(m_0 - a_0)_j (m_0 - b_0)_j} \quad (j \le \min(a_0, b_0)), \qquad \lambda_j = 0 \quad (j > a_0).
$$

Since $a_0 + b_0 \le m_0$, for $1 \le i < \min(a_0, b_0)$ we have $(a_0 - i)(b_0 - i) \le (m_0 - a_0 - i)(m_0 - b_0 - i)$, so $\lambda_1 \ge \lambda_2 \ge \dots \ge 0$. Because $\mathcal F_0$ is the constant functions, every centered $f$ satisfies $\lVert K f \rVert_2^2 = \langle f, K^{\ast} K f \rangle \le \lambda_1 \lVert f \rVert_2^2 = \rho^2 \lVert f \rVert_2^2$. Applying Cauchy–Schwarz to the centered indicators of $\mathcal{B}$ and $\mathcal{E}$ yields (3). $\square$

Now suppose an approximate lower bound $R \ge r_c$ is already known for all lists of size $n - k$ (with subset size $k$). Test a target $r \in (0, 1]$ at size $n$ by assuming $R < r$. Define the bad top-star density $b = \Pr(Y < 0 \mid 1 \in S)$, the off-star good density $e = \Pr(Y \ge 0 \mid 1 \notin S)$, and $t = p / (1 - p) = k / (n - k)$. Because $\Pr(Y \ge 0) = p(1 - b) + (1 - p) e < p r$, we have $b > 1 - r$ and $e < t(b + r - 1)$.

Sample a uniform disjoint pair $(U, D)$ of sizes $a_0 = k - 1$ and $b_0 = k$ from the $m_0 = n - 1$ remaining elements $\{2, \dots, n\}$. Whenever $U$ is bad ($x_1 + \sum_{i \in U} x_i < 0$), the complement $[n] \setminus (\{1\} \cup U)$ has size $n - k$ and strictly positive sum; by the $r_c$-guarantee at size $n - k$, $\Pr(D \text{ good} \mid U) \ge t r_c$. Hence $\Pr(U \text{ bad},\, D \text{ good}) \ge b t r_c$. On the other hand, Lemma I.4 gives $\rho^2 = \frac{(k-1)k}{(n-k)(n-k-1)} \le \frac{k^2}{(n-k)^2} = t^2$ (since $n \ge 2k$). Dividing (3) by $bt$ and using $1 - e \le 1$ and $e < t(b + r - 1)$ yields

$$
r_c \le b + r - 1 + \sqrt{\frac{t(1 - b)(b + r - 1)}{b}}. \tag{4}
$$

**Lemma I.5 (Bad-Star Density Certificate).** Let $p \le P < 1$ and $T = P / (1 - P)$. If $\beta \in (0, 1)$ satisfies

$$
y = \beta + r - 1 \in [0, r_c), \qquad \zeta = \frac{y}{\beta}, \qquad T \zeta \le 4(1 - \beta), \qquad (r_c - y)^2 > T(1 - \beta)\zeta, \tag{5}
$$

then (4) implies $b > \beta$.

*Proof.* Suppose $b \le \beta$. Since $1 - r < b \le \beta$, we have $(b + r - 1)/b = 1 - (1 - r)/b \le y/\beta = \zeta$, and $t \le T$. Thus $r_c \le b + r - 1 + \sqrt{T \zeta (1 - b)}$. Differentiating $f(b) = b + r - 1 + \sqrt{T \zeta (1 - b)}$ gives $f'(b) = 1 - \frac{\sqrt{T\zeta}}{2\sqrt{1-b}} \ge 0$ for all $b \le \beta$ by $T\zeta \le 4(1 - \beta)$. Hence $r_c \le f(\beta) = y + \sqrt{T\zeta(1 - \beta)}$, contradicting $(r_c - y)^2 > T(1 - \beta)\zeta$. $\square$

### 1.4 Coordinate Caps

Conditional on $1 \in S$, the random variable $Y = x_1 + \sum_{i \in S \setminus \{1\}} x_i$ has mean $v A$ and variance

$$
\sigma^2 = \frac{k-1}{n-1} \cdot \frac{n-k}{n-2} \left(1 - \frac{n}{n-1} A^2\right) \le pv (1 - A^2),
$$

since $(k-1)n \le k(n-2)$ and $\frac{n}{n-1} > 1$. By Cantelli's one-sided Chebyshev inequality (proved directly by Cauchy–Schwarz on $Y_+ \mathbf 1_{Y \ge 0}$), $b = \Pr(Y < 0 \mid 1 \in S) \le \frac{\sigma^2}{\sigma^2 + (v A)^2}$, so $b(vA)^2 \le (1 - b) pv (1 - A^2)$. Using $b > \beta$, $p \le P$, and $v \ge 1 - P$, any $D \ge 0$ satisfying

$$
D^2 \ge \frac{P(1 - \beta)}{(1 - P)\beta + P(1 - \beta)} \tag{6}
$$

is a valid upper cap $A \le D$.

For the minimum coordinate $-h = x_n < 0$, conditional on $n \in S$ the mean of $Y$ is $-vh$, so Jensen's inequality gives $\mathbb{E}[Y_-^2] \ge p (vh)^2$ and $m = \mathbb{E}[Y_-] \ge p v h$. Assuming $R < r$, Cauchy–Schwarz gives $\mathbb{E}[Y_+^2] \ge m^2 / (r p) \ge p v^2 h^2 / r$. Summing both bounds against $\mathbb{E}[Y^2] = pv$ gives $pv \ge pv^2 h^2 (1 + 1/r)$, i.e., $h^2 \le r / (v(1 + r))$. Hence any $H_0 > 0$ satisfying

$$
H_0^2 \ge \frac{r}{(1 - P)(1 + r)} \tag{7}
$$

is a valid cap $h \le H_0$.

### 1.5 Lower Quartics and Finite-Interval Certification

For any two positive rationals $z, u > 0$, set

$$
d = z + \frac{z(z+u)}{3z+u}, \qquad c = \frac{3z+u}{z^2(z+u)^3}, \qquad \lambda = 2u - d, \qquad I = 2ud - u^2.
$$

**Lemma I.6 (Quartic Indicator Minorant).** For all $s \in \mathbb{R}$, $L(s) := c s (s+u)^2 (d-s) \le \mathbf 1_{s \ge 0}$. Consequently,

$$
R \ge \frac{\mathbb{E}[L(Y)]}{p} = c v \bigl(I - (B + \lambda g S_3)\bigr). \tag{8}
$$

*Proof.* For $s < 0$, either $s \le d$ gives $s(d-s) \le 0$ so $L(s) \le 0 = \mathbf 1_{s \ge 0}$. For $s \ge 0$, $L(s) \le 0 < 1$ if $s \ge d$, while on $[0, d]$ the polynomial $L(s)$ satisfies

$$
L'(s) = c (s+u) \bigl(-4s^2 + (3d - 2u)s + ud\bigr).
$$

Substituting $d = z + \frac{z(z+u)}{3z+u}$ shows that $s = z$ is the unique positive root of $L'$, and $L(z) = 1$. Hence $L(s) \le \mathbf 1_{s \ge 0}$ everywhere. Expanding $L(s) = c (u^2 d s + I s^2 - \lambda s^3 - s^4)$ and taking expectation via (1) gives (8). $\square$

In a density band $\ell \le p \le P$ (with $k \ge 2$), define

$$
W = P(1 - P), \qquad G_- = 1 - 2P, \qquad G_+ = \frac{1 - 2\ell}{1 - \ell}.
$$

Then $w \le W$ and $G_- \le g \le G_+$ (using $1 - 2/n \ge 1 - p$ for $k \ge 2$). Whenever $\lambda \ge 0$ and $D^2 \le 1/2$, define for $s \in [0, 1]$:

$$
F_+ = 3W + (1 - 6W) D^2 + \lambda G_+ D, \qquad F_-(s) = \max_{\theta \in \{0, W\}} \bigl(3\theta + (1 - 6\theta) s^2 - \lambda G_- s\bigr),
$$

$$
E(s) = \max\bigl\{ F_-(s),\; s^2 F_-(s) + (1 - s^2) F_+ \bigr\}. \tag{9}
$$

**Lemma I.7 (Mass-Aware Convexity and Endpoint Maximum).** Under the above hypotheses, $B + \lambda g S_3 \le E(h)$. Moreover, on every closed subinterval $[s_0, s_1] \subseteq [0, 1]$, $\max_{s \in [s_0, s_1]} E(s) = \max\{E(s_0), E(s_1)\}$.

*Proof.* Write $B + \lambda g S_3 = \sum_{i=1}^n x_i^2 f(x_i)$ where $f(t) = 3w + (1 - 6w) t^2 + \lambda g t$. Because $1 - 6w > 0$, $f$ is convex on $[-h, D]$, so for all $i \in [n]$, $f(x_i) \le \max\{f(-h), f(D)\}$. Since $D^2 \le 1/2$, the coefficient $3 - 6D^2 \ge 0$ of $w$ in $f(D)$ is nonnegative, hence $f(D) \le F_+$. By linearity in $w \in [0, W]$ and $g \ge G_-$, $f(-h) \le F_-(h)$. Crucially, $x_n = -h$ occurs with weight $x_n^2 = h^2$; averaging $f(x_n) \le F_-(h)$ with weight $h^2$ and $f(x_i) \le \max\{F_-(h), F_+\}$ on the remaining weight $1 - h^2$ yields $B + \lambda g S_3 \le E(h)$.

For the endpoint property, each branch of $F_-(s)$ is convex quadratic. Each branch of $s^2 F_-(s) + (1 - s^2) F_+$ has the form $q_\theta(s) = F_+ + s^2(3\theta - F_+) - \lambda G_- s^3 + (1 - 6\theta) s^4$ ($\theta \in \{0, W\}$), whose derivative is

$$
q_\theta'(s) = s \bigl[ 2(3\theta - F_+) - 3\lambda G_- s + 4(1 - 6\theta) s^2 \bigr].
$$

Since $F_+ \ge 3W \ge 3\theta$ and $1 - 6\theta > 0$, the quadratic in brackets has nonpositive constant term and positive leading term, so it changes sign at most once on $(0, \infty)$, from negative to positive. Hence $q_\theta$ is quasiconvex on $[0, \infty)$ and attains its maximum on $[s_0, s_1]$ at an endpoint. Taking the maximum of four quasiconvex functions preserves the endpoint property. $\square$

Consequently, if for every cell $[s_0, s_1]$ covering $[0, H_0]$ the two rational endpoint inequalities

$$
(1 - P) c \bigl(I - E(s_i)\bigr) \ge r \qquad (i = 0, 1) \tag{10}
$$

hold, then (8) yields $R \ge r$ (positivity of the left side justifies $v \ge 1 - P$), contradicting $R < r$.

### 1.6 Complete Rational Certificate and Equality Characterization

The four bands below satisfy (5)–(7) with $0 < \beta < 1$ and $D^2 \le 1/2$. Rows 1–2 consume the $r_c = 69/100$ guarantee of Lemma I.3 (valid at size $n - k \ge 5k$) and prove $R \ge 87/100$ for all $n \ge 6k$. Rows 3–4 consume $r_c = 87/100$ (valid at size $n - k \ge 6k$) and prove $R \ge 1$ for all $n \ge 7k$:

| Row | $\ell$ | $P$ | $r_c$ | $r$ | $\beta$ | $D$ | $H_0$ |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| 1 | $0$ | $1/7$ | $0.69$ | $0.87$ | $0.588$ | $0.324$ | $0.737$ |
| 2 | $1/7$ | $1/6$ | $0.69$ | $0.87$ | $0.560$ | $0.369$ | $0.748$ |
| 3 | $0$ | $1/8$ | $0.87$ | $1$ | $0.644$ | $0.271$ | $0.756$ |
| 4 | $1/8$ | $1/7$ | $0.87$ | $1$ | $0.6175$ | $0.306$ | $0.764$ |

Each row's $[0, H_0]$ is tiled by the following 7 closed cells; the final column lists a conservative rational lower bound on $\min_{i \in \{0,1\}} (1-P) c (I - E(s_i)) \times 10^6$ (rounded down):

| Row | $s_0$ | $s_1$ | $z$ | $u$ | Certified Lower Bound $\times 10^6$ |
| :---: | :---: | :---: | :---: | :---: | :---: |
| 1 | $0$ | $0.737$ | $0.69$ | $0.60$ | $930{,}664 \ge 870{,}000$ |
| 2 | $0$ | $0.540$ | $0.75$ | $0.57$ | $870{,}042 \ge 870{,}000$ |
| 2 | $0.540$ | $0.748$ | $0.70$ | $0.64$ | $873{,}160 \ge 870{,}000$ |
| 3 | $0$ | $0.756$ | $0.67$ | $0.63$ | $1{,}028{,}085 > 1{,}000{,}000$ |
| 4 | $0$ | $0.459$ | $0.70$ | $0.54$ | $1{,}000{,}431 > 1{,}000{,}000$ |
| 4 | $0.459$ | $0.604$ | $0.68$ | $0.58$ | $1{,}000{,}043 > 1{,}000{,}000$ |
| 4 | $0.604$ | $0.764$ | $0.64$ | $0.68$ | $1{,}012{,}062 > 1{,}000{,}000$ |

All inequalities in (5)–(7) and (10) are exact rational checks verified over the continuous parameter intervals (no $k$-cutoff) by `verify_universal.py` in `<0.3s`.

**Equality characterization.** For a centered nonconstant vector at $n \ge 7k$, suppose $R = 1$ and $b > 0$. Then $e = tb$, so (4)–(9) hold unchanged with $r = 1$ (non-strict inequalities). Since every certified lower bound in Rows 3–4 is **strictly greater than $1$**, this yields $R > 1$, contradiction. Hence $b = 0$: every $k$-subset containing $x_1$ is nonnegative, exhausting all $\binom{n-1}{k-1}$ nonnegative $k$-subsets. If $\sum x_i > 0$, centering can only shrink the nonnegative family, so equality still forces the same star. Constant vectors at $n \ge 7k$ give $\binom{n}{k} > \binom{n-1}{k-1}$, and $k = 1$ is immediate. $\square$

### 1.7 Independent Elementary Backup: $n \ge 3k^2$ in Ten Lines

Independently of (1)–(10), assume $x_1 \ge \dots \ge x_n$, $\sum x_i = 0$, $x_1 = A > 0$, and $R < 1$. Set $B_{\mathrm{top}} = \sum_{i=1}^k x_i \le k A$. Then $\mathbb{E}[Y_-] = \mathbb{E}[Y_+] < p B_{\mathrm{top}}$. Extending a uniform $(k-1)$-set $U$ by one uniform point gives conditional expectation $\frac{n-k}{n-k+1} \sum_{i \in U} x_i$; by Jensen on $u \mapsto u_-$, $\mathbb{E}\!\left[\max\!\left(-\sum_{i \in U} x_i, 0\right)\right] \le \frac{n-k+1}{n-k} \mathbb{E}[Y_-]$. Conditioning on $1 \notin U$ (probability $\frac{n-k+1}{n}$) and applying Markov at threshold $A$ gives

$$
b = \Pr\!\left(\sum_{i \in U} x_i < -A \,\middle|\, 1 \notin U\right) \le \frac{n \mathbb{E}[Y_-]}{(n-k)A} < \frac{k B_{\mathrm{top}}}{(n-k)A} \le \frac{k^2}{n-k}.
$$

Since $R < 1$, pick any negative $k$-set $T$ containing $1$, and delete $T$ along with the smallest $n \bmod k$ remaining entries. The remaining $N'$ elements satisfy $k \mid N'$, $N' \ge n - 2k + 1$, and have positive sum. Averaging over a uniform random partition into $k$-blocks yields at least $\binom{N'-1}{k-1} \ge \binom{n-2k}{k-1}$ nonnegative $k$-sets disjoint from $T$ (hence off the $1$-star). In star units, this is at least $1 - \frac{(2k-1)(k-1)}{n-1}$ by the union bound. For $n \ge 3k^2$ ($k \ge 2$), the difference

$$
\left(1 - \frac{(2k-1)(k-1)}{n-1}\right) - \frac{k^2}{n-k}
$$

increases in $n$ and at $n = 3k^2$ has numerator $2k(2k-1)^2 > 0$, so the off-star surplus strictly exceeds the bad-star deficit $b$, contradiction. $\square$

---

## Part II: Complete Resolution of Milojević–Sudakov (June 2026) Conjectures 1 & 3

Let $w_1, \dots, w_m > 0$ with $\sum_{i=1}^m w_i = 1$, let $v_1, \dots, v_m \stackrel{\text{i.i.d.}}{\sim} \mathrm{Ber}(p)$, and let $X = \sum_{i=1}^m w_i v_i$.

**Theorem II.1 (Complete Resolution of Milojević–Sudakov Conjecture 1, `arXiv:2606.30287v1`).**
1. For every $p \in [0, 1/3]$ and all nonnegative weights summing to $1$,

$$
\Pr(X \ge p) \ge p.
$$

   This range is sharp: for $p > 1/3$ and $w = (1/3, 1/3, 1/3)$, $\Pr(X \ge p) = 1 - (1-p)^3 - 3p(1-p)^2 = 3p^2 - 2p^3 < p$.
2. For every $p \in (0, 1/3)$, the strict inequality $\Pr(X > p) \ge p$ holds unconditionally; moreover, if $\max_i w_i \le p$, then

$$
\Pr(X > p) > p.
$$

**Theorem II.2 (Complete Resolution of Milojević–Sudakov Conjecture 3 / Question `q:MMS_variant`).** For every $\varepsilon > 0$ and every $C > 0$, there exists $n_0(C, \varepsilon)$ such that for all $n \ge \max((3 + \varepsilon)k, n_0(C, \varepsilon))$, every real vector $x \in \mathbb{R}^n$ with $\sum_{i=1}^n x_i \ge 0$, at most $C$ nonnegative entries, and all negative entries equal has at least $\binom{n-1}{k-1}$ nonnegative $k$-element subsets.

### 2.1 Exact Unit-Fraction Coloring Proof (Including Endpoint $p = 1/3$)

**Lemma II.3 (Lean 4 Verified: `bernoulli_exceedance_unit_fraction`).** For every integer $q \ge 1$ and $p = 1/q$, $\Pr(X \ge 1/q) \ge 1/q$.

*Proof.* Independently assign each index $i \in [m]$ a uniformly random color $c_i \in \{1, \dots, q\}$. For each color $r$, the indicator vector with entries $\mathbf 1_{c_i = r}$ ($i = 1, \dots, m$) is distributed identically to $(v_1, \dots, v_m) \sim \mathrm{Ber}(1/q)^{\otimes m}$. Because $\sum_{r=1}^q \sum_{i : c_i = r} w_i = \sum_{i=1}^m w_i = 1$, every coloring has at least one color $r$ with weight $\ge 1/q$. Taking expectation over the random coloring gives $q \Pr(X \ge 1/q) = \mathbb{E}\!\left[\sum_{r=1}^q \mathbf 1_{\sum_{c_i=r} w_i \ge 1/q}\right] \ge 1$. $\square$

In particular, $p = 1/3$ is resolved cleanly and unconditionally (with zero computer assistance); $p = 0$ is trivial since $X \ge 0$ always. It remains to prove Theorem II.1(2) for all $p \in (0, 1/3)$.

### 2.2 Scale-Free Heavy-Coefficient Test and Hypercontractivity

Set $q = 1 - p$, $r = p/q \in (0, 1/2)$, and $a = \max_i w_i$. Remove one coordinate achieving $a$, let $Y = \sum_{\text{other}} w_i (v_i - p)$, and put

$$
L = \Pr(Y \le -qa), \qquad H = \Pr(Y > pa).
$$

Then $\Pr(X > p) = p(1 - L) + q H$. If $L = 0$, then $\Pr(X > p) \ge p$; moreover, when $a \le p < 1/2$, setting all residual bits to $1$ gives $Y = q(1 - a) \ge q(1 - p) > p^2 \ge pa$ with positive probability, so $H > 0$ and $\Pr(X > p) > p$. When $L > 0$, proving $\Pr(X > p) > p$ is equivalent to refuting $H \le r L$.

Couple two residual configurations $(A, B)$ independently across coordinates with joint probabilities $\Pr(A_i = 1, B_i = 0) = p$, $\Pr(A_i = 0, B_i = 1) = p$, and $\Pr(A_i = 0, B_i = 0) = 1 - 2p$. Conditional on $A$, the vector $B$ is an independent $\mathrm{Ber}(r)$ sample on the zero coordinates of $A$, and $\mathbb{E}[Y(B) \mid A] = -r Y(A)$. Let $\theta$ be any lower bound on $\Pr(\sum u_i (\xi_i - r) > 0)$ valid for all nonempty positive weight vectors at bias $r$. Whenever $Y(A) \le -qa$, the complement of $A$ carries strictly positive weight and has conditional mean $-r Y(A) \ge r q a = pa$, so $\Pr(Y(B) > pa \mid A) \ge \theta$, yielding

$$
J := \Pr\bigl(Y(A) \le -qa,\; Y(B) > pa\bigr) \ge L \theta.
$$

In the $p$-biased orthonormal Fourier basis $\chi_S(A) = \prod_{i \in S} \frac{A_i - p}{\sqrt{pq}}$, the conditional expectation operator $T f(A) = \mathbb{E}[f(B) \mid A]$ acts diagonally by $T \chi_S = (-r)^{|S|} \chi_S$. Its spectrum on mean-zero functions lies in $[-r, r^2]$, so subtracting the midpoint $\frac{r^2 - r}{2}$ gives operator norm $\le \frac{r + r^2}{2}$ (and plain operator norm $\le r$). Since the events $\{Y \le -qa\}$ and $\{Y > pa\}$ are disjoint on a single sample, their centered indicators satisfy $\langle f, g \rangle = -L H$. Cauchy–Schwarz yields both

$$
J \le L H + r \sqrt{L(1-L)H(1-H)}, \qquad J \le \left(1 + \frac{r - r^2}{2}\right) L H + \frac{r + r^2}{2} \sqrt{L(1-L)H(1-H)}.
$$

Under $0 < L$, $H \le rL$, and $r \le 1/2$, monotonicity of $x(1-x)$ on $[0, 1/2]$ yields the scale-free test

$$
\frac{\theta}{r} \le B_r(L) := \left(1 + \frac{r - r^2}{2}\right) L + \frac{1 + r}{2} \sqrt{r(1 - L)(1 - rL)}. \tag{11}
$$

**Lemma II.4 ($L^2 \to L^4$ Hypercontractivity for Very Rare Losses).** For $0 < r \le 1/2$, $\lVert T f \rVert_4 \le \lVert f \rVert_2$. Consequently, $J \le L^{3/4} H^{1/2}$, so $H \le rL$ implies $\theta^4 \le r^2 L$.

*Proof.* On a single coordinate, write $f = \alpha + \beta \chi$ with $\mathbb{E}[\chi] = 0$, $\mathbb{E}[\chi^2] = 1$, $\mathbb{E}[\chi^3] = \frac{1-2p}{\sqrt{pq}} = \frac{1-r}{\sqrt{r}}$, and $\mathbb{E}[\chi^4] = \frac{1}{pq} - 3 = \frac{1}{r} - 1 + r$. Then $Tf = \alpha - r\beta \chi$, and

$$
(\alpha^2 + \beta^2)^2 - \mathbb{E}[(\alpha - r\beta \chi)^4] = (2 - 6r^2)\alpha^2\beta^2 + 4 r^3 \mathbb{E}[\chi^3] \alpha\beta^3 + (1 - r^4 \mathbb{E}[\chi^4]) \beta^4.
$$

For $r \le 1/2$, $2 - 6r^2 \ge 1/2$, $1 - r^4 \mathbb{E}[\chi^4] = 1 - r^3 + r^4 - r^5 \ge 7/8$, and the discriminant $(4 r^3 \mathbb{E}[\chi^3])^2 = 16 r^5 (1-r)^2 \le 1/2 < 4(1/2)(7/8)$, so the binary form is everywhere nonnegative. Tensorization by Minkowski's integral inequality (interchanging $L^4_y L^2_x \le L^2_x L^4_y$) yields $\lVert T f \rVert_4 \le \lVert f \rVert_2$ in any dimension. Hölder's inequality gives $J = \langle \mathbf 1_L, T \mathbf 1_H \rangle \le \lVert \mathbf 1_L \rVert_{4/3} \lVert T \mathbf 1_H \rVert_4 \le L^{3/4} H^{1/2}$, and combining with $L \theta \le J$ and $H \le r L$ yields $\theta^4 \le r^2 L$. $\square$

### 2.3 Purely Analytic Proof on $(0, 1/7]$ (Lean 4 Verified)

**Proposition II.5 (Lean 4 Verified: `bernoulli_strict_exceedance_one_seventh`).** For $0 < p \le 1/7$, $\Pr(X > p) \ge p$, and $\Pr(X > p) > p$ whenever $\max_i w_i \le p$.

*Proof.* Standardize $Z = (X - p)/\sqrt{pq \sum w_i^2}$ (mean $0$, variance $1$) and set $u = \mathbb{E}[Z_+^2]$, $b = \mathbb{E}[Z_+] = \mathbb{E}[Z_-]$, $K = \mathbb{E}[Z^4]$. As in Lemma I.3, Hölder interpolation gives $K b^2 \ge u^3 + (1-u)^3$, and Cauchy–Schwarz gives

$$
\Pr(Z > 0) \ge \frac{b^2}{u} \ge \frac{1/u - 3 + 3u}{K} \ge \frac{2\sqrt{3} - 3}{K} > \frac{23/50}{K}.
$$

Writing $t = a^2 / \sum w_i^2 \in (0, 1]$, direct expansion gives $K = 3 + \left(\frac{1}{pq} - 6\right) \frac{\sum w_i^4}{(\sum w_i^2)^2} \le 3 + \left(\frac{1}{pq} - 6\right) t$.
- **Small head ($t \le 1/10$):** For $p \le 1/7$, $p K \le \frac{12}{5} p + \frac{1}{10q} \le \frac{12}{35} + \frac{7}{60} < \frac{23}{50}$, giving $\Pr(X > p) > p$ outright.
- **Auxiliary bound at $s = r \le 1/6$:** We claim $\Pr(\sum u_i (\xi_i - s) > 0) \ge \frac{3}{4} s$ for all nonempty positive weights. If $t \le 3/8$, then $sK \le \frac{3}{4} s + \frac{3}{8(1-s)} \le \frac{1}{8} + \frac{9}{20}$ and $\frac{23/50}{1/8 + 9/20} > \frac{3}{4}$. If $t > 3/8$, conditioning on the largest coordinate hitting $1$ leaves failure probability at most $\frac{s(1-t)}{(1-s)t + s(1-t)} \le 1/4$ by Cantelli, giving success $\ge \frac{3}{4} s$.
- **Large head ($t > 1/10$):** Suppose $L > 0$ and $H \le rL$. Put $U = Y/a - p$. Then $\mathbb{E}[U] = -p$, $\mathbb{E}[U_-] \ge L$, $\mathbb{E}[U_-^2] \ge L$, and $\mathbb{E}[U_+^2] \ge ((L-p)_+)^2 / (rL)$. Summing against $\mathbb{E}[U^2] = pq(1-t)/t + p^2$ gives

$$
L + \frac{((L-p)_+)^2}{r L} \le 9p - 8p^2 \le \frac{55}{49}.
$$

  The left side is increasing in $L$ and at $L = 3/8$ exceeds $3/8 + 6(3/8 - 1/7)^2 / (3/8) > 55/49$, forcing $L < 3/8$. The plain covariance bound gives $\theta/r \le L + \sqrt{r(1-L)} \le 3/8 + \sqrt{(1/6)(5/8)} < 3/4$, contradicting $\theta \ge \frac{3}{4} r$. $\square$

### 2.4 Zero-Float Certified Extension Across $[1/7, 1/3)$

To extend Proposition II.5 across the entire remaining interval $[1/7, 1/3)$ with zero floating-point decisions and without importing any Berry–Esseen constant or normal table, we normalize weights to $\sum u_i^2 = 1$, set $W = \sum u_i (v_i - p) / \sqrt{pq}$, and build a verified integer table $F[k, j]$ (in units $1/Q$, $Q = 10^7$) uniformly lower-bounding $\Pr(W > j/D)$ over all $p \in [l, h]$ and all weight vectors with $\max_i u_i \le k/B$:

1. **Self-contained Beurling–Selberg / Vaaler normal comparison.** With Fejér kernel $K(y) = (\sin(\pi y)/(\pi y))^2$ and $H_0(y) = \sum_{n \neq 0} \mathrm{sgn}(n) K(y-n) + 2y K(y)$, the bandlimited function $P(y) = (1 + H_0(y) - K(y))/2$ satisfies $P(y) \le \mathbf 1_{y > 0}$ for all $y \in \mathbb{R}$ (including $y = 0$), with $\int (\mathbf 1_{y > 0} - P(y))\,dy = 1/2$ and Fourier multiplier of $H_0$ on $(0, 1)$ equal to $-i[(1-t)\cot(\pi t) + 1/\pi]$. Scaling by $\lambda = T / (2\pi)$ and comparing $W$ against a standard normal $N$ (maximum density $M = 1/\sqrt{2\pi}$) gives

$$
\Pr(W > x) \ge 1 - \Phi(x) - \frac{\pi M}{T} - \int_0^T \frac{21}{20 \pi s} \bigl|\varphi_W(s) - e^{-s^2/2}\bigr|\,ds,
$$

   where the orthogonal real/imaginary multiplier components satisfy $(\pi v A_v)^2 + \pi^2 v^2 (1-v)^2 \le (21/20)^2$ on $v = s/T \in [0, 1]$ (checked on width $1/1000$ cells via $\cot z \le 1/z - z/3$). The integrand $|\varphi_W(s) - e^{-s^2/2}|$ is bounded by the minimum of three explicit telescoping bounds (modulus damping, order-3/4, and order-5/6 cumulant expansion), and for $x < 0$ the table is also seeded by Cantelli $x^2/(1+x^2)$ and the Chernoff bound $1 - e^{-x^2/2}$ (valid since the tilted log-MGF has second derivative $\le u_i^2$ at negative tilts for $p \le 1/2$). Every exponential, sine, and Gaussian tail bound is computed outward in pure integer arithmetic.
2. **Exact dynamic-programming refinement.** For each shell $u = \max_i u_i \in [(k-1)/B, k/B]$, exposing that coordinate yields conditional thresholds $(x + \sqrt{p/q}\,u)/\sqrt{1 - u^2}$ (miss) and $(x - \sqrt{q/p}\,u)/\sqrt{1 - u^2}$ (hit) with residual cap $\le \min(1, (k/B)/\sqrt{1 - (k/B)^2})$. Rounding cap and thresholds outward and combining miss/hit with weights $(1-l, l)$ (valid by monotonicity in the exposed bit) updates the table; taking prefix minima over shells preserves validity for all balls $\max u_i \le k/B$.
3. **Auxiliary-bias table and mixing cut.** The same procedure on $I' = [l/(1-l), h/(1-h)]$ yields a certified lower bound $\theta$ at bias $r \in I'$. On $[31/100, 1/3]$, complementary head-pair credits ($C_2$ for $s < 1/2$) further sharpen $\theta$ without circularity (running the auxiliary prefix checker with no mixing cut). `mix_threshold` finds an integer $J$ such that any $L \le J/1000$ contradicts either (11) or Lemma II.4 ($\theta^4 \le r^2 L$).
4. **Triple-partition credit (for $p < 1/3$) and prefix branch-and-bound.** Fix a nonempty exposed head $H$ of total weight $W_H$ and an actual bias $p < 1/3$. For any three head patterns partitioning $H$, the sum of their three raw residual thresholds is $(3p - 1) W_H < 0$. Sorting their standardized thresholds $x \le y \le z$ and raising $z$ to $-x - y$ yields a universal certified lower bound $C_3$ on the sum of their three conditional probabilities (`triple`, tiling $[-2, 0] \times [x, -x/2]$ by $1/50$ squares and including Cantelli's $4/5$ for $x < -2$). For disjoint triples of patterns with lower-bias probabilities $\ge c_i$ and individual bounds $\ge v_i$, adding $(\min_i c_i)(C_3 - \sum_i v_i)_+$ is strictly sound for every $p < 1/3$.

Sorting weights $u_1 \ge u_2 \ge \dots$ and bisecting prefix bins $[(k_i-1)/U, k_i/U]$ with outward `int128` comparisons certifies strict surplus $\Pr(X > p) > p$ on every subinterval tiling $[1/7, 1/3)$:
- `bernoulli_constants.py`: pure-integer replay covering $[1/7, 3/10]$ (`12.0s`);
- `bernoulli_extension.py` + `prefix.cpp`: exact `int128` replay covering $[29/100, 8/25]$ (`13.4s`) and $[8/25, 1/3)$ (`10.1s`, with boundary $p = 1/3$ covered by Lemma II.3).

### 2.5 Exact Compactness Transfer to Conjecture 3

*Proof of Theorem II.2.* Fix $\varepsilon > 0$ and $C > 0$, and put $p_0 = 1/(3 + \varepsilon) < 1/3$. Suppose for contradiction that there exists a sequence of counterexamples $x^{(t)} \in \mathbb{R}^{n_t}$ with $n_t \ge k_t / p_0$, $n_t \to \infty$, $\sum x_i^{(t)} \ge 0$, at most $C$ nonnegative entries, all negative entries equal, and fewer than $\binom{n_t - 1}{k_t - 1}$ nonnegative $k_t$-subsets. For $n_t > C$ there is a negative entry; normalize its value to $-1$ and set $w_i^{(t)} = (x_i^{(t)} + 1) / n_t \ge 0$. Then $\sum_i w_i^{(t)} = 1$, at most $m = \lfloor C \rfloor$ weights are nonzero, and a $k_t$-subset is nonnegative iff its collected weight is $\ge p_t = k_t / n_t$. If $\max_i w_i^{(t)} \ge p_t$, the star on that index already gives $\binom{n_t - 1}{k_t - 1}$ nonnegative sets; hence $\max_i w_i^{(t)} < p_t \le p_0$ for all $t$.

Pad the exceptional sites to length $m$ with zeros. Passing to a convergent subsequence, $(w^{(t)}, p_t) \to (w^{\ast}, p_{\ast})$ with $\sum_{i=1}^m w_i^{\ast} = 1$ and $1/m \le \max_i w_i^{\ast} \le p_{\ast} \le p_0 < 1/3$. Dropping zero coordinates of $w^{\ast}$ and applying Theorem II.1(2) at bias $p_{\ast} \in (0, 1/3)$ yields $\Pr(\sum w_i^{\ast} v_i > p_{\ast}) > p_{\ast}$. Because only finitely many subsets $E \subseteq [m]$ satisfy $\sum_{i \in E} w_i^{\ast} > p_{\ast}$, every such $E$ satisfies $\sum_{i \in E} w_i^{(t)} > p_t$ for all sufficiently large $t$. Meanwhile, the hypergeometric probability that a uniform $k_t$-subset intersects $[m]$ in $E$ is

$$
\frac{(k_t)_{|E|} (n_t - k_t)_{m - |E|}}{(n_t)_m} \longrightarrow p_*^{|E|} (1 - p_*)^{m - |E|} \qquad (t \to \infty).
$$

Summing over strictly winning patterns $E$ gives $\Pr(Y^{(t)} \ge 0) > p_t = k_t / n_t$ for all sufficiently large $t$, contradicting $g(x^{(t)}; k_t) < \binom{n_t - 1}{k_t - 1}$. $\square$

---

## Part III: Exact $k = 8$ Frontier — $f(8) \ge 26$, Farkas Closures, and Sharp $g(33, 8) = \binom{32}{7}$

Recall $f(k) = \min\{N : g(n, k) = \binom{n-1}{k-1} \text{ for all } n \ge N\}$, known for $k \le 7$ since [Hartke–Stolee (2014)](https://arxiv.org/abs/1302.3636) ($f(7) = 23$).

### 3.1 Exact Counterexample at $(25, 8)$ and Even $n$ Rational Farkas Closures

- **Sharp obstruction ($f(8) \ge 26$):** Taking $22$ entries equal to $+3$ and $3$ entries equal to $-22$ gives $\sum x_i = 0$ and nonnegative $8$-subsets precisely when all $8$ chosen entries are $+3$:

$$
g(x; 8) = \binom{22}{8} = 319{,}770 < 346{,}104 = \binom{24}{7}.
$$

  This witness is verified both in Lean 4 (`Foundation.lean`: `not_mms_25_8`, `threshold_eight_ge`) and in `verify.py`.
- **Chowdhury's step ($g(n+k, k) \ge g(n, k) + \binom{n-1}{k-1}$ when $g(n,k) = \binom{n-1}{k-1}$):** Adding $k$ elements preserves MMS (`Foundation.lean`: `mms_add_k`), so certifying a single base $n_0$ with $g(n_0, 8) = \binom{n_0-1}{7}$ resolves the entire congruence class $n = n_0 + 8s$ ($s \ge 0$).
- **Exact Farkas / block-lift certificates (`verify_cert.py`):** Replaying exact rational LP duals and Gale-dominance branch-and-bound trees (`Foundation.lean` formalizes tree soundness in `mms_of_tree`) certifies:
  - $g(18, 8) = 12{,}870$ (exact non-star minimum, $< \binom{17}{7} = 19{,}448$), and sharp star bases $g(28, 8) = \binom{27}{7} = 888{,}030$, $g(30, 8) = \binom{29}{7} = 1{,}560{,}780$, $g(32, 8) = \binom{31}{7} = 2{,}629{,}575$ (propagating via Chowdhury's step to all $n \equiv 0, 4, 6 \pmod 8$ with $n \ge 28$; cf. [Džavoronok, arXiv:2605.22708v2](https://arxiv.org/abs/2605.22708), Prop. 4.4 for all even $n \ge 28$).

### 3.2 Sign-Stratified Spectral Certificates (`SPEC1`) and Sharp $g(33, 8) = \binom{32}{7}$

**Theorem III.1.** $g(33, 8) = \binom{32}{7} = 3{,}365{,}856$. Consequently, the MMS conjecture holds for $k = 8$ at every $n \equiv 1 \pmod 8$ with $n \ge 33$ (and unconditionally for all $n \ge 56$ by Theorem I.1).

*Proof method (verified by `cover_exact.py` + `spectral_exact.py` on `certs/m_33_8_3365856.cert`).* Fix $x \in \mathbb{R}^n$ with $\sum_{i=1}^n x_i \ge 0$, let $r \in \{1, \dots, n-1\}$ be the number of nonnegative entries (zeros included), and let $b = n - r$. For each feasible stratum $j \in \{\max(0, k-b), \dots, \min(k, r)\}$, let $p_j$ be the fraction of nonnegative $k$-subsets among the $c_j = \binom{r}{j} \binom{b}{k-j}$ subsets containing $j$ nonnegative and $k - j$ negative entries. Then $g(x; k) = \sum_j c_j p_j$, and replacing a uniform negative entry by a uniform unselected nonnegative entry cannot decrease the sum, giving monotonicity $0 = p_0 \le p_1 \le \dots \le p_k = 1$.

1. **Cyclic cover rows (pseudo-matchings).** For any tuple $(j_1, \dots, j_m)$ of strata satisfying $\sum_i j_i \ge r$ and $\sum_i (k - j_i) \le b$, assign edge $i$ a cyclic interval of $j_i$ nonnegative indices (concatenated consecutively around $\mathbb{Z}/r\mathbb{Z}$) and $k - j_i$ pairwise-disjoint negative indices. Every nonnegative entry is covered at least once and no negative entry is covered twice, so the sum of the $m$ edge sums is $\ge \sum_{i=1}^n x_i \ge 0$. Hence at least one edge is nonnegative; averaging over uniform independent relabelings of the two classes yields $\sum_{i=1}^m p_{j_i} \ge 1$.
2. **Pairwise disjoint-sample correlation amplification.** Whenever two edges $u, v$ in a cover row occupy disjoint cyclic intervals of nonnegative labels (and automatically disjoint negative labels), their indicators are sampled from the product of two independent disjoint-pair distributions: sizes $(j_u, j_v)$ in $[r]$ and sizes $(k-j_u, k-j_v)$ in $[b]$. By Lemma I.4 on each factor, the product centered operator norm is bounded by the maximum of the two factor norms:

$$
\rho_{u,v} = \max\!\left( \sqrt{\frac{j_u j_v}{(r - j_u)(r - j_v)}},\; \sqrt{\frac{(k - j_u)(k - j_v)}{(b - k + j_u)(b - k + j_v)}} \right)
$$

   (with $0$ when either subset is empty). Hence the probability that both edges are simultaneously nonnegative is at least

$$
F(p_{j_u}, p_{j_v}) = \max\!\left(0,\; p_{j_u} p_{j_v} - \rho_{u,v} \sqrt{p_{j_u}(1 - p_{j_u}) p_{j_v}(1 - p_{j_v})}\right),
$$

   which is nondecreasing in each argument. On any forest $\mathcal{T}$ of eligible disjoint pairs among the $m$ edges, if $M \ge 1$ edges are nonnegative then at most $M - 1$ forest edges have both endpoints nonnegative. Taking expectations strengthens the cover row from $\sum_i p_{j_i} \ge 1$ to

$$
\sum_{i=1}^m p_{j_i} \ge 1 + \sum_{\{u, v\} \in \mathcal{T}} F(p_{j_u}, p_{j_v}).
$$

3. **Zero-float iterative dual replay.** For each $r \in \{1, \dots, 32\}$ in `m_33_8_3365856.cert` ($39\text{ KB}$), assuming $g(x; 8) \le T - 1 = 3{,}365{,}855$, each round derives rational lower bounds on individual $p_j$ from nonnegative integer combinations of monotonicity, the conditional upper bound $g(x; 8) \le T - 1$, and cover rows amplified by maximum-weight forests computed with outward-rounded integer square roots (`isqrt`). A final nonnegative dual proves $\sum c_j p_j > T - 1$, refuting $g(x; 8) \le 3{,}365{,}855$ for every $r \in \{1, \dots, 32\}$. Equality is attained by $(32, -1, \dots, -1)$. $\square$

---

## Verification Boundary & Reproducibility Ledger

We keep a strict, transparent boundary between machine-checked Lean 4 kernel proofs and zero-float computational replays:

### 1. Lean 4 `v4.35.0` Kernel-Verified Modules (`lean/Conjectures/ManickamMiklosSinghi*`)

All Lean 4 modules compile under `leanprover/lean4:v4.35.0` with **zero `sorry`**, **zero forbidden constructs** (`check_catalog.py --lean-only`), and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`), audited by `ProofAudit.lean` and `leanchecker`:

- `Conjectures.ManickamMiklosSinghi.Foundation`: core definitions (`good`, `nonnegKSubsets`, `MMSHolds`, `support`, `exceedance`, `milojevicSudakovConjectureOne`, `milojevicSudakovConjectureThree`), reduction to sorted zero-sum vectors (`mms_iff_sorted_zero`), Gale monotonicity, Chowdhury step (`mms_add_k`), divisible case (`mms_of_dvd`), exact obstruction at $(25,8)$ (`not_mms_25_8`, `threshold_eight_ge`), and rational Farkas tree soundness (`mms_of_tree`).
- `Conjectures.ManickamMiklosSinghi.BernoulliOneSeventh`: unconditional unit-fraction $q$-coloring theorem (`bernoulli_exceedance_unit_fraction`, closing $p = 1/3$), full analytic Conjecture 1 on $[0, 1/7]$ (`bernoulli_exceedance_one_seventh`), and strict surplus on $(0, 1/7]$ when $\max w_i \le p$ (`bernoulli_strict_exceedance_one_seventh`).
- `Conjectures.ManickamMiklosSinghi.SevenK*` (`29` modular files culminating in `SevenKFinal.lean`) + umbrella `Conjectures.ManickamMiklosSinghi`: **100% kernel-verified** unconditional formalization of Theorem I.1's main bound (`ManickamMiklosSinghi.mms_seven_k : ∀ n k : ℕ, 0 < k → 7 * k ≤ n → MMSHolds n k`), including centered unit reduction (`SevenKReduction`), exact 4-moment slice identities (`SevenKFullMoments`, `SevenKMomentWeights`, `SevenKBase`), unconditional $n \ge 5k$ starting density (`centered_five_k`), Johnson-scheme disjoint-pair variance decay and mixing (`SevenKLoss`, `SevenKChain`, `SevenKMix`, `SevenKGap`), coordinate caps (`SevenKStar`, `SevenKCaps`), lower quartics (`SevenKQuartic`, `SevenKBound`), all 4 rows / 7 rational certificate cells (`SevenKCells`, `SevenKBootstrap`, `SevenKBand`), and the $6k$ / $7k$ upgrades (`centered_six_k`, `centered_seven_k`, `mms_seven_k`). Across all **32 modules** (`ManickamMiklosSinghi.lean` + 31 submodules), the unified Lean 4 `v4.35.0` axiom audit passes **532 theorems and 99 definitions** with **0 violations** and **standard axioms only** (`propext`, `Classical.choice`, `Quot.sound`). (Note: the equality-case star uniqueness and the $n \ge 3k^2$ backup in Sections 1.5–1.6 are proved analytically and checked by `verify_universal.py`, not yet formalized in Lean.)

### 2. Zero-Float Exact Replay (`results/manickam-miklos-singhi/verify.py`)

Run from the repository root (standard Python 3 + NumPy int64 + `g++` C++17; zero floating-point decisions; zero external solvers or GMP; runs in `~43s`):

```bash
python3 results/manickam-miklos-singhi/verify.py
```

This replays and mutation-tests:
1. `verify_universal.py`: exact rational verification of all 4 rows / 7 cells of Theorem I.1, slice-moment identities, the $n \ge 3k^2$ backup, and negative mutation tests (`~0.3s`).
2. `bernoulli_constants.py` + `bernoulli_extension.py` (`prefix.cpp`): exact integer / `int128` verification of strict exceedance on $[1/7, 3/10]$, $[29/100, 8/25]$, and $[8/25, 1/3)$ plus mutation rejection (`~41s`).
3. Exact $(25, 8)$ counterexample ($319{,}770 < 346{,}104$), `verify_cert.py` on the four even $n$ $k=8$ Farkas certificates, `cover_exact.py` + `spectral_exact.py` on the sharp `SPEC1` certificate `certs/m_33_8_3365856.cert`, and negative mutation tests on both certificate verifiers (`~1.1s`).

---

## References

1. N. Manickam and D. Miklós, *On the number of non-negative partial sums of a non-negative sum*, Colloq. Math. Soc. János Bolyai **52** (1988), 385–392.
2. N. Manickam and N. M. Singhi, *First distribution invariants and EKR theorems*, J. Combin. Theory Ser. A **48** (1988), 91–103.
3. A. Chowdhury, G. Sarkis, and S. Shahriari, *A New Quadratic Bound for the Manickam–Miklós–Singhi Conjecture*, `arXiv:1403.1844v4` (`SOURCE.tex`).
4. A. Pokrovskiy, *A linear bound on the Manickam–Miklós–Singhi conjecture*, J. Combin. Theory Ser. A **133** (2015), 280–306 (`arXiv:1308.2176`).
5. S. G. Hartke and D. Stolee, *A linear bound on the Manickam–Miklós–Singhi conjecture for small k* / *Exact values for k ≤ 7*, Electron. J. Combin. **21** (2014), #P1.42 (`arXiv:1302.3636`).
6. J. Džavoronok, *On the Manickam–Miklós–Singhi conjecture*, `arXiv:2605.22708v2` (May 2026).
7. A. Milojević and B. Sudakov, *On the Probability a Weighted Bernoulli Sum Exceeds Its Mean*, `arXiv:2606.30287v1` (June 2026).

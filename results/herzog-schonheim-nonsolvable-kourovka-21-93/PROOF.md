# The Herzog–Schönheim conjecture for finite almost simple groups

**Theorem.** Let $S$ be a finite nonabelian simple group and identify $S$ with its inner automorphism group. For every $S\le G\le\operatorname{Aut}(S)$, a partition of $G$ into at least two left cosets of subgroups has two parts of equal index.

This proves the finite almost simple case of [Kourovka 21.93](https://arxiv.org/abs/1401.0300) / [Erdős 274](https://www.erdosproblems.com/274), not the conjecture for all groups. The distinction from the simple case matters: [Garonzi and Margolis](https://arxiv.org/html/2509.25118v2) (GM) prove the simple and symmetric cases, but in Remark 5.1 exhibit almost simple groups with **unbounded** sum of distinct reciprocal subgroup indices. Their examples adjoin field automorphisms to $\operatorname{PSL}_2(2^a)$ for highly composite $a$. We bound the mass of the parts that *cut* a socle coset, rather than the mass of all possible indices in $G$.

## 1. A relative-index criterion

Write **HS** for the conclusion of the theorem about coset partitions. For a finite group $X$ and a positive integer $m$, put

$$
D(X)=\sum_{\ell\in\{[X:Y]:Y<X\}}\frac1\ell,\qquad
K(m)=\max_{b\mid m}\ \sum_{\substack{h\mid m\\h\ge b}}\frac{b}{h}.
$$

Both sums count **distinct integers**, not subgroups. If $m_0\mid m$, then $K(m_0)\le K(m)$ by inclusion of divisor sets. Also $K(m)\le\tau(m)\le m$.

**Lemma.** Suppose $N\trianglelefteq G$, $Q=G/N$ is HS and $|Q|\mid m$. If $K(m)D(N)<1$, then $G$ is HS.

**Proof.** Assume that $G=\bigsqcup_i g_iH_i$ has at least two parts with all global indices distinct. Write $\pi:G\to Q$ for the quotient map and set

$$
h_i=[Q:\pi(H_i)],\qquad \ell_i=[N:N\cap H_i],\qquad
[G:H_i]=h_i\ell_i.
$$

The product identity follows by counting the kernel and image of $\pi$ on $H_i$. The image of a part has quotient density $1/h_i$. A part with $\ell_i=1$ contains every $N$-coset it meets. If all parts have this property, the partition descends to $Q$ with its indices and number of parts unchanged, a contradiction.

Let $J=\{i:\ell_i>1\}$ and let $R$ be the union of the images of those parts. No part with $\ell_i=1$ meets $\pi^{-1}(R)$: it would contain an entire fibre meeting another part. Hence $\pi^{-1}(R)$ is **exactly** the union of the parts in $J$. Its density is

$$
\nu=\frac{|R|}{|Q|}=\sum_{i\in J}\frac{1}{h_i\ell_i}.
$$

Take $b=\min_{i\in J}h_i$. One image in $R$ has density $1/b$, so $\nu\ge1/b$. For fixed $\ell_i=\ell$ the $h_i$ are distinct, since their products with $\ell$ are distinct; they divide $m$ and are at least $b$. Therefore

$$
1\ \le\ b\nu
\ \le\ D(N)\sum_{\substack{h\mid m\\h\ge b}}\frac b h
\ \le\ D(N)K(m),
$$

a contradiction. No independence of the images or splitting of the group extension was assumed. $\square$

The distinction between whole fibres and cut fibres also occurs in [Menon, §3](https://arxiv.org/html/2611.11002v1). Here neither a coset-union bound in $Q$ nor a primitive-solvable local-index restriction in $N$ is required. The primitive-solvable step does not transfer verbatim: in $A_5$ the normalizer of a Sylow $5$-subgroup has index $6$, divisible by none of $5,2^{\operatorname{ord}_5(2)}=16,3^{\operatorname{ord}_5(3)}=81$ from Menon's Lemma 4.2. We use Menon's Theorem 1.2 only to know that the quotient is HS: by the Schreier theorem $\operatorname{Out}(S)$ is solvable, as is $G/S$. It suffices, outside cases settled directly, to bound $K(o)D(S)$ for a **multiple** $o$ of $|\operatorname{Out}(S)|$.

For example, take $S=\operatorname{PSL}_2(64)$ and the full field-automorphism extension $G=S\rtimes C_6$. Pullback from $C_6$ gives proper indices $2,3,6$ with reciprocal sum already one. Yet $|S|=262080$, every proper subgroup has index at least $64$, and the sum of divisors of $262080$ at most $4095$ is $96034$. Thus $K(6)D(S)\le 2\cdot96034/262080=48017/65520<1$.

## 2. Bounds that can be checked from the socle

Let $v=|S|$, let $u$ be a lower bound on the smallest proper subgroup index, and let $c$ bound the number of isomorphism types of maximal subgroups. Write $P(v)=\prod_{p\mid v}p/(p-1)$. We use three upper bounds for $D(S)$:

1. **Order divisors:** $\displaystyle v^{-1}\sum_{s\mid v,\;su\le v}s$.
2. **Maximal counts:** $cP(v)/u$.
3. **Maximal indices:** if $B$ lists all distinct indices of maximal subgroups, use $\displaystyle v^{-1}\sum_{s\in\bigcup_{j\in B}\{d:d\mid v/j\}}s$.

Indeed $D(S)$ is the sum of distinct proper subgroup orders divided by $v$. Every such order divides a maximal subgroup order $w$. All divisors of $w$ sum to at most $wP(v)$ by the geometric series, which gives bound 2 since $w/v\le1/u$. Counting their union gives bound 3. If at most $k$ maximal types have order at least $A$, the same calculation gives

$$
D(S)\le P(v)\left(\frac{k}{u}+\frac{cA}{v}\right).
$$

Two useful bounds do not require factoring $v$. First $P(v)\le1+\log_2 v$: for the $i$-th smallest prime divisor, $p_i\ge i+1$, so the product telescopes to at most $1+\omega(v)$. Second, when $v<2^B$, multiply $p/(p-1)$ over the first primes, stopping **before** their primorial reaches $2^B$. This upper bounds $P(v)$ because the factors decrease with $p$ and no more such primes can divide $v$.

## 3. Reduction to a finite calculation

We use the classification of finite simple groups. For classical groups $n$ is the natural dimension (not the rank), $q=p^f$ is the parameter, $t=\lfloor\log_2q\rfloor$, and $z=t+1$. For unitary groups the defining matrices are over $\mathbb F_{q^2}$. The group orders and the diagonal, field and graph factors of the outer orders are as in [Byott, Tables 1–4](https://nyjm.albany.edu/j/2015/21-40p.pdf). In particular $o=|\operatorname{Out}(S)|\le24nz$ in classical type; for $\operatorname{PSL}_2(q)$ it is $\gcd(2,q-1)f$. In exceptional Lie type outside the Tits group the outer order divides $6f$.

**Unbounded classical parameters.** For $n\ge3$, GM Lemma 4.5 and Table 2 give $v\le q^{n^2}$ and $u\ge q^{\max(2,n-2)}$ (using the individual rows at small dimensions). Here and below an inequality on $u$ means that this lower bound on the minimal index is available. [Häsä, Theorem 1.1](https://arxiv.org/abs/1112.3941), as used in GM Lemma 4.4, bounds the number of maximal types by $2n^{5.2}+n\log_2\log_2q\le2n^6+nz$. Thus $K(o)D(S)$ is bounded above by

$$
\frac{24nz(2n^6+nz)(n^2z+1)}{2^{t\max(2,n-2)}}.
$$

The fraction is below one at $(n,t)=(64,1),(4,16),(3,16)$. The numerator has nonnegative coefficients and degree at most nine in $n$ and three in $z$. Starting at $(64,1)$, an increment in $n$ grows it by at most $(65/64)^9<2$, whereas the denominator at least doubles; an increment in $t$ grows it by at most $(3/2)^3<2^{62}$. Starting at $(4,16)$, use $(5/4)^9<2^{16}$ and $(18/17)^3<4$ instead. At $n=3$ only the increment in $t$ is needed. This handles every $n\ge64$ or $t\ge16$ with $n\ge3$.

For $S=\operatorname{PSL}_2(q)$, $v<q^3$, $u\ge q$ except at $q=9$, and $c\le5+\omega(f)$ by GM Tables 2–3. For $t\ge16$ it suffices that

$$
2t(5+t)(3z+1)<2^t.
$$

This holds at $t=16$, and the left side grows by a factor at most $(17/16)^3<2$ per increment. The exception $q=9$ is not in this tail.

**Unbounded exceptional parameters.** GM Table 5 gives $v\le q^{248}$, $u\ge q^2$, and $c\le166+\log_2\log_2q$ for the ten infinite families. It suffices that $6z(166+z)(248z+1)<2^{2t}$. Again the inequality holds at $t=16$ and persists by the cubic growth ratio above.

**Finite classical box.** It remains to take $2\le n<64$ and prime powers $2\le q<2^{16}$, subject to the simple-group restrictions. [The verifier](verify.py) generates the prime powers by integer factorization. It first removes a whole dyadic interval if the corresponding inequality above holds. For the rest it computes $v,u,o$ from the order formulas and GM Table 2. At $n\le12$ it uses $c=C+\omega(f)$ from GM Table 3. At $n\ge13$ it uses the split bound of §2 with $A=q^{3\delta n}$, where $\delta=2$ for unitary groups and $1$ otherwise. GM Lemma 4.3 gives $k\le 3n/2+14\sqrt n+12+\log_2\log_2q$; the verifier rounds upwards using integers. In both cases it multiplies by the exact $K(o)$. When the bound from maximal counts is too large, it tries the order-divisor bound instead.

The small-order exit $vo<2000$ uses [Hu–Lin](https://doi.org/10.28919/ejma.2026.6.14); hence it applies to every intermediate group, not just the socle. The isomorphism $\operatorname{PSL}_4(2)\cong A_8$ reduces that row to the alternating case below. The only other rows not settled by the previous bounds are the following. The inputs are **all distinct maximal indices** in the linked GAP Character Table Library tables:

| Socle | $o$ | Maximal indices |
|---|---:|---|
| [PSL₃(3)](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/L3%283%29.html) | 2 | 13, 144, 234 |
| [PSL₃(4)](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/L3%284%29.html) | 12 | 21, 56, 120, 280 |
| [PSL₄(3)](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/L4%283%29.html) | 4 | 40, 117, 130, 2106, 8424, 10530 |
| [PSL₅(2)](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/L5%282%29.html) | 2 | 31, 155, 64512 |
| [PSL₆(2)](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/L6%282%29.html) | 2 | 63, 651, 1395, 13888, 55552, 357120, 1904640 |

In each row bound 3 of §2, multiplied by $K(o)$, is less than one. This is an upper bound from divisibility, not an assumption that every divisor is realized.

**Finite exceptional box.** For $q<2^{16}$ take $(C,r)$ from GM Table 5, so that $c\le C+\log_2\log_2q$ and $v\le q^r$; for $F_4$ conservatively take $C=19$ from their proof. The following exponents $a$ give $u\ge q^a$ directly from the same table, with $u=351,416$ used at $G_2(3),G_2(4)$:

| Type | ${}^2B_2$ | $G_2$ | ${}^2G_2$ | ${}^3D_4$ | $F_4$ | ${}^2F_4$ | $E_6$ | ${}^2E_6$ | $E_7$ | $E_8$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $a$ | 2 | 4 | 3 | 9 | 11 | 10 | 16 | 18 | 27 | 50 |

Use $o=6f$, or $o=f$ for the Suzuki and the two Ree families, with their odd-exponent field restrictions. The primorial bound for $v<2^{rz}$ and bound 2 of §2 suffice in every remaining row.

**Alternating, sporadic and Tits socles.** For $A_n$ with $n\ge5$, $n\ne6$, the only intermediate groups are $A_n$ and $S_n$, already HS by GM. For $A_6$, even its full automorphism group has order $1440<2000$.

For the sporadics and the Tits group take $o=2$, so $K(o)=3/2$. Apart from the five Mathieu groups, $J_2$ and the Higman–Sims group, GM Table 1 gives $c/u\le1/16$. All orders are less than $2^{200}$ and the primorial bound for these orders times $3/2$ is less than 16. For $J_2$ and Higman–Sims use $u=100$ and respectively $(v,c)=(604800,9),(44352000,10)$ in bound 2. The Mathieu groups $M_{11},M_{23},M_{24}$ have trivial outer group. For [M₁₂](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/M12.html) and [M₂₂](https://www.math.rwth-aachen.de/homes/sam/ctbllib/ctbltoc/data/M22.html) bound 3 works with maximal indices $\{12,66,144,220,396,495,1320\}$ and $\{22,77,176,231,330,616,672\}$, respectively.

These families exhaust the possible socles. The relative-index lemma proves the theorem. $\square$

## Verification and scope

Run [verify.py](verify.py) with Python 3. It recomputes the rational comparisons, the exhaustive finite parameter ranges and the base/ratio inequalities for the infinite tails. Its negative control adds the forbidden whole-socle order to the $\operatorname{PSL}_3(4)$ certificate and requires rejection. The classification, the tabulated structural bounds, Menon's theorem and the small-order theorem are cited mathematical inputs, not claims verified by the script.

The [Lean file](../../lean/Conjectures/HerzogSchonheimNonSolvable.lean) isolates the finite counting step: for projected sets with constant positive fibre sizes summing to a full fibre at every covered quotient point, it bounds the filled area by the product of the sums of distinct admissible local and projected sizes. The group classification and the headline theorem are **not** formalized in Lean.

The theorem does not cover general solvable-radical extensions or groups with multiple minimal nonabelian normal factors. In particular, descending every conjectural counterexample to an almost simple quotient would require a separate theorem; HS for a quotient alone does not give such a descent.

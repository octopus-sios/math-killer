# Interlacing across two heights of a balanced array

Fix a column count $d\ge2$ and a row cap $1\le r\le d$. Let $a_{h,k}$ count labeled binary arrays with $h$ rows, $d$ columns, exactly $k$ ones per column and at most $r$ ones per row. Put $P_h(q)=\sum_k a_{h,k}q^k$, $D_h=\lfloor hr/d\rfloor$ and $N=n+1$.

**Theorem (first two roots, all heights and caps).** In each of $P_n,P_N$, the two zeros of smallest modulus are simple and negative, using all available zeros if the degree is below two. Every other zero has strictly larger modulus. Writing $\alpha_j$ and $\beta_j$ for the moduli from the old and new rows respectively, these initial lists strictly alternate:

$$
\beta_1<\alpha_1<\beta_2<\alpha_2
$$

with nonexistent entries omitted. In particular this holds for the original four-column, cap-two polynomial at every height, not merely eventually. Sections 1–4 handle the two-root assertion for $d\ge13$ as part of a growing-prefix result. Section 5 closes the remaining widths.

**Theorem (full interlacing in two sectors).** The polynomials $P_n,P_N$ have only simple negative zeros, and these zeros strictly alternate, if either of the following holds:

1. $2d\ge n+2$;
2. $d<N$ and $d^2\ge Nr\log(8N/d)$.

The logs are natural. In order of **increasing modulus**, the order is $\beta_1<\alpha_1<\beta_2<\alpha_2<\cdots$, omitting nonexistent terms. This includes degree increases and ties in degree. For example, the second range contains $r=2$, $n=t^3$, $d=t^2$ for all sufficiently large integers $t$; both degrees are $2t$ and $d/n\to0$.

**Theorem (nearest zeros at every height).** Let $m\ge1$ satisfy

$$
(1+1/m)^d\ \ge\ 64(m+1).
$$

For each $h=n,N$, the $\min(m,D_h)$ zeros of $P_h$ nearest the origin are simple and negative, and every other complex zero has strictly greater modulus. These two initial lists strictly alternate in the same order as above. There is **no** restriction on the height or cap. For instance, this gives interlacing of the first two available roots for all $d\ge13$ and all heights. More generally $d\ge(m+1)\log(64(m+1))$ suffices. In particular the number controlled, up to the degree, grows at least on the order of $d/\log d$.

These are partial results on [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) and its [consecutive-row question](https://github.com/PerAlexandersson/RealRooted/issues/2005), not a proof of unrestricted real-rootedness. What distinguishes the assertions from single-row real-rootedness is the ordering of the two sets of roots. [ProgramComputer's prior results](https://github.com/ProgramComputer/open-math-research/blob/e6724cb96ff30e8469b7bbc54208666623ce74f6/topics/balanced-arrays/README.md) include all-height real-rootedness for $(r,d)=(2,4)$, all-height interlacing at corank one, interlacing of the nearest root at all caps, eventual interlacing for fixed proper rank and dimension, and an ineffective uniform eventual real-rootedness theorem. We do not settle all-height interlacing for $(2,4)$. At rank one the stronger window of $d+1$ interlacing rows is already [Ding's Theorem 1.3](https://doi.org/10.1016/j.disc.2025.114522); at full rank real-rootedness of the binomial powers follows by Schur–Szegő composition.

## 1. A sharp two-height coefficient comparison

All quotas from zero to $D_h$ occur: give the columns successive blocks of length $k$ from the cyclic list of row labels. No column repeats a label and each row is used at most $\lceil dk/h\rceil$ times. Larger quotas exceed total capacity. At $h=0$ the polynomial is $1$. In particular $D_N-D_n\in\{0,1\}$. Write $R_{h,k}=a_{h,k}/a_{h,k-1}$ on its positive support. Our key inequalities, whenever both displayed ratios exist, are

$$
\frac{R_{N,k}}{R_{n,k}}\ \ge\ \left(1+\frac{1}{N-k}\right)^d,
\qquad
\frac{R_{n,k}}{R_{N,k+1}}\ \ge\ \left(1+\frac{1}{k}\right)^d. \tag{1}
$$

Both constants are sharp: for $r=d$ one has $a_{h,k}=\binom hk^d$ and both are equalities. Thus even where we do not know how to interlace the roots, we can interlace their inverse-ratio approximations at every height.

Let $C_h(v)$ count arrays of column margins $v=(v_1,\ldots,v_d)$; set it to zero at impossible margins. Deletion of ones makes its positive support a down-set in the nonnegative box. We use only the **distinct-column** part of the known margin inequality: for $i\ne j$,

$$
C_h(v)C_h(v+e_i+e_j)\le C_h(v+e_i)C_h(v+e_j).
$$

Equivalently, the extension ratio $U_h(v,i)=C_h(v+e_i)/C_h(v)$ decreases weakly when other margins increase with $v_i$ fixed, comparing positive denominators along the down-set. For clarity, the [array proof of the margin inequality](https://github.com/ProgramComputer/open-math-research/blob/e6724cb96ff30e8469b7bbc54208666623ce74f6/topics/balanced-arrays/orientation-normalization.md) applies [Kahn–Neiman, Lemma 8](https://arxiv.org/pdf/1001.0610). Here is the reduction. Color the two arrays in a product red and blue. In each of columns $i,j$ give the smaller margin an occupied dummy cell in a private extra row, equalizing the two quotas. For each column fix the doubly occupied rows and the rows occupied in exactly one color, and pair the exclusive rows across colors. If there are $2b$ exclusive rows in a column, the multiplicity of the refinement is $b!$ for either product. Fix the unordered pairs and orient them from red to blue. At a real row of degree $H$ with $c$ common cells, both outdegree and indegree must be at least $\max(0,H+c-r)$; this enforces both caps. At the two degree-one dummies the left product forces both edges out, the right product one out and one in. The orientation lemma says the count cannot decrease on this change: the old outdegree bound dominates each of the new bounds pointwise, and their sum is unchanged. Sum over the paired data with the reciprocal refinement multiplicities. Nothing here asserts stability of the row polynomial.

Now fix $v,i$ with $C_n(v+e_i)>0$. Condition the last row at height $N$ to have support $S$, $|S|\le r$, then remove it. With $i\notin S$, the margin $v-\mathbf1_S$ is below $v$ in the other coordinates. Hence, term by term,

$$
C_n(v+e_i-\mathbf1_S)\ \ge\ U_n(v,i)\,C_n(v-\mathbf1_S).
$$

Summing counts arrays in which the last bit of column $i$ is **zero**. By exchangeability of the $N$ rows its fraction at margin $w$ is $(N-w_i)/N$. We obtain

$$
U_N(v,i)\ \ge\ \frac{N-v_i}{N-v_i-1}\,U_n(v,i).
$$

For the second comparison start instead at $w=v+\mathbf1$, and keep supports with $i\in S$. The old margin $w-\mathbf1_S$ now agrees with $v$ at $i$ but is **above** $v$ elsewhere. Thus

$$
C_n(w+e_i-\mathbf1_S)\ \le\ U_n(v,i)\,C_n(w-\mathbf1_S).
$$

This time the last bit is **one**, with fraction $w_i/N$. The result is $U_n(v,i)\ge (v_i+2)U_N(w,i)/(v_i+1)$ whenever the latter extension is defined. Impossible summands cause no problem: a negative coordinate in the zero-bit comparison is away from $i$ and persists on both sides; in the one-bit comparison an infeasible nonnegative base cannot admit an extension.

Increase each column in turn on the path from $(k-1)\mathbf1$ to $k\mathbf1$. At each step the coordinate being raised is still $k-1$. Multiplying the zero-bit bounds gives the first inequality of (1); multiplying the one-bit bounds, with the second path shifted by $\mathbf1$, gives the second. Feasibility of the terminal margins in each claimed inequality gives positive counts on its paths.

Multiplying successive bounds in (1) recovers the single-row curvature estimate at every internal quota of either $h=n$ or $h=N$:

$$
\frac{R_{h,j}}{R_{h,j+1}}\ \ge\
\left[\left(1+\frac1j\right)\left(1+\frac1{h-j}\right)\right]^d. \tag{2}
$$

For the new row insert $R_{n,j}$, which exists since $j<D_N$; for the old row insert $R_{N,j+1}$. In particular the $R_{h,j}$ decrease. The gain in (1) is that the two factors in (2) are assigned separately to the two gaps **between** heights.

## 2. Localizing zeros from coefficient ratios

For a polynomial $F(z)=\sum_{j=0}^D f_jz^j$ with positive coefficients and decreasing ratios $R_j=f_j/f_{j-1}$, fix $s\le D$. Suppose $R_j/R_{j+1}\ge T$ for $1\le j\le s$ with $j<D$. For $1<\lambda\le2$ and $T>\lambda^2/(\lambda-1)$, each interval

$$
I_j=\left(\frac1{\lambda R_j},\,\frac{\lambda}{R_j}\right),\qquad 1\le j\le s,
$$

contains the modulus of a negative root. Indeed, at $t=1/(\lambda R_j)$ the term of $F(-t)$ of index $j-1$ has adjacent magnitudes, relative to its own, at most $1/\lambda$ and $\lambda/T$. Their sum is less than one. On each side the magnitudes continue to decrease outwards, so the corresponding alternating tail costs at most its first term. At $t=\lambda/R_j$ the index $j$ dominates by the same argument. Missing neighbors cost zero. The two signs are opposite. The intervals are disjoint because $T>\lambda^2$. For $s=D$ this gives the full degree of distinct negative roots.

For a prefix $0<s<D$, if also $T\ge16$, then on $|z|=3/R_s$ the term of index $s$ dominates the sum of the absolute values of all other terms: the relative sum is at most

$$
\sum_{\ell\ge1}3^{-\ell}+\sum_{\ell\ge1}(3/T)^\ell<1.
$$

Rouché's theorem gives exactly $s$ roots inside, counted with multiplicity. They are precisely the roots already located in $I_1,\ldots,I_s$. This also applies at each shorter prefix satisfying the hypotheses.

## 3. Full alternating order in the two sectors

If all the within-row gaps satisfy the localization test, it suffices that both cross-row factors in (1) be at least $\lambda^2$. Then the intervals for the two full lists are disjoint in the asserted alternating order. Constant rows need no interval. Take $n\ge1$ since $n=0$ is immediate.

For $2d\ge N+1$, use $\lambda=5/4$. The right side of (2) is at least $(1+2/N)^{2d}$: the product in brackets is $1+(h+1)/(j(h-j))\ge(1+2/h)^2$. Since $\log(1+x)>2x/(2+x)$ for $x>0$, this gives a within-row bound greater than $e^2>25/4=\lambda^2/(\lambda-1)$. Each cross factor is at least $(1+1/n)^d>\exp(d/N)>\lambda^2$.

In the second sector use $\lambda=1+d/(4N)<5/4$. Each cross factor is at least $1+d/n>\lambda^2$. An internal index has $j+1\le Nr/d$, so (2) exceeds $\exp(d/(j+1))\ge\exp(d^2/(Nr))\ge8N/d$. This exceeds $\lambda^2/(\lambda-1)$, as required.

## 4. A growing prefix with no height bound

Assume $T=64(m+1)\le(1+1/m)^d$. By (2) the localization test holds through $s_h=\min(m,D_h)$ in each row with $\lambda=1+1/(8(m+1))$: one has $T>\lambda^2/(\lambda-1)$. Thus the two prefixes consist of the nearest roots even if other roots are nonreal. For each available comparison $\alpha_k,\beta_{k+1}$ within the prefixes, the second factor in (1) is at least $T$, so $\alpha_k<\beta_{k+1}$. What remains is $\beta_k<\alpha_k$.

If $N\le2d(m+1)$, the first factor in (1) is at least $1+d/(N-k)>1+1/(2(m+1))>\lambda^2$, so the intervals again suffice. At larger heights this gap can be arbitrarily close to one; localization of the two rows separately is not enough. Instead we evaluate the old row at a root of the new one.

Write $B_j=a_{N,j}$ and $g_j=a_{n,j}/B_j$ on the new support (zero numerator allowed). This ratio is the probability of an **empty last row** at quota $j$. The expected row sum is $dj/N$, so

$$
0\le 1-g_j\le dj/N.
$$

Take any $1\le k\le\min(m,D_n)$. Since $N>2d(m+1)$, $g_{k-1}>1/2$. The first inequality of (1) gives $g_k/g_{k-1}\le(1+d/N)^{-1}$, hence $g_{k-1}-g_k>d/(4N)$.

At $t=\beta_k\in I_k$ for the new row set $w_j=B_jt^j$. Subtract $g_{k-1}P_N(-t)=0$ from $P_n(-t)$. The term at $k-1$ disappears; the term at $k$ has sign $(-1)^{k-1}$ and magnitude greater than $(d/(4N))w_k$. Put $\rho=2/T$. The gap estimates at $k-1,k$ and monotonicity of all further ratios give

$$
w_{k-1-\ell}\le2\rho^\ell w_k,\qquad
w_{k+\ell}\le\rho^\ell w_k\qquad(\ell\ge1)
$$

for indices present. Indeed $w_{k-1}/w_k<\lambda\le2$; stepping one more index away on either side costs at most $\lambda/T$. At the endpoints the missing tail is empty. The remaining terms have multipliers $|g_j-g_{k-1}|\le(d/N)\max(j,k-1)$. Their total magnitude divided by $(d/N)w_k$ is at most

$$
\frac{3k\rho}{1-\rho}+\frac{\rho}{(1-\rho)^2}
\le\frac{3k+2}{32(m+1)-1}<\frac14 .
$$

Consequently $P_n(-\beta_k)$ has sign $(-1)^{k-1}$. For $k>1$ we already have $\alpha_{k-1}<\beta_k$. Also $\beta_k<\lambda/R_{N,k}\le\lambda/R_{n,k}$ by (1). Through that right endpoint of old interval $I_k$ there are exactly $k$ old roots, by localization and the disk count (or the degree when $k=D_n$). They are simple and negative. Starting from $P_n(0)=1$, the sign at $\beta_k$ therefore places it strictly **before** $\alpha_k$. This proves the second theorem.

## 5. The second root at the remaining widths

We now prove the two-root conclusion **without a width condition**. The earlier theorem takes care of $d\ge13$ because $(3/2)^{13}>192$. For smaller widths we exploit the fact that a sign at the second root can be certified using just three nonconstant coefficients, even when the degree is unbounded.

First let $4\le d\le12$. In a row $F$ of degree at least two write $R_j=f_j/f_{j-1}$ and $Q_j=R_j/R_{j+1}$ at internal indices. The second root has modulus in

$$
\left(\frac{3}{4R_2},\,\frac{3}{2R_2}\right). \tag{3}
$$

Indeed $Q_j\ge(1+1/j)^4$ by (2). At $t=u/R_2$, the terms of $F(-t)$ of indices one and two have magnitudes $w_1=f_1t=uQ_1$ and $u w_1$. For $u=3/4$, truncating after the quadratic term gives an upper bound $1-w_1/4<0$. For $u=3/2$, truncating after the cubic gives a lower bound $1+w_1(-1+u-u^2/Q_2)>0$; omit the last summand inside the parentheses if the cubic is absent. The tails alternate with decreasing magnitudes by (2). Thus there are negative roots before and inside (3). For degree two this exhausts the zeros. For higher degree, on the circle of radius $\sqrt{Q_2}/R_2$ the immediate neighbors of the quadratic term each have relative magnitude at most $4/9$. The constant term contributes at most $(4/9)^2/16=1/81$. Beyond the cubic each further step costs at most $(4/9)(3/4)^4=9/64$ (if the degree is three this tail is empty). Since

$$
\frac{4}{9}+\frac1{81}+\frac{4/9}{1-9/64}<1,
$$

Rouché counts exactly two zeros in the disk, which contains (3). These are therefore the first two, both simple.

The [all-height first-root theorem](https://github.com/ProgramComputer/open-math-research/blob/e6724cb96ff30e8469b7bbc54208666623ce74f6/topics/balanced-arrays/first-root.md) gives $\beta_1<\alpha_1$ and puts every other new zero outside the old first modulus. It remains to prove $\beta_2<\alpha_2$ when the old degree is at least two. Set $A_j=a_{n,j}$, $B_j=a_{N,j}$ and $\delta_j=B_j-A_j$, extending both coefficient lists by zeros. If $R_{N,2}\ge2R_{n,2}$, (3) already separates the second roots. Otherwise throughout the old interval (3) we have $t<3/R_{N,2}$.

The fraction $\delta_j/B_j$ of arrays using the last row lies between $j/N$ (one specified column hits) and $dj/N$ (union bound) at each positive quota on the new support. For $j\ge3$ with $B_{j+1}>0$, multiplying (2) along the new row gives $R_{N,j+1}/R_{N,2}\le(2/(j+1))^d$. Thus

$$
t\,\frac{\delta_{j+1}}{\delta_j}
<3d\,\frac{j+1}{j}\left(\frac{2}{j+1}\right)^d
\le\frac{4d}{2^d}\le1.
$$

It follows that $P_N(-t)-P_n(-t)\ge t(-\delta_1+t\delta_2-t^2\delta_3)$. This quadratic in parentheses is concave in $t$, so it suffices to check positivity at the two endpoints of (3) for the old row. For $u=p/q$ equal to $3/4$ or $3/2$, the endpoint condition, after multiplication by $(q A_2)^2$, is

$$
F_{p,q}(n)=-\delta_1(q A_2)^2+\delta_2pq A_1A_2-\delta_3(p A_1)^2>0. \tag{4}
$$

**Exact positivity certificate.** Each $A_k$ is a polynomial in $n$ of degree at most $dk$: choose the $\ell$ nonempty rows and fill them. In the basis $\binom{n}{\ell}$ its coefficient is the equal-margin coefficient of $(e_1+\cdots+e_r)^\ell$. Hence $\delta_k$ has degree at most $dk-1$, and (4) has degree at most $5d-1$. Set $n_0=\lceil2d/r\rceil$, the first old row with a quadratic term. For every $4\le d\le12$, $1\le r\le d$ and both $(p,q)$, the checker verifies

$$
\Delta^i F_{p,q}(n_0)>0\qquad(0\le i<5d),\qquad
\Delta F(n)=F(n+1)-F(n).
$$

These are **6,360 integer inequalities**. To reproduce them, the checker removes a nonempty row from the remaining margins: if $g_j$ columns have residual margin $j>0$ and $b_j$ of them lose a unit, there are $\prod_j\binom{g_j}{b_j}$ choices, with $1\le\sum_j b_j\le r$. The empty list of positive margins has one fill with zero further rows. This computes all the needed binomial-basis coefficients for $k=1,2,3$. Evaluating at $n_0,\ldots,n_0+5d$ gives the samples for (4) and its full difference table. The Newton expansion at $n_0$ has basis $\binom{n-n_0}{i}$, so its positive constant and positive further coefficients prove (4) for **all** integers $n\ge n_0$, not only at the sampled heights.

The checker also reconstructs every input polynomial by inclusion–exclusion within each column, independently of the margin recursion. Label the $k$ occurrences and exclude their pair coincidences. If $X,Y,Z$ mark blocks of weights 1, 2, 3, the signed block patterns for one column are $X$, $X^2-Y$, and $X^3-3XY+2Z$ respectively: in the last case two or three pair equalities both force a triple. Raise the corresponding expression to power $d$. For each resulting collection of labeled blocks count placements onto $\ell$ nonempty rows, removing arbitrary blocks of total weight between 1 and $r$ for the last row. The signed sum divided by $(k!)^d$ agrees at each $\ell$ with the first computation.

In particular $P_N(-\alpha_2)>P_n(-\alpha_2)=0$. Just past its simple first root the new row has negative sign, and $\beta_1<\alpha_2$. It must cross again before $\alpha_2$, giving $\beta_2<\alpha_2$. This completes the missing comparison.

For completeness, $d=2,3$ use previously known families. At full rank, the weak interlacing of $(1+q)^n$ and $(1+q)^N$ passes to their $d$-fold coefficientwise powers by [Garloff–Wagner, Theorem 4](https://www-home.htwg-konstanz.de/~garloff/Garloff_Wagner_Hadamard_Products.pdf). Parts (a) and (c) give simple, coprime negative roots for $d\ge2$: unequal degrees and nonzero constants exclude the proportional and shifted-proportional exceptions. At corank one use the [all-height strict interlacing proof](https://github.com/ProgramComputer/open-math-research/blob/e6724cb96ff30e8469b7bbc54208666623ce74f6/topics/balanced-arrays/no-full-row.md). At rank one the coefficients are $h!/((h-dk)!(k!)^d)$, interpreted as zero for $dk>h$. Thus $P_n=P_N-(d/N)qP_N'$; simplicity of the negative roots from the [rank-one Jacobi multiplier argument](https://github.com/ProgramComputer/open-math-research/blob/e6724cb96ff30e8469b7bbc54208666623ce74f6/topics/balanced-arrays/finite-linear-reduction.md) excludes common roots in Ding's interlacing, and the displayed derivative identity puts the new rightmost root first.

**Verification.** Run the accompanying checker with Python 3 in isolated mode. It proves the finite difference inequalities used in (4) from the labeled-array counts, checks (1) at and away from equality, and checks strict alternation directly on example rows by signed Euclidean chains. The unbounded-height step is the Newton expansion; the width and prefix theorems in Sections 1–4 are analytic.

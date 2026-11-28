# Eventual real-rootedness at every fixed count in the Gessel–Zhuang conjecture

**Theorem.** Choose any one of parts (a)–(g) of [Gessel and Zhuang, Conjecture 7.1](https://arxiv.org/html/2306.15785v3#S7.SS1), and fix its conditioning count $k$ (nonnegative for peaks, positive for runs). For all sufficiently large $n$, the slice polynomial $P_{n,k}(t)$ has only real, nonpositive zeros. For the non-elementary rows described below, the zeros are simple: one is zero and all the others are strictly negative. The elementary rows satisfy the conjecture at **every** size at which they are nonempty. So do (a)–(d) at $k=1$ and (e)–(g) at $k=3$ (§4).

The order of quantifiers matters. The threshold can depend on $k$; this does not prove the conjecture for all pairs $(n,k)$. The proof gives signs at enough points to count **all** zeros, not just a limiting proportion of them.

## 1. Reducing a row to finitely many rational functions

Write $T(z)=4z/(1+z)^2$, $R(x)=(1+x)/(1-x)$. Give the rows in (a)–(g), in that order, the indices
```math
 r=2k+2,\quad 2k+1,\quad 2k+1,\quad 2k+2,\quad k,\quad k,\quad k .
```
For each positive index $s$ put
```math
 (a_s,h_s)=
 \begin{cases}
 (0,0)&\text{inverse peak column},\\
 (\lfloor s/2\rfloor,s\bmod 2)&\text{inverse left peak column},
 \end{cases}
 \qquad b_s=a_s+h_s-1 .
```
With $n$ implicit, set
```math
 K_s(z)=[x^n]\frac{R(x)^{a_s}}{(1-x)^{h_s}(1-zR(x)^s)} .
```
There is a positive normalization of the transformed row of the form
```math
 S_n(z)=K_r(z)+\sum_{1\le s<r} c_s(n)K_s(z),
 \qquad |c_s(n)|=O_r(n^{\lfloor(r-s)/2\rfloor}).                 \tag{1}
```
Here $S_n(z)$ equals $P_{n,k}(T(z))$ times a positive constant and the column factor $(1+z)^{n+\epsilon}/(1-z)^{n+1}$, with $\epsilon=1$ for inverse peaks, $0$ for inverse left peaks. In particular their signs agree for $-1<z<0$.

Here are the details of extraction from the part (a) generating identities for the corresponding seven distributions in [Gessel–Zhuang, §§3–5](https://arxiv.org/html/2306.15785v3). Use $u^2$ for the first source variable in the peak and left peak identities, and $u$ in the two run identities and the birun identity. Multiply a left peak identity by an extra $u$. In the following table the coefficients on the right are the $K_s$ at the indicated powers $u^s$: summing the inverse index $j$ gives the geometric denominator $1-zR^s$. The horizontal factors multiply the **whole** permutation polynomial, before extraction; constants independent of $u,z$ are positive and suppressed.

| Conditioning statistic | Substitution in the permutation polynomial | Horizontal factor, including extra shift | Indices on the right |
|---|---|---|---|
| peaks | $T(u^2)$ | $(1+u^2)^{n+1}/(1-u^2)^{n+1}$ | even |
| left peaks | $T(u^2)$ | $u(1+u^2)^n/(1-u^2)^{n+1}$ | odd |
| up-down runs | $2u/(1+u^2)$ | $(1+u^2)^n/((1-u^2)^{n-1}(1-u)^2)$ | all |
| biruns ($n\ge2$) | $2u/(1+u^2)$ | $(1+u)^3(1+u^2)^{n-1}/((1-u)(1-u^2)^n)$ | all |

For example, for inverse left peaks and even $s$ the numerator on the right is $R^{s/2}$, and for odd $s$ it is $R^{(s-1)/2}/(1-x)$. Interchange the variables in the mixed peak identity for (d). The even index zero contributes nothing for $n>0$. Equating coefficients through $u^r$ gives a triangular system. Its diagonal consists of positive constants independent of $n$ from the leading terms of the substitutions. In an entry $r-s$ places above the initial power, every factor with $n$ in its exponent is a power of $1\pm u^2$. Hence that entry is a polynomial in $n$ of degree at most $\lfloor(r-s)/2\rfloor$. The inverse triangular system has the same bound (the degrees add along chains), proving (1).

Assume henceforth $r\ge3$. Then $S_n(0)=0$: the inverse peak weight includes $t$; for inverse left peaks the only permutation with constant weight is the identity, which is outside these rows.

## 2. The dominant pair and its sign grid

Abbreviate $(a_r,h_r,b_r)$ by $(a,h,b)$. For $0<v\le1$ put $z=-v^r$, $\theta=\pi/r$, $w=v e^{i\theta}$. The exact filter for every $s\ge1$ is
```math
 K_s(z)=\frac{2^{1-h_s}}s\sum_{\omega^s=z}
 \frac{\omega^{-b_s}}{(1-\omega)^{2-h_s}}
 \left(\frac{1+\omega}{1-\omega}\right)^{n-1+h_s}.                \tag{2}
```
Indeed the average of $\omega^{-a_s}/(1-\omega R)$ is $R^{a_s}/(1-zR^s)$ since $0\le a_s<s$. Taking $[x^n]$ after multiplication by $(1-x)^{-h_s}$ gives (2) for $n\ge1$.

In $K_r$ the pair at $w,\bar w$ contributes $2A\cos\Psi_n(v)$, where $A>0$ is the absolute value of the individual summand including its prefactor, and
```math
 \phi=\arg R(w),\qquad \delta=-\arg(1-w),\qquad
 \Psi_n=(n-1+h)\phi+(2-h)\delta-b\theta .
```
Use continuous arguments starting at zero for $\phi,\delta$. Both increase strictly: their tangents in the interior are $2v\sin\theta/(1-v^2)$ and $v\sin\theta/(1-v\cos\theta)$. At $v=1$ they reach $\pi/2$ and $(\pi-\theta)/2$. Thus the phase starts at $-b\theta$ and ends at $(n+1)\pi/2$ for inverse peaks and $n\pi/2$ for inverse left peaks, since in the latter case $a+h/2=r/2$. Let $d$ be the integer part of this endpoint divided by $\pi$. It is the combinatorial upper bound on the degree. For each $2\le j\le d$ take the unique $v_j$ with $\Psi_n(v_j)=j\pi$. We prove that eventually **every** such sample has sign $(-1)^j$.

### Large samples: $nv\longrightarrow\infty$

All estimates here are for fixed $r$. Write $\rho=|R(w)|$. For $\omega=q e^{i\alpha}$,
```math
 \log|R(\omega)|=\operatorname{arctanh}\frac{2q\cos\alpha}{1+q^2}.
```
A zero numerator in $R$ is interpreted by continuity in modulus. There is $\eta>0$ such that $\log\rho\ge\eta v$ and every pole other than the dominant pair in (1) has $\max(1,|R(\omega)|)/\rho\le e^{-\eta v}$. For $s=r$ this uses the strict cosine gap. For $s<r$ the radius $q=v^{r/s}$ is at most $v$ and the maximal cosine is $\cos(\pi/s)<\cos\theta$. Use monotonicity of $2q/(1+q^2)$ and compactness away from zero; at zero the leading log-modulus gap is at least a positive constant times $v$ by expansion. The factors $|1-\omega|$ are bounded above and away from zero for all these poles. In particular
```math
 A\ \ge C v^{-b}\exp(\eta n v)
```
for some $C>0$ (decrease $\eta$ if needed). The other terms at index $r$ are $o(A)$.

We must also beat the powers of $n$ in (1), even when $nv$ grows more slowly than $\log n$. Fix $s<r$ and put $e=\lfloor(r-s)/2\rfloor$, $y=nv$. If $n v^{r/s}\ge1/2$, then $y\ge 2^{-s/r}n^{1-s/r}$. All prefactors and their ratios to the leading prefactor are bounded by powers of $n$ here. The exponential gap gives $c_sK_s=o(A)$.

Otherwise $|z|\le (2n)^{-s}$. On the circle $|z|=n^{-s}$, (2) gives $|K_s(z)|=O(n^{b_s})$ for $n\ge2$, since $|\omega|=1/n$ and $|R(\omega)|^{n}=O(1)$ uniformly as $n\to\infty$. By Cauchy's coefficient bound,
```math
 |K_s(z)-K_s(0)|=O(n^{b_s+s}|z|).
```
Now $e+b_s+s-r<b$: in the peak column $b_s=b=-1$, and in the left peak column $b_s\le b$ while $e<r-s$. The centered lower term times $c_s$ is $O(n^{e+b_s+s-r} y^r)$. Its constant term vanishes in the peak column. In the left peak column the constant term times $c_s$ is $O(n^b)$ because $b_s=\lfloor(s-1)/2\rfloor$ and $e+b_s\le b$. Comparing with $A\ge C n^b y^{-b}\exp(\eta y)$ gives $c_sK_s=o(A)$ whenever $y\to\infty$. This proves the claimed grid signs in this regime.

### Bounded samples: the zeros nearest the origin

Suppose $nv\to y>0$. Since $S_n(0)=0$, subtract the constant term from **each** kernel in (1). By the strict exponent inequality just proved, every centered lower term is $o(n^b)$. In (2) for $s=r$, the points $n\omega$ tend to the $r$ solutions of $\xi^r=-y^r$, and $R(\omega)^{n-1+h}\to e^{2\xi}$. Filter the exponential series: the powers that survive in the average of $\xi^{-b}e^{2\xi}$ have indices $b+r\ell\ge0$. If $b\ge0$, the $\ell=0$ term is canceled by $n^{-b}K_r(0)\to 2^a/b!$, as follows by extracting $[x^n]\,(1+x)^a/(1-x)^{b+1}$. If $b=-1$, there is no such term. It follows that
```math
 n^{-b} S_n(-v^r)\longrightarrow
 -2^{1-h+b+r} y^r E_{r,\mu}(-(2y)^r),\qquad
 \mu=r+b+1,\qquad
 E_{r,\mu}(x)=\sum_{\ell\ge0}\frac{x^\ell}{\Gamma(r\ell+\mu)}.       \tag{3}
```
The shift by $r$ in the second parameter is essential.

We use the zero localization theorem of [Popov and Sedletskii, *Distribution of Roots of Mittag-Leffler Functions*, Theorem 3.1.1, (3.1.4) and (3.2.1)](https://doi.org/10.1007/s10958-013-1255-3). In our notation, for $r>2$, $0<\mu\le2r-1$ and $m\ge1$ it gives
```math
 \operatorname{sgn} E_{r,\mu}(-\xi_m^r)=(-1)^m,\qquad
 \xi_m=\frac{m\pi+(\mu-1)\theta}{\sin\theta}.
```
Indeed the simple negative roots lie one per successive interval ending at these sample points, starting from $E_{r,\mu}(0)>0$. The source's parameter $\rho$ is $1/r$. Our $\mu$ is $r$ in the peak column and $r+1+\lfloor(r-1)/2\rfloor\le2r-1$ in the left peak column.

For fixed $j\ge2$, the phase equation gives $nv_j\to y_j=(j\pi+b\theta)/(2\sin\theta)$: $v_j\to0$, $\phi/v\to2\sin\theta$, and $\delta\to0$. Since $2y_j=\xi_{j-1}$, the minus sign in (3) gives precisely $(-1)^j$. These signs for fixed $j$ and the large-sample estimate exhaust the grid: if there were failures at unbounded sizes, pass to a sequence with $nv_j\to\infty$ or with $nv_j$ bounded. In the latter case $j$ is bounded by the phase formula, so pass to a constant index. Both alternatives contradict the established signs.

Finally choose a fixed $0<y<y_2$ sufficiently small that (3) is negative. The ordered grid starts with a negative sign at $v=y/n$, then has alternating signs at $v_2,\ldots,v_d$. If the last sample is $v=1$, (2) is continuous there and its nonzero sign persists just inside. As $v$ increases, $T(-v^r)$ runs strictly from $0$ to $-\infty$. The intermediate value theorem gives $d-1$ distinct negative roots, in addition to the root at zero. The degree bound $d$ proves both completeness and simplicity.

## 3. The elementary rows

For $r=1$ the left-peak-zero and up-down-run-one classes contain only the identity. The birun-one class consists of the two monotone permutations for $n\ge2$, both of inverse peak number zero.

For $r=2$, write
```math
 O_n(t)=\sum_{j\ge0}\binom n{2j+1}t^j,\qquad
 B_n(t)=\sum_{j\ge0}\binom n{2j}t^j .
```
A peakless permutation decreases to $1$ and then increases. For each $i=1,\ldots,n-1$, its inverse has a descent at $i$ precisely when $i+1$ is on the decreasing side. Thus all binary descent words of length $n-1$ occur exactly once. The same is true for permutations increasing to $n$ and then decreasing: the descent bit at $i$ records whether $i$ is on the decreasing side. In a binary word, $j$ runs of ones are specified by $2j$ boundaries among $n$. For $j$ internal zero-to-one transitions, prepend a one and append a zero; the $2j+1$ changes can be chosen among the $n$ gaps. Thus the inverse left peak enumerator is $B_n$, and the inverse peak enumerator with the source shift is $tO_n$.

Parts (a),(d) at $k=0$ therefore give $tO_n,B_n$. The up-down-run-two class is the second (mountain) class with the identity removed, giving $t(O_n-1), B_n-1$ for (e),(f). The birun-two class is the disjoint union of the two classes with **both** monotone permutations removed from each, giving $2t(O_n-2)$ for (g). Ignore an empty row.

At $t=-\tan^2 u$ for $0<u<\pi/2$, the even and odd binomial expansions give
```math
 B_n(t)=\frac{\cos(nu)}{\cos^n u},\qquad
 O_n(t)=\frac{\sin(nu)}{\sin u\cos^{n-1}u}.
```
At $u=j\pi/n$, $1\le j\le\lfloor n/2\rfloor$, both $B_n$ and $B_n-1$ have sign $(-1)^j$, using the one-sided limiting sign at the endpoint. For $B_n$ start at $u=0$ with a positive sign; for $B_n-1$ count the zero at the origin instead. For $n\ge3$ the denominator in the odd formula is strictly less than $1/2$, since $\sin u\cos u\le1/2$. Thus $O_n-c$ for $c=0,1,2$ has sign $(-1)^j$ at $u=(2j+1)\pi/(2n)$, $0\le j\le\lfloor(n-1)/2\rfloor$, again using a limiting sign if necessary. These sign changes attain the degree bounds. Sizes $1,2$ are immediate. This proves the elementary cases without a size threshold.

## 4. The first non-elementary count, at every size

In fact **(a)–(d) at $k=1$ and (e)–(g) at $k=3$ hold without an asymptotic threshold** (for nonempty slices). Here is an explicit estimate; the finite part $n<40$ is tested from the exact source rows by the accompanying integer verifier.

Suppress the positive factors as in (1). For (a),(d) the row is $K_4-2nK_2$. For (b),(c) it is $K_3-(2n+1)K_1$. For (e),(f) it is $K_3-2K_2+(3-2n)K_1$, and for (g) it is $K_3-4K_2+(11-2n)K_1$. These are the first terms of the triangular extraction in §1. For example, after scaling the run rows to unit diagonal, if the first three rows are $X_1,X_2,X_3$, the up-down run identity gives $K_1=X_1$, $K_2=X_2+2X_1$, and $K_3=X_3+2X_2+(2n+1)X_1$.

Let $n\ge40$, $y=nv$, and use the samples $j\ge2$ of §2. The error means the sum of **all** terms except the leading conjugate pair. The following are upper bounds on the absolute error divided by $2A$, multiplied by $\rho^{n-1}$:

| Case | Upper bound |
|---|---|
| $r=3$, inverse peaks | $1/2+6\sqrt v+(31/10)yv$ |
| $r=3$, inverse left peaks | $1/2+6v+(31/10)y$ |
| $r=4$, either column | $1+4y$ |

For clarity, in the first row $2A=(4/3)v\rho^{n-1}/|1-w|^2$; the remaining third root is $-v$, $|K_2|\le2v^{3/2}$, and $|K_1|\le2v^3$. In the second row $2A=(2/3)v^{-1}\rho^n/|1-w|$; now $|K_2|\le2$, $|K_1|\le1$, and only (f) has a $K_2$ term, of coefficient $-2$. For both, use $|1-w|\le1$, $|R(-v)|\le1$ and $|c_1|\le2n+1$. In the third row $2A=v^{-b}\rho^{n-1}/|1-w|^2$. The other two poles have modulus of $R$ equal to $1/\rho$, with at least as large a denominator. The second-index poles are $\pm i v^2$, with $|R|=1$, whence $|K_2|\le2v^2$ for inverse peaks and $|K_2|\le2$ for inverse left peaks. These bounds give the table directly from (2).

It remains to check that each displayed bound is strictly less than $\rho^{n-1}$. If $v\ge1/4$, then $y\ge10$ and $\log\rho\ge 2v\cos\theta/(1+v^2)\ge v/2$, so $\rho^{n-1}\ge e^{39y/80}>7+4y$. If $v\le1/4$, then $\phi\le(32/15)v\sin\theta$, $\delta\le1/3$ and $\log\rho\ge(32/17)v\cos\theta$.

* For $r=3$ and inverse peaks, the phase equation gives $(n-1)\phi\ge5\pi/3-2/3$, hence $y>2$. The bound in the table is at most $7/2+y<e^{9y/10}\le\rho^{n-1}$.
* For $r=3$ and inverse left peaks, $n\phi\ge7\pi/3-1/3$, hence $y>3$. The upper bound is at most $2+(31/10)y<e^{9y/10}\le\rho^{n-1}$.
* For $r=4$, $(n-1)\phi\ge7\pi/4-2/3$, hence $y>2$. Now $1+4y<e^{5y/4}\le\rho^{n-1}$.

Each exponential-versus-affine inequality follows at the indicated left endpoint from the exponential series and persists by differentiation. Thus all samples have the required signs. For the initial negative sign, the coefficient of $t$ is positive: take the descent word of any permutation in the conditioning class, and realize it as the inverse descent word of a valley permutation, using the bijection in §3. Its inverse is still in the specified class because each conditioning statistic depends only on the descent word. The valley has zero peaks and has one left peak unless it is the identity, which these rows exclude. With zero constant term, the counting argument of §2 now works at every $n\ge40$.


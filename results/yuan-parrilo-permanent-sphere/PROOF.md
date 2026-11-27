# The Yuan–Parrilo permanent bound in order four and at low rank

Let $A=V^*V$ be Hermitian positive semidefinite of order $n\ge 1$, with Gram vectors $v_1,\ldots,v_n$. Write $P(z)=\prod_i v_i^*z$ and let $M$ denote its maximum absolute value on the **complex unit sphere** of the Gram span. Thus the objective in [Yuan–Parrilo, Conjecture 5.1](https://doi.org/10.1007/s10107-021-01616-3) is $r(A)=n^nM^2$. Restricting to the Gram span does not change this maximum: projection preserves every linear factor, and normalization can only increase the product.

**Results.**

1. $\operatorname{per}(A)\le r(A)$ holds for every $n\le 4$, without a restriction on the rank.
2. It also holds for $\operatorname{rank}(A)=d$ whenever $(d)_{n-1}\le n^{n-1}$, where $(d)_k=d(d+1)\cdots(d+k-1)$. In particular $n\ge 2d-2$ suffices. This rules out every complex rank-two and rank-three counterexample at every order.
3. At all ranks and orders, $r(A)\ge c^n\operatorname{per}(A)$ for the absolute constant

$$
c=e\exp\!\left(-\sum_{j=0}^{\infty}\frac{\log(1+2^j)}{2^{j+1}}\right)>\frac56.
$$

The third result is an approximation, **not** the conjectured constant $1$. The first case not covered by results 1 and 2 is order five, rank four. None of the arguments depends on a numerical optimization.

## Normalizations and two lower bounds on the sphere maximum

A zero column makes both sides zero. Otherwise, scaling individual columns multiplies both sides by the product of their squared scale factors. For the order-four proof take $\|v_i\|=1$ and put $h=\operatorname{per}(A)$. Let $T$ be the average of the $n!$ elementary tensors obtained by permuting $v_1\otimes\cdots\otimes v_n$. Symmetrization is an orthogonal projection, so

$$
\|T\|^2=\langle T,v_1\otimes\cdots\otimes v_n\rangle=\frac{h}{n!}.
$$

This is the squared Bombieri–Weyl norm of $P$. In contrast, if $g$ is standard circular complex Gaussian, then $\mathbb E|P(g)|^2=h$ by the complex Wick formula. The usual linear polarization bound gives $r(A)\ge\prod_i\|v_i\|^2$, which is insufficient: for $n$ identical unit columns the product of squared norms is $1$ whereas the permanent is $n!$.

By [Banach's symmetric multilinear norm theorem](https://doi.org/10.1112/blms/bdl033), the maximum of $|\langle T,u_1\otimes\cdots\otimes u_n\rangle|$ over $n$ unit vectors is already attained with all $u_i$ equal. Testing at $u_i=v_i$ therefore gives our first bound:

$$
r(A)\ \ge\ n^n\left(\frac{h}{n!}\right)^2.
\tag{1}
$$

For the second bound, partition the factors into two nonempty blocks $I,J$, of sizes $m,l$. Let $a,b$ maximize their respective products with $\|a\|^2=m$ and $\|b\|^2=l$. Average the logarithm of the product at $a+e^{it}b$ over uniform $t$. The circle mean of $\log|\alpha+e^{it}\beta|$ is $\log\max(|\alpha|,|\beta|)$ (Jensen's formula, including equality of the moduli by the integrable logarithmic singularity). Each factor thus contributes at least its block's log value. The mean of $\log\|a+e^{it}b\|^2$ is at most $\log(m+l)$ by concavity. Applying the pointwise bound $|P(y)|^2\le r(A)(\|y\|^2/n)^n$ before integrating proves

$$
r(A)\ge r(A[I])\,r(A[J]).
\tag{2}
$$

Here $A[I]$ denotes a principal submatrix; orthogonality between blocks is **not** assumed. For two unit columns with inner-product magnitude $a$, the two-factor maximum on the sphere of radius $\sqrt{2}$ is $(1+a)^2$. To see this, the sum of their two squared overlaps is at most $2(1+a)$ by the top eigenvalue of the two-column Gram matrix. AM–GM gives the upper bound; the normalized sum of the phase-aligned columns gives equality.

## Order four

Group the six off-diagonal magnitudes by opposite edges of the complete graph: $(a,a')$ on $(12,34)$, $(b,b')$ on $(13,24)$, and $(c,c')$ on $(14,23)$. Set $s=\max(a+a',b+b',c+c')$. Applying (2) to the three pairings gives

$$
r(A)\ge \max\big\{(1+a)^2(1+a')^2,(1+b)^2(1+b')^2,(1+c)^2(1+c')^2\big\}\ge(1+s)^2.
$$

If $h\ge 9/4$, (1) gives $r(A)\ge(4/9)h^2\ge h$. If $h<9/4$ and $s\ge 1/2$, the pairing bound gives $r(A)\ge 9/4>h$. It remains to handle $s<1/2$.

Put $p=aa'+bb'+cc'$. Taking absolute values termwise in the permutation expansion:

- The identity contributes $1$. The six transpositions contribute the sum of the six squared magnitudes, at most $3s^2-2p$.
- Each triangle contributes two oriented three-cycles. The four triangle monomials are distinct terms of $(a+a')(b+b')(c+c')$, so these terms contribute at most $2s^3$.
- The three double transpositions contribute $(aa')^2+(bb')^2+(cc')^2$. The six four-cycles contribute at most $2(aa'bb'+aa'cc'+bb'cc')$. Together these are bounded by $p^2$.

Now $0\le p\le 3s^2/4\le 2$. Consequently

$$
h\le 1+3s^2-2p+2s^3+p^2\le 1+3s^2+2s^3\le(1+s)^2\le r(A),
$$

where the penultimate inequality uses $s+s^2\le 1$. This proves the order-four claim.

Smaller orders follow by adjoining orthogonal unit columns, i.e. padding by an identity block. In fact $r(A\oplus B)=r(A)r(B)$: for block orders $m,l$ and squared radii $t,u$ with $t+u=m+l$, the blockwise upper bounds give a factor $(t/m)^m(u/l)^l\le1$, with equality attainable at $t=m,u=l$. Both objectives equal $1$ on an identity block. In particular the constant $1$ in the exact upper bound cannot be decreased.

## Rank-sensitive bound

Here the unit-column normalization is unnecessary. With $d$ the dimension of the Gram span, $U$ Haar uniform on its complex unit sphere, and $q=n-1$, the sphere moment identity is

$$
\mathbb E\,|U^{\otimes q}\rangle\langle U^{\otimes q}|
=\frac{\Pi_{\mathrm{sym},q}}{\binom{d+q-1}{q}},
$$

where $\Pi_{\mathrm{sym},q}$ is orthogonal projection onto symmetric $q$-tensors. Indeed, the corresponding Gaussian moment sums the $q!$ permutation operators by Wick's formula, while its independent radial factor has moment $\mathbb E\|g\|^{2q}=(d)_q$. For $q=0$ use the scalar identity.

Contract the first $n-1$ legs of $T$ against $U^{\otimes(n-1)}$. Banach's theorem bounds the norm of the remaining vector by $M$, since its norm tests just one additional unit direction. By the moment identity the mean squared norm of the contraction is $\|T\|^2/\binom{d+n-2}{n-1}$. Hence

$$
\frac{\operatorname{per}(A)}{r(A)}
\le \frac{n!\binom{d+n-2}{n-1}}{n^n}
=\frac{(d)_{n-1}}{n^{n-1}}.
$$

For $n\ge2$, the $n-1$ factors in the numerator have arithmetic mean $d+(n-2)/2$, which is at most $n$ when $n\ge 2d-2$. The $n=1$ case is immediate.

## A dimension-free approximation by doubling the polynomial

Let $a_k=\mathbb E|P(g)|^{2k}$. Use independent standard complex Gaussian vectors $X,Y,U,V$ in the Gram span and set $F(x,y)=P((x+y)/\sqrt2)^k$. As a polynomial in two blocks, $F$ is a sum of at most $(k+1)^n$ products $f(x)h(y)$: for each linear factor raised to power $k$, expand by the binomial theorem.

Expand $F$ in Gaussian-orthonormal polynomial bases in $x$ and $y$, with coefficient matrix $D$. It has rank at most $(k+1)^n$ by this product expansion, and $\operatorname{tr}(DD^*)=a_k$ since $(X+Y)/\sqrt2$ is standard Gaussian. Orthogonality of the four independent bases gives

$$
\mathbb E\!\left[F(X,Y)F(U,V)\overline{F(X,V)F(U,Y)}\right]
=\operatorname{tr}\big((DD^*)^2\big)\ge\frac{a_k^2}{(k+1)^n},
$$

using Cauchy–Schwarz on the nonzero eigenvalues.

The expectation can also be computed exactly. Take $W=(X+Y+U+V)/2$, $S=(X+Y-U-V)/2$ and $H=(X-Y-U+V)/2$. These are independent standard complex Gaussians by orthogonality of the coefficient rows. The two unbarred arguments of $P$ are $(W+S)/\sqrt2,(W-S)/\sqrt2$; the two barred arguments have $H$ in place of $S$. Conditional on $W$, a holomorphic polynomial in the centered circular Gaussian $S$ has expectation its value at zero, since all nonconstant holomorphic moments vanish. The same applies to $H$, independently. The displayed expectation is therefore $4^{-nk}a_{2k}$. We obtain

$$
a_{2k}\ge \left(\frac{4^k}{k+1}\right)^n a_k^2.
\tag{3}
$$

For $k=2^m$, iterating (3), taking logarithms and dividing by $k$ gives

$$
\frac{\log a_k}{k}\ge\log a_1+n\log k-n\sum_{j=0}^{m-1}\frac{\log(1+2^j)}{2^{j+1}}.
$$

For uniform unit $U_0$, radial decomposition, the full support of sphere measure and Stirling's formula give, respectively,

$$
a_k=(d)_{nk}\,\mathbb E|P(U_0)|^{2k},
\qquad
\lim_{k\to\infty}\left(\mathbb E|P(U_0)|^{2k}\right)^{1/k}=M^2,
\qquad
\lim_{k\to\infty}\frac{(d)_{nk}^{1/k}}{(k!)^{n/k}}=n^n.
$$

Thus $a_k^{1/k}/(k!)^{n/k}\to r(A)$. Since $k/(k!)^{1/k}\to e$ and $a_1=\operatorname{per}(A)$, the claimed constant follows.

For an exact simple lower estimate, split $\log(1+2^j)=j\log 2+\log(1+2^{-j})$. The first part of the weighted sum is $\log 2$; the first three terms of the second part give $\tfrac18\log45$, and its remaining tail is at most $\sum_{j\ge3}2^{-2j-1}=1/96$. Hence $c\ge e^{95/96}/(2\cdot 45^{1/8})>5/6$. The last strict inequality follows already from the degree-six Taylor lower bound for the exponential, checked in the accompanying exact script.

This argument does not give the general upper bound with constant one. Already for $k=2$, the factor per column in (3) is $16/3$ instead of the $6$ that would yield lossless doubling after division by factorials. The rank estimate does not control how the nonzero singular values are distributed.

## Scope and verification

The paper's lower bound $(n!/n^n)r(A)\le\operatorname{per}(A)$ is not at issue. [Chalmers, Theorem 1.1](https://doi.org/10.13140/RG.2.2.15004.86408) treats the stronger Pate tensor-product conjecture in order three; this proof of order four uses neither that result nor permanent-on-top.

The Lean theorem <code>YuanParriloPermanentSphere.permanent_four_matching</code> verifies the cycle estimate for actual complex order-four permanents, even without positive semidefiniteness. It does **not** formalize the analytic comparisons with the sphere maximum, the rank theorem, or (3). The Python verifier independently audits the cycle polynomial and the rational constant estimate; neither numerical search nor a computational certificate is needed as a premise of the proof.

# Log-concavity of the stable second hypersimplices

**Theorem (Solus's unimodality conjecture, strengthened).** Let $n\ge3$ and $1\le r\le\lfloor n/2\rfloor$. Label the sites of an $n$-cycle and let $P_{n,r}$ be the convex hull of all $e_a+e_b$ for which $a,b$ have circular distance at least $r$. Then the coefficients of $h^*(P_{n,r};x)$ are log-concave and have no internal zeros. In particular they are unimodal.

This settles [Solus, Conjecture 3.4.5, p. 73](https://uknowledge.uky.edu/math_etds/32/), also [Braun–Solus, Conjecture 4.22](https://doi.org/10.1016/j.jcta.2018.03.002). The vertices are **sums**, not signed differences. The proof uses no numerical cutoff.

## A subset formula, and why it gives log-concavity

Let $h_k$ denote the coefficient of $x^k$. On the same labeled cycle define

$$
\mathcal S_k=\{S\subseteq[n]:\ |S|=2k,\quad |S\cap I|\le k\text{ for every cyclic interval }I\text{ of }r+1\text{ sites}\}.
$$

**Coefficient identity:** $h_k=|\mathcal S_k|$ for every $k\ge0$. Note the shift from $r$ to $r+1$. Equivalently $h_k$ counts the $2k$-vertex subsets admitting a perfect matching with edges of circular distance at least $r+1$, counting a subset just once. Indeed, if the interval condition holds, pair opposite sites in the cyclic list of the $2k$ marked sites. If an arc between paired sites had length at most $r$, some interval of $r+1$ sites would contain both endpoints and at least $k+1$ marks. Conversely each allowed matching edge contributes at most one mark to such an interval.

We first deduce the theorem from the identity. Represent $S$ by its prefix counts $u_0,\ldots,u_n$, with $u_0=0$, $u_n=2k$, and successive differences in $\{0,1\}$. Extend by $u_{a+n}=u_a+2k$. The remaining conditions are exactly

$$
u_{a+r+1}-u_a\le k \qquad (0\le a<n).
$$

Take two prefix vectors, one from $\mathcal S_{k-1}$ and one from $\mathcal S_{k+1}$. Their midpoint has successive differences between 0 and 1, interval differences at most $k$, and endpoints $0,2k$. Its extension increases by $2k$ per period. **Rounding every coordinate down, or rounding every coordinate up, preserves all these bounds.** Indeed $b\le a+c$ with $c$ integral implies $\lfloor b\rfloor\le\lfloor a\rfloor+c$, and likewise for ceilings. Rounding commutes with the integral period increment, so this includes intervals crossing the label cut.

Apply the discrete midpoint inequality of [Halikias, Klartag and Slomka, Theorem 1.2](https://arxiv.org/pdf/1911.04392). At $\lambda=1/2$, for finite integer-vector sets $U,V$, it bounds $|U||V|$ by the product of the cardinalities of the coordinatewise floor and ceiling sets of $(U+V)/2$ (apply the theorem to indicators). Both midpoint sets here lie in the prefix representation of $\mathcal S_k$. Consequently $h_{k-1}h_{k+1}\le h_k^2$. The matching interpretation rules out internal zeros: deleting a matched pair preserves matchability. This proves unimodality once the identity is established.

## Proof of the coefficient identity

**1. A transfer count for a circle.** Put $2t$ labeled bins on a circle, $t>0$, and distribute $n$ beads with at least $\delta$ beads per bin, where $\delta=0$ or $1$. Require every $t$ consecutive bins to contain between $\alpha$ and $n-\alpha$ beads. On the state set $\{\alpha,\ldots,n-\alpha\}$ let $J$ reverse the order ($h\mapsto n-h$), and set

$$
M(z)_{hh'}=\frac{z^{|h-h'|}}{1-z^2}.
$$

The number of occupancy vectors is $[z^n]\operatorname{tr}(J(z^{2\delta}M(z))^t)$. To see this, slide a semicircle one bin at a time for $t$ steps. It ends at the complement of the starting semicircle. If $a$ beads leave and $b$ enter in a step, then $b-a=h'-h$. The generating function of all such pairs $a,b\ge\delta$ by degree $a+b$ is $z^{2\delta}M_{hh'}$. The trace with $J$ specifies an end state $n-h$ given a start $h$. Conversely the steps fill all antipodal bin pairs; selecting degree $n$ forces $\sum(a+b)=n$ and the end condition forces $\sum(b-a)=n-2h$. Thus the actual initial semicircle contains $\sum a=h$; there is no multiplicity from a free starting height. The last $t$ slides satisfy the bounds by complementation. On an empty state set the count is zero.

**2. Apply the count to lattice points.** Write $L(t)=|tP_{n,r}\cap\mathbb Z^n|$. The integer vectors counted are exactly the nonnegative $g_1,\ldots,g_n$ of sum $2t$ with each $r$ consecutive coordinates summing to at most $t$. Necessity holds at the vertices after scaling. For sufficiency, list the $2t$ tokens given by multiplicities $g_i$ cyclically and pair token $j$ with token $j+t$. An arc of fewer than $r$ site-edges between paired tokens would give an $r$-window with at least $t+1$ tokens; ties at a site are included in this argument. Thus the vector is a sum of $t$ allowed vertices. By clearing denominators this also gives the real polytope description (rational points are dense in the rational constraint polytope). If $n>2r$, the constant coordinates $2/n$ satisfy the inequalities strictly in the sum hyperplane, giving dimension $n-1$. If $n=2r$, the vertices have disjoint antipodal supports: projection onto the first $n/2$ coordinates identifies the polytope and its affine lattice with the standard simplex. Then $h^*=1$, and $\mathcal S_k$ is empty for $k>0$ since no matching edge can have distance $r+1$. Hence assume $n>2r$.

Use the $g_i$ as the consecutive **gaps** of $n$ beads on a circle of circumference $2t$. Zero gaps are allowed. The $r$-gap bound says every semicircle of integer bins $(p,p+t]$ contains at least $r$ beads: use the $r$-th successor of the last occurrence at $p$, or of the last bead before $p$ if that bin is empty. Conversely the bound at occupied bins gives the gap condition starting at every bead, including earlier occurrences at the same position. Complementation gives the upper bound $n-r$. Writing $A(t)$ for the count in step 1 with $\alpha=r$ and $\delta=0$, we have $2tL(t)=nA(t)$. On one side choose an initial bin for the labeled gap sequence; on the other choose a starting bead occurrence in the occupancy vector. Occurrences at each bin are ordered from arrival to departure, so the correspondence also holds with zero gaps. These are labeled objects, not rotation classes. Thus, for the $M,J$ on the states $r,\ldots,n-r$,

$$
L(t)=\frac n{2t}[z^n]\operatorname{tr}(J M(z)^t).
$$

**3. Extract a coefficient of the numerator.** The inverse matrix $Q(z)=M(z)^{-1}$ has end diagonals $1$, inner diagonals $1+z^2$ and both off-diagonals $-z$, with all other entries zero (multiply the matrices). Its size is at least 2. Let $E$ be the diagonal projector onto the inner sites. The key simplification is

$$
\frac{Q((1-x)w)-xI}{1-x}=Q(w)-xw^2 E=:K(w,x).
$$

Define $F(w,x)=\log(\det K_-/\det K_+)$, where subscripts restrict to the $-1,+1$ eigenspaces of $J$. All matrices in this identity commute with $J$. The formal trace–log identity $-\log\det(I-xM)=\sum_{t\ge1}x^t\operatorname{tr}(M^t)/t$, subtracted between the two spaces, sums the preceding formula for $L(t)$. More explicitly, use $\det(I-xM)=\det(Q-xI)/\det Q$ in each space, and absorb the Ehrhart multiplier $(1-x)^n$ by substituting $z=(1-x)w$ before taking $[w^n]$. Including $L(0)=1$ gives

$$
h^*(P_{n,r};x)=(1-x)^n+\frac n2[w^n]\big(F(w,x)-F((1-x)w,0)\big).
$$

Scalar determinant factors from $1-x$ are constant in $w$ and disappear. Now expand $F$ in **$x$**. Since $K=Q(w)(I-x w^2 M(w)E)$,

$$
F(w,x)=F(w,0)+\sum_{k\ge1}\frac{x^k}{k}\operatorname{tr}\big(J(w^2 M(w)E)^k\big).
$$

Write $c=(n/2)[w^n]F(w,0)$. The first identity becomes $(1-c)(1-x)^n+(n/2)[w^n]F(w,x)$. The latter summand has degree at most $\lfloor n/2\rfloor$ by the second identity, while the Ehrhart numerator of an $(n-1)$-dimensional lattice polytope has degree at most $n-1$. Comparing $x^n$ gives $c=1$. In particular

$$
h(x)=\frac n2[w^n]F(w,x),\qquad
h_k=\frac n{2k}[w^n]\operatorname{tr}\big(J_\circ(w^2 M_\circ(w))^k\big)\quad(k\ge1),
\tag{1}
$$

where $\circ$ denotes the principal submatrix on $r+1,\ldots,n-r-1$. Indeed the projector forces every visited index in the twisted trace into the inner sites, which are closed under $J$.

**4. Apply the same count to marked subsets.** This last trace is step 1 again, now with $2k$ bins, $\alpha=r+1$ and **$\delta=1$**. It counts ordered positive gaps summing to $n$ for which every $k$ consecutive gaps sum to at least $r+1$ (the upper bound is equivalent by complementation). Place these gaps between $2k$ distinct marked sites of the labeled $n$-cycle. The condition says precisely that no $k+1$ successive marks fit in $r+1$ consecutive sites, equivalently $S\in\mathcal S_k$. The number of these subsets is $n/(2k)$ times the gap count: specify one starting site, then divide by the $2k$ choices of starting mark. This is exactly the prefactor in (1). Finally $h_0=1=|\mathcal S_0|$. This completes the coefficient identity and the proof for every $n,r$.

## Appendix: closed binomial evaluation and the line of real roots

Neither this computation nor the finite checks below are needed for log-concavity. They give an efficient evaluation of the subset counts and a stronger conclusion on one line of parameters. Set $d=n-2r>0$, $p=1+(1-x)w^2$, and $D_\pm=\det K_\pm$. Define the end continuants $f_0=f_1=1$ and $f_{k+1}=p f_k-w^2 f_{k-1}$ for $k\ge1$. Expansion along the last row gives these determinants. Folding the path of $d+1$ sites gives

$$
\frac{D_-}{D_+}=
\begin{cases}
f_s/(f_{s+1}-w^2f_{s-1}) & d=2s,\\[2pt]
(f_{s+1}+w f_s)/(f_{s+1}-w f_s) & d=2s+1 .
\end{cases}
$$

In the first case the antisymmetric center vanishes; in the symmetric case its two neighbors give twice the usual $-w^2 f_{s-1}$ term in the last continuant step. In the second case reflection at the middle edge adds $+w$ or $-w$ to the last diagonal.

Adopt $\binom ab=0$ for $b<0$ or $b>a$ with $a\ge0$. For $0\le i\le\lfloor n/2\rfloor$ put $B_i=\binom n{2i}$. For each **positive odd** $j$ with $j(d+2)\le n$, put $a=(n-j(d+2))/2$, $A=a+2j-1$, $B=a+jd-1$. Then

$$
h_i=B_i-\sum_j\frac n j
\left(\binom A{i+j-1}\binom B{i-j}
      -\binom A{i+j}\binom B{i-j-1}\right).
\tag{2}
$$

There are no higher nonzero coefficients. We derive the formula to keep track of the signs and the finite boundaries.

Let $\lambda,\mu$ be the roots of $y^2-py+w^2$, ordered by $\lambda(0)=1$, and write $\Delta=\lambda-\mu$, $v=w/\lambda$. The continuant is

$$
f_k=\frac{(1-\mu)\lambda^k-(1-\lambda)\mu^k}{\Delta}.
$$

In the folded quotients the finite-length factor is $(1-T)/(1+T)$ in **both** parities, where $T=((1-\lambda)/(1-\mu))v^d$. In fact, for even $d$, $f_{s+1}-w^2 f_{s-1}=(1-\mu)\lambda^s+(1-\lambda)\mu^s$, leaving prefactor $1/\Delta$. For odd $d$ use $(\mu\pm w)/(\lambda\pm w)=\pm v$, leaving prefactor $(1+v)/(1-v)$. The log of either prefactor contributes exactly $B_i$ in (1). For even $d$ factor $\Delta^2=(1-(1+\sqrt{x})^2w^2)(1-(1-\sqrt{x})^2w^2)$; for odd $d$ use $((1+v)/(1-v))^2=(p+2w)/(p-2w)$ and $p\pm2w=(1\pm(1+\sqrt{x})w)(1\pm(1-\sqrt{x})w)$. The extracted polynomial is the even part of $(1+\sqrt{x})^n$.

Set $u=w/(1-\mu)$ and $Y=uv$. Since $(1-\lambda)(1-\mu)=xw^2$ and $\mu=wv$, one has $u=w(1+Y)$, $v=w(1+xY)$, and $Y=w^2(1+Y)(1+xY)$. Hence $T=xw^{d+2}(1+Y)^2(1+xY)^d$. Expanding $\log((1-T)/(1+T))=-2\sum_{j\ {\rm odd}}T^j/j$ explains the range in (2). In particular each subtracted polynomial has nonnegative coefficients. With $y=w^2$, formal series reversion gives

$$
[y^a]\,(1+Y)^{2j}(1+xY)^{jd}
=[b^a]\,(1-xb^2)(1+b)^{a+2j-1}(1+xb)^{a+jd-1}.
$$

Indeed substitute $y=b/((1+b)(1+xb))$ in the coefficient residue; the logarithmic Jacobian is $(1-xb^2)/((1+b)(1+xb))$. Extracting $x^{i-j}$ gives (2). Each correction has degree at most $a+j=(n-jd)/2\le r$; thus $h_i=B_i$ for $i>r$.

**Real-rooted boundary family.** For $n=2m$ and $r=m-2$ the even folded numerator is $f_2=1-xy$, and its denominator is $f_3-y f_1=1-(1+2x)y-x(1-x)y^2$, with $y=w^2$. By (1),

$$
h(x)=a^m+b^m-x^m,\qquad
a,b=\frac{1+2x\pm\sqrt{1+8x}}2 .
$$

This polynomial has degree $m$ with leading coefficient 1 (also immediate from (2) since $m>r$). For $x<-1/8$, take $a=\rho e^{\mathrm i\theta}$ in the upper half plane, $b=\overline a$. Then $\rho^2=x(x-1)>x^2$. As $x$ runs from $-1/8$ to $-\infty$, the argument varies continuously from $0$ to $\pi$ in the limit. At each $\theta=k\pi/m$ for $0\le k<m$, the term $2\rho^m\cos(m\theta)$ strictly dominates $x^m$ in absolute value and has sign $(-1)^k$. The initial sign also holds at $-1/8$. Use the points in first-hitting order and finally use the leading sign $(-1)^m$ at a sufficiently negative argument. The $m$ intervening intervals each contain a distinct zero, exhausting the degree. Newton's inequalities give log-concavity.

**Independent checks.** Run `python3 -I verify.py` in this directory: the binomial formula is checked against all distinct sums of vertices through $n=10$ and, independently, against direct enumeration of the window-constrained subsets through $n=16$. The verifier also rejects a corrupted coefficient vector and checks log-concavity for all 25,599 admissible pairs through $n=320$. The optional command `python3 -I verify.py --band 321 1024 --jobs 22` checks all 189,625 pairs in that range with $d\le 2+8\sqrt{7n}$. The theorem covers the parameters outside these computations as well.

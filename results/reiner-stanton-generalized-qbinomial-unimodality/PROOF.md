# The centred difference of two Gaussian polynomials

**Theorem (Stanley–Zanello, Conjecture 1.1(iv)).** Fix $k\ge5$. For all sufficiently large $m$ (depending only on $k$), the polynomial

$$
\binom{m}{k}_q-q^{k(m-b)/2+b-2k+2}\binom{b}{k-2}_q
$$

is nonnegative and unimodal for **every** integer $b$ with $k-2\le b\le(km-4k+4)/(k-2)$ and $k(m-b)$ even, except $b=(km-4k+2)/(k-2)$ when integral. At that exception the polynomial is not unimodal.

Parts (i)–(iii) ($k=2,3,4$) and the case $k=5$ of (iv) were proved by [Stanley and Zanello](https://arxiv.org/abs/1711.10033v2). [Koutschan, Uncu and Wong](https://arxiv.org/abs/2302.04067v2), Theorems 12–13 and Corollary 14, proved (iv) for $k=6,7$. We prove (iv) for every fixed $k\ge5$; we do **not** give a classification of the sporadic failures for small $m$. Nor does the asymptotic quantifier imply the original Reiner–Stanton assertion at every finite parameter.

## 1. Where a uniform bound is needed

Write $G_{k,L}=\binom{L+k}{k}_q$, $L=m-k$, $h=k-2$, $A=b-h$ and $s=(kL-hA)/2$. The hypotheses say that $A$ and $s$ are nonnegative integers. The two terms of $F=G_{k,L}-q^sG_{h,A}$ are symmetric about $kL/2$, counting zeros outside their support. Write $\Delta P(n)=[q^n](1-q)P$, with coefficients zero in negative degrees, and $\Delta^2 P(n)=[q^n](1-q)^2P$. It suffices to prove $\Delta F(n)\ge0$ for $0\le n\le\lfloor kL/2\rfloor$, including $n=0$.

On this half-interval the smaller term satisfies

$$
|\Delta G_{h,A}(n-s)|\le 2^h(1+n)^{h-2}.
\tag{1}
$$

Indeed, expand the numerator of the product formula
$G_{h,A}=\prod_{j=1}^h(1-q^{A+j})/(1-q^j)$.
In the first difference, the factor $1-q$ cancels. Each of the $2^h$ terms counts, with a sign, solutions of $2x_2+\cdots+hx_h=v$ for some $v\le n$; fixing all but one multiplicity determines the last, and there are no solutions for $v<0$. In particular (1) is $O_k(L^{k-4})$ for $L\ge1$, **uniformly in $A$ and $s$**. A strict increase of $G_{k,L}$ by just one would not suffice.

## 2. The two scaled differences of the larger rectangle

Let $B_k$ be the density of the sum of $k$ independent uniform variables on $[0,1]$, equivalently the $k$-fold convolution of the unit interval indicator. With $x_+=\max(x,0)$,

$$
B_k(x)=\frac1{(k-1)!}\sum_{i=0}^k(-1)^i\binom{k}{i}(x-i)_+^{k-1}.
$$

The formula follows from the triangular density at $k=2$ by integrating over a unit interval at each step. We will use, for $r=1,2$, the estimate

$$
\Delta^r G_{k,L}(n)=\frac{L^{k-r-1}}{k!}B_k^{(r)}(n/L)
                  +O_k(L^{k-r-2})
\tag{2}
$$

**uniformly** at all integers $0\le n\le kL+1$ as $L\to\infty$. Uniformity at the knots and near the centre matters here; one cannot simply difference a pointwise coefficient asymptotic.

To see (2), put $e=k-r-1$ and
$H_r(q)=(1-q)^r/\prod_{j=1}^k(1-q^j)$.
Its pole at $1$ has order $e+1$ and leading coefficient $1/k!$ in powers of $1-q$. At any other root of unity of order $t\ge2$ its pole has order $\lfloor k/t\rfloor\le\lfloor k/2\rfloor\le k-3\le e$. A partial fraction of order $a$ at a root of unity contributes a constant times a phase of modulus one times $\binom{v+a-1}{a-1}$ in degree $v\ge0$. Thus

$$
[q^v]H_r(q)=\frac{v^e}{k!\,e!}+O_k((1+v)^{e-1})
\quad (v\ge0).
$$

For $v<0$ both the coefficient and the positive-part leading term are zero. The numerator of $G_{k,L}$ makes $\Delta^rG_{k,L}(n)$ the alternating sum of these coefficients at $v=n-|S|L-\sum_{j\in S}j$ over subsets $S\subseteq\{1,\ldots,k\}$. In the leading term, replacing $v_+^e$ by $(n-|S|L)_+^e$ costs $O_k(L^{e-1})$: the arguments differ by at most $k(k+1)/2$ and their positive parts are at most $kL+1$. This also covers indices where only one argument is positive. Grouping by $|S|$ now gives the $r$-th derivative of the displayed truncated-power formula, proving (2).

## 3. A gap bound all the way to the middle

We claim that, for $L$ large enough in terms of $k$,

$$
\min_{L\le n\le\lfloor kL/2\rfloor}\Delta G_{k,L}(n)
   \ \ge\ c_k L^{k-3}
\tag{3}
$$

for some $c_k>0$. The loss of one power relative to the bulk is important.

Each $B_j$ is symmetric about $j/2$, positive on $(0,j)$ and zero outside $[0,j]$. For $j\ge3$,
$B_j'(x)=B_{j-1}(x)-B_{j-1}(x-1)$.
Starting from the triangle $B_2$, this gives $B_j'(x)>0$ for $0<x<j/2$: the point $x$ is in the interior of the smaller support and is strictly closer than $x-1$ to $(j-1)/2$. In particular

$$
B_k''(k/2)=B_{k-1}'(k/2)-B_{k-1}'(k/2-1)
           =-2B_{k-1}'(k/2-1)<0 .
$$

Choose a small $\eta>0$ with $1<k/2-\eta$ such that $B_k''$ is bounded above by a strictly negative constant on $[k/2-2\eta,k/2+2\eta]$. On the compact interval $[1,k/2-\eta]$, $B_k'$ has a strictly positive minimum. Hence (2) gives $\Delta G_{k,L}(n)\ge a_k L^{k-2}$ on this latter interval of $n/L$, and $\Delta^2G_{k,L}(n)\le-d_k L^{k-3}$ on the central interval, for constants $a_k,d_k>0$ and all sufficiently large $L$.

To handle the last lattice step, let $N=\lfloor kL/2\rfloor$ and $D(n)=\Delta G_{k,L}(n)$. Symmetry gives $D(N+1)=-D(N)$ if $kL$ is even, and $D(N+1)=0$ if it is odd. Applying the second-difference estimate at $N+1$ therefore gives $D(N)\ge d_k L^{k-3}/2$ in either case. For $k/2-\eta\le n/L\le N/L$, every step from $D(n)$ to $D(N)$ is decreasing by the same second-difference estimate. This proves (3). By (1), $h-2=k-4<k-3$, so (3) implies $\Delta F(n)>0$ for every $L\le n\le N$, eventually in $L$, simultaneously for all admissible $b$.

## 4. The left edge and the exception

In degree $0\le n\le L$ the numerator factors $1-q^{L+j}$ have no effect. Thus $\Delta G_{k,L}(n)$ counts partitions of $n$ with parts in $\{2,\ldots,k\}$. If $n<s$, there is nothing to subtract. If $s\le n\le L$, then $hA=kL-2s\ge(k-2)L=hL$, so $A\ge L$ and the smaller first difference also counts unrestricted partitions, of $n-s$ with parts in $\{2,\ldots,h\}$.

For $s=0$ include these partitions directly. For $s\ge2$ append a fixed partition of $s$ into twos and threes (one three and the rest twos for odd $s$). This is an injection, even when the appended parts already occur, since the fixed multiplicities can be subtracted. It gives $\Delta F(n)\ge0$ at the entire left edge. Together with (3) and symmetry this proves nonnegativity and unimodality for $s\ne1$.

Finally, $s=1$ is exactly $(k-2)b=km-4k+2$. For $L\ge2$ the larger polynomial starts $1+q+2q^2$ and $A\ge1$, so the shifted difference starts with coefficients $1,0,1$. This is not unimodal. The thresholds used above depended only on the fixed $k$, as required. $\square$

### Exact finite checks

The companion `verify.py` compares product-formula arrays with the $q$-Pascal identity, checks the published small-height classifications on their stated ranges, and separately counts the small-$m$ deviations from the eventual rule. These checks and the corruption controls do not replace the asymptotic argument. For background on fixed-height coefficient asymptotics see [Stanley–Zanello](https://arxiv.org/abs/1503.06367); for related central concavity arguments see [Zbarsky](https://arxiv.org/abs/1408.3895).

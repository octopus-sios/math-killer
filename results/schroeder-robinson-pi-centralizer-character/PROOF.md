# Prime-set row sums: the missing constituents of simple groups

**Theorem.** If $G$ is a nonabelian finite simple group and $\chi\in\mathrm{Irr}(G)$ has full character-table row sum zero, then for **every** prime set $\pi$,
```math
 S_\pi(G,\chi):=\sum_{K\in\mathrm{Cl}_\pi(G)}\chi(g_K)\ \ge 0.
```
Here $g_K$ runs once over the classes of elements whose orders have all their prime factors in $\pi$, including the identity. These pairs $(G,\chi)$ are [classified by Heide, Saxl, Tiep and Zalesski](https://arxiv.org/abs/1209.1768): $G=\mathrm{PSU}_n(q)$ with $n\ge3$ odd and $\gcd(n,q+1)=1$, and $\chi$ is the Weil character of degree $(q^n-q)/(q+1)$. We obtain the exact boundary:
```math
 S_\pi(G,\chi)=0\quad\Longleftrightarrow\quad
 q^d+1\text{ is a }\pi\text{-number for every odd }d\le n,\ d\ge1.
```
For instance the degree-ten row of $\mathrm{PSU}_5(2)$ has sum zero already for $\pi=\{3,11\}$, whereas its sum is four for $\pi=\{2\}$.

This eliminates the entire set of simple-group **pairs** singled out before [Schroeder's Theorem 3.6](https://arxiv.org/html/2609.26464v1#S3). That theorem proves nonnegativity in dimension three. A full row sum of zero does not control the sign after columns have been removed. The abelian simple case is elementary: a nontrivial row of a cyclic group of prime order has sum zero or one according as the prime belongs to the set or not. Nor does our theorem assert positivity for *other* characters of a group merely because one of its rows is missing from the conjugation representation.

**Further conclusions.**
- For all field sizes and dimensions, every Weil component and determinant twist on the full unitary group has nonnegative local sum (§§1–2). The same holds for every Weil row of $\mathrm{SU}_n(q)$, $n\ge3$, on that group and on any central quotient to which the row descends (§§4–5). For dimensions at least three we determine **all** the zeros on these rows. In particular every Weil row of a nonabelian simple projective unitary group with positive full row sum remains strictly positive for every prime set.
- The **whole** local centralizer function is a character on $\mathrm{SL}_2(q)$ and $\mathrm{PSL}_2(q)$ for every $\pi$ (§6), and on $A_n$ whenever $2\in\pi$ (an application of Sundaram, §7).
- For fixed $\pi$, the all-row assertion for $H$ is equivalent to that for the regular wreath product $H\wr C_\ell$ for **every prime** $\ell$ (§8).
- On all 26 sporadic simple groups, even a sum over **any set of element orders containing order one** is strictly positive on every irreducible row (exact character-table computation, §9).

The connection with [Conjecture 3.5](https://arxiv.org/abs/2609.26464) is that $S_\pi$ is the multiplicity of $\chi$ in $\Pi_{\pi,G}$: the class size cancels the centralizer in the inner product, and inversion permutes the selected classes. Integrality is Schroeder's Theorem 3.2. His Theorem 3.3 and [Robinson, §§5 and 8](https://arxiv.org/abs/2505.03976) cover the prime-complement and the $\pi$-separable cases. The unrestricted conjecture, including for simple groups in general, does not follow.

## 1. Two series on the full unitary group

Write $`U_n=\mathrm{GU}_n(q)`$ for the isometries over $`\mathbb F_{q^2}`$, $`p=\mathrm{char}(\mathbb F_q)`$, $`M=q+1`$, and $`Z=\mu_M`$ for the norm-one scalars. Fix a generating complex character $\lambda$ of $Z$. The total unitary Weil character is $(-1)^n(-q)^{\dim\ker(g-I)}$ (dimension over $`\mathbb F_{q^2}`$). On its $\lambda^r$ central eigenspace the character is
```math
w_{r,n}(g)=\frac{(-1)^n}{M}\sum_{z\in Z}\lambda(z)^{-r}(-q)^{\dim\ker(zg-I)} .
```
See [Katz–Tiep, §16.4](https://web.math.princeton.edu/~nmk/kt15_105.pdf). Indices $r,k$ are taken modulo $M$. We allow the same formula in dimension one, where the $r=0$ component is zero. In odd dimension $w_{0,n}(1)=(q^n-q)/M$.

Let $u_\pi$ mean the largest divisor of $u$ supported on $\pi$. Put
```math
a=M_\pi,\qquad b=M/a,\qquad N_d=(q^d-(-1)^d)_\pi,\qquad
J=\begin{cases}\{1,2,\ldots\}&p\in\pi,\\ \{1\}&p\notin\pi.\end{cases}
```

We use the unitary conjugacy-class parametrization ([Schaeffer Fry–Vinroot, §§2.1–2.2](https://www.math.wm.edu/~vinroot/SURealClassesJGT_Revised.pdf)). A class assigns a partition to each orbit of $F:x\mapsto x^{-q}$ on $\overline{\mathbb F}_q^\times$. At every eigenvalue in that orbit the parts are its Jordan block lengths. Dimension counts all the blocks at all eigenvalues. For a $\pi$-class use only roots of $\pi$-order and block lengths $j\in J$: a nontrivial unipotent part has $p$-power order. These conditions are sufficient as well as necessary.

For the determinant twist $\lambda^k\circ\det$, set $L=a/\gcd(a,k)$ (its order on the $\pi$-part of $Z$). Define $A(t)$ by taking in degree $n$ the sum of the twist over the $\pi$-classes of $U_n$, with constant term one. Define $B(t)$ in the same way, but weight the summand also by $(-q)^{\dim\ker(g-I)}$ and replace $t$ by $-t$. Write their coefficients $A_n,B_n$. In the ring of formal power series,
```math
\begin{aligned}
\log A(t)&=\sum_{m\ge1}\alpha_m t^m/m,&
\alpha_m&=\sum_{\substack{jd=m,\ j\in J\\ L\mid j}} jN_d,\\
\log B(t)&=\sum_{m\ge1}\beta_m t^m/m,&
\beta_m&=(-1)^m\left(\alpha_m+\sum_{jd=m,\ j\in J}j\big((-q)^d-1\big)\right).
\end{aligned}
```

Indeed the multiplicity of a block of length $j$ at an orbit $O$ of size $s$ gives the geometric factor with ratio $t^{js}\lambda^k(\prod_{x\in O}x)^j$. In its logarithm, the term of repeat number $d/s$ counts the points fixed by $F^d$ on this orbit, with weight from the product of $d$ successive iterates. The group of all $\pi$-roots fixed by $F^d$ has order $N_d$. The map $x\mapsto x^{1-q+\cdots+(-q)^{d-1}}$ from the *whole* fixed group onto $Z$ is surjective: the absolute exponent is $(q^d-(-1)^d)/M$ and the domain is cyclic of order $q^d-(-1)^d$. On $\pi$-parts it is therefore onto the subgroup $Z_\pi$. Character orthogonality gives $N_d$ if $L\mid j$ and zero otherwise. This proves the first logarithm. At eigenvalue $1$, each block, regardless of its length, contributes one to the kernel dimension. Before the substitution $t\mapsto-t$ the weighting thus multiplies $A(t)$ by
```math
\prod_{j\in J}\frac{1-t^j}{1+qt^j}.
```
This gives the second logarithm. No diagonalizability assumption has been made when $p\in\pi$.

The sum for $w_{r,n}(\lambda^k\circ\det)$ vanishes unless $a\mid r+nk$: scalar multiplication permutes the $\pi$-classes. When this divisibility holds the sum equals
```math
\frac{a}{M}\left(B_n+(-1)^n c_r A_n\right),\qquad
c_r=\begin{cases}
 b-1&r=0,\\
 -1&r\ne0,\ a\mid r,\\
 0&a\nmid r .
\end{cases} \tag{1}
```
For $z\in Z_\pi$ change variables $g\mapsto zg$ in the central projection. The determinant phase cancels the central Fourier phase by the divisibility condition, giving $aB_n/M$. For $z\notin Z_\pi$ there is no eigenvalue $z^{-1}$, and $\sum_{z\notin Z_\pi}\lambda(z)^{-r}=a c_r$.

## 2. The coefficient inequality

We prove that $B_n\ge0$; when $b\ge2$ we prove the stronger
```math
 B_n\ \ge\ (b-1)^{\,n\bmod 2}\,A_n . \tag{2}
```
As $\alpha_m\ge0$, all $A_n\ge0$. These estimates in (1) prove the full-unitary assertion (the case $c_r=-1$ requires $b\ge2$).

For odd $m$, every $d$ in its divisor sum is odd, and the $\pi'$-part of $q^d+1$ is at least $b$ since $M\mid q^d+1$. Thus $\beta_m\ge (b-1)\alpha_m$. For even $m$ put $D_m=\beta_m-\alpha_m$. If $J=\{1\}$ then $D_m=q^m-1>0$. Otherwise pair the terms indexed by odd $d\mid m$ and $2d$; their sum is
```math
\frac{m}{2d}(q^d+1)(q^d-3).
```
The unpaired terms ($4\mid d$) are positive. For $q\ge3$, therefore, $D_m\ge0$. In these cases (2) follows by expanding the exponential: a monomial of odd total degree must use at least one odd index, and when $b\ge2$ every additional factor $b-1$ is at least one. For $b=1$ nonnegative logarithm coefficients suffice without a comparison.

It remains to handle $q=2$ and $J=\{1,2,\ldots\}$. Here $D_2=-3$, while $D_m\ge0$ at every other even index. Indeed only the pair starting at $d=1$ is negative, giving $-3m/2$. For $4\mid m$ the $d=4$ term alone covers this. For $m=2s$ with $s\ge3$ odd, the pair starting at $s$ covers it, since $(2^s+1)(2^s-3)\ge3s$. Also $D_m\ge6m$ if $6\mid m$, by just the pairs starting at $1$ and $3$.

* If $a=3$ and $L=1$, then $\alpha_2=2N_1+N_2\ge9$, so even $\beta_2\ge0$. If $a=3$ and $L=3$, remove the factor $(1+t)^3$ from $B(t)$. For odd $m$ the $j=1$ contribution to $\beta_m$ is now understood *before removal* as $2^m+1$ since $L\nmid1$; all other contributions are nonnegative. Removing the factor subtracts $3$ at odd log indices and adds $3$ at even ones (in the normalization $m[t^m]\log$). The remaining logarithm is nonnegative. This proves the required positivity when $b=1$.
* If $a=1$, then $b=3,L=1$ and the even log deficit at $2$ is real. Compare after extracting the following small factors from $A,B$, respectively:
```math
 H(t)=\frac1{(1-t)(1-t^2)},\qquad
 Q(t)=\frac{1+t}{(1-t)(1-t^3)^2}.
```
Their normalized logarithm coefficients are $h_m=1+2[2\mid m]$ and $u_m=2[m\text{ odd}]+6[3\mid m]$ (brackets denote indicators). We have $\alpha_m\ge h_m$ by the $d=1$ term and, at $m=2$, the $d=2$ term. At odd $m$, $\beta_m-2\alpha_m\ge0$; if $3\mid m$, the $d=3$ term alone gives an excess $6(m/3)$ since $N_3=(2^3+1)_\pi=1$. Hence $\beta_m-u_m\ge2(\alpha_m-h_m)$ at odd indices. At even indices $\beta_m-u_m\ge\alpha_m-h_m$ since $D_m\ge-3$ and $D_m\ge3$ when $6\mid m$. The exponential comparison now works for $B/Q$ against $A/H$ with factor two at odd degrees.

Finally $[t^n]Q\ge 2^{n\bmod2}[t^n]H$. Here $[t^n]H=1+\lfloor n/2\rfloor$. The first six coefficients of $Q$ are $1,2,2,4,6,6$; for $n\ge6$ its coefficient exceeds that at $n-3$ by at least three (expand $(1-t^3)Q$). Thus $[t^n]Q\ge n+1$ for $n\ge3$. Multiplication preserves the even/odd comparison, since two odd factors give a factor four, not less than one. This establishes (2) in the last case.

## 3. The exact support in the full unitary group

Now let $n\ge3$ and write $W(n,r,k)$ for the sum in (1), including the scalar obstruction. Use two conditions:
- (O): the dimension is odd and $q^d+1$ is a $\pi$-number for every positive odd $d\le n$.
- (X): $(n,q)=(3,2)$, with $2\in\pi$ and $3\notin\pi$.

**Zero criterion.** Apart from the forced zero when $a\nmid r+nk$, the sum vanishes exactly when $r=0$ and either (O) holds with $k=0\bmod M$, or (X) holds.

First suppose $n$ is odd. If $L>1$, the $j=1$ term in the logarithm gives the strict surplus $\beta_n-(b-1)\alpha_n\ge q^n+1$: the other terms of the difference are nonnegative by §2. For $b\ge2$ this makes the exponential comparison strict by its single-index term of degree $n$; for $b=1$ it makes $B_n>0$. In the case $q=2$, unrestricted $J$ and $L=3$, the odd log coefficient after extracting $(1+t)^3$ is still strictly positive since $2^n+1>3$. Thus no compatible row with $L>1$ vanishes. If $L=1$, compatibility implies $a\mid r$; for nonzero $r$ the parenthesis in (1) is $B_n+A_n>0$ since $\alpha_1=a>0$.

For $r=0$, $L=1$ and $b=1$ we necessarily have $k=0$. The odd log coefficients of $B$ are sums of the nonnegative numbers $j(q^d+1-N_d)$ for $jd=m$, $j\in J$. They vanish through odd degree $n$ exactly under (O) (take $j=1$). All log coefficients here are nonnegative, with $\beta_2>0$ by §2. Any strictly positive odd term of degree at most $n$ can be padded with copies of degree two, so $B_n=0$ exactly under (O).

For $r=0$, $L=1$ and $b\ge2$, the comparison (2) is strict for $J=\{1\}$ or $q>3$: use $D_2>0$ and the monomial with one index $2$ and $n-2$ indices $1$. For $q=3$ we have $b=4$, and the $n$ indices $1$ alone give strictness since $(b-1)^n>b-1$. For $q=2$, unrestricted $J$ and $a=1$, the degree-four comparison after extraction is strict since $D_4=9>u_4-h_4=-3$; the positive coefficient of $Q$ at $n-4$ then gives strictness for odd $n\ge5$. The remaining case is (X), where the log recurrence gives $A_3=3$, $B_3=6$ and $b=3$, hence zero.

Now let $n$ be even, so $n\ge4$. For $J=\{1\}$ or $q\ge3$ one has $D_n>0$: in the paired-divisor proof of §2 use $d=n$ if $4\mid n$ and the pair starting at $n/2\ge3$ otherwise (for unrestricted $J$). Thus $B_n>0$; when $c_r=-1$ we have $b\ge2$ and retaining the index $n$ in the exponential comparison gives $B_n-A_n\ge D_n/n>0$. In the case $q=2$ and unrestricted $J$, if $a=3$ then $b=1$ and either $\beta_n=\alpha_n+D_n>0$ for $L=1$, or $\beta_n+3>0$ in the logarithm after extraction for $L=3$. If $a=1$, the even-index inequality after removing $Q,H$ is strict at index $n$: we have $D_n>u_n-h_n$ since $D_n\ge0$ and in fact $D_n\ge6n$ for $6\mid n$. The constant terms of both extracted factors are one, so $B_n>A_n$. This proves the criterion.

To deduce the headline theorem, let $n$ be odd and $\gcd(n,M)=1$. Then $U_n=\mathrm{SU}_n(q)\times Z$, since $z\mapsto z^n$ is an automorphism of $Z$. The special group equals its projective quotient and the Weil component with $r=0$ is trivial on $Z$. Its local sum on the special group is $W(n,0,0)/a$, since the direct factor $Z$ contributes exactly $a$ local classes. The small case (X) does not satisfy coprimality, so the criterion gives exactly (O).

## 4. Passing to special and projective groups without coprimality

This step is needed for the further scope, not for the zero criterion. We explain why simply dividing a full-unitary sum by the number of scalars would in general be incorrect.

Take $`H=\mathrm{SU}_n(q)`$ and a subgroup $`D`$ of its scalar center. For a row $`w_{r,n}|_H`$ descending to $H/D$, assume $`\lambda^r|_D=1`$. The $\pi$-classes of $H/D$ are the orbits of $`D_\pi`$ on the $\pi$-classes of $H$: a lift has central $\pi'$-part that can be removed, and two $\pi$-lifts of conjugate elements differ after conjugation by a $\pi$-scalar. The weighted orbit count for the row is therefore the average, over $`z\in D_\pi`$, of the row sums on the classes fixed under multiplication by $z$.

For a full-unitary class in $H$, let $h$ be the gcd of $M$ and all the Jordan block lengths present. The class splits into $h$ special-unitary classes, by the [unitary class splitting formula, §2.2](https://www.math.wm.edu/~vinroot/SURealClassesJGT_Revised.pdf). If the full class is fixed by $z$, **all** these subclasses are fixed. Indeed, for a representative $x$ and its unipotent part $u$, the groups $\det C_{U_n}(x)\subseteq\det C_{U_n}(u)$ both have index $h$ in $Z$: the splitting formula gives this index, and the block lengths are the same, with the eigenvalues forgotten. Any conjugator from $x$ to $zx$ centralizes $u$. We can cancel its determinant with one from $C_{U_n}(x)$, producing a conjugator in $H$. This applies to each representative.

Put $e=|z|$. Use $h=\sum_{v\mid h}\varphi(v)$, where $\varphi$ is Euler's totient. For a fixed $v\mid M$ the contributing full classes have all block lengths multiples of $v$ and their eigenvalue data are invariant under multiplication by $\langle z\rangle=\mu_e$. If $p\notin\pi$, only $v=1$ occurs. These data exist only if $ev\mid n$. Put $m=n/(ev)$.

Pass from eigenvalues $x_0$ to $y_0=x_0^e$ and divide each block length by $v$. The $e$ roots in each fiber had identical partitions. Since $e$ is a $\pi$-number prime to $p$, every fiber over a $\pi$-root consists of exactly $e$ $\pi$-roots. The power map commutes with $F$. This gives exactly the $\pi$-class data of $U_m$, and expanding the fibers and the lengths is the inverse. There is one determinant constraint: the product of the $e$ roots of $X^e-y_0$ is $(-1)^{e-1}y_0$, so we retain the smaller classes represented by $y$ for which $\det(y)^v=(-1)^{(e-1)vm}$.

At a scalar eigenvalue $t^{-1}$ upstairs, the number of Jordan blocks is now $\dim\ker(t^e y-I)$ downstairs. The central projection formula gives
```math
 w_{r,n}(x)=(-1)^{n-m}\sum_{s:\ es\equiv r\pmod M}w_{s,m}(y).
```
Indeed $\lambda^r$ is trivial on $\mu_e$; after summing over the fibers of $t\mapsto t^e$ one gets the projector for its corresponding character on $Z^e$, equivalently the sum of the $e$ projectors for its extensions to $Z$. The determinant condition is imposed by character orthogonality on $Z$. To be explicit, write $W(m,s,k)$ for (1), or zero when its divisibility condition fails, i.e. the full-unitary sum with twist $k$. Define $a_D=|D_\pi|$. The desired special-quotient sum is
```math
\frac{1}{a_D M}
\sum_{e\mid a_D}\varphi(e)
\sum_{\substack{v\mid \gcd(M,n/e)\\v\in J}}\varphi(v)(-1)^{n-m}
\sum_{es\equiv r\ (M)}\ \sum_{k\bmod M}
 (-1)^{(e-1)vmk}W(m,s,vk),\qquad m=n/(ev). \tag{3}
```
For $q$ odd the generating character takes $-1\in Z$ to $-1\in\mathbb C$; for $q$ even, $e$ is odd. This explains the determinant phase in both characteristics. If $n$ is odd or $q$ even, all contributing $ev$ are odd. Both signs are then positive (the dimensions have the same parity), and §2 proves nonnegativity term by term, without a finite check.

For clarity, these central components do give individual Weil rows on $H$ for $n\ge3$. Their degrees are positive by the scalar projection at the identity. The squared absolute value of the total character is $q^{2\dim\ker(g-I)}$, the number of fixed vectors. Its norm squared on $H$ therefore counts vector orbits: zero, nonzero isotropic vectors, and one orbit for each of the $q-1$ nonzero norms. Witt's lemma gives transitivity for the full unitary group; the stabilizer of a nonzero vector contains a full unitary group on a nonzero orthogonal complement (split off a nondegenerate line or a hyperbolic plane), so its determinant is onto and the orbits do not split in $H$. The norm squared is thus $q+1$, and there are $q+1$ nonzero character summands. They must be distinct and irreducible.

## 5. Even dimension in odd characteristic

Here $n\ge4$ is even, $q\ge3$ is odd. The ranks $m$ in (3) need not be even. We bound the possible negative terms before the weighted orbit count's division by $a_D$. Put $g=\gcd(n,M)$ and $u=\gcd(n,a)$, so $u$ is the order of the special group's $\pi$-scalar center. If $u\nmid r$ the sum is zero: that center acts by scalar multiplication on the quotient's $\pi$-classes and the row transforms by a nontrivial central character. Assume $u\mid r$.

**Main term.** For $e=v=1$ the fixed-class sum, before division by $a_D$, is $M^{-1}\sum_k W(n,r,k)$. Exactly $uM/a$ indices satisfy $a\mid r+nk$. At each, the parenthesis in (1) is at least $D_n/n$, in the notation of §2. Indeed $\beta_n\ge D_n$ and the log coefficients of $B$ are nonnegative. If $c_r=-1$ then $b\ge2$ and the log coefficients of $B$ dominate those of $A$ in all degrees, so even $B_n-A_n\ge D_n/n$ by retaining the single index $n$ in the exponential difference. For $J=\{1\}$ one has $D_n=q^n-1$; for unrestricted $J$ either $4\mid n$ and the unpaired term $d=n$ gives this same lower bound, or $n/2$ is odd and its pair gives $(q^{n/2}+1)(q^{n/2}-3)$. Thus the main term is at least
```math
 \frac{u}{Mn}\left(q^n-2q^{n/2}-3\right)\ \ge\ \frac{u q^n}{2Mn}.
```

**Possible losses.** All terms with even $m$ have positive signs in (3). For odd $m$ use the absolute sum over *all* smaller classes (drop both the prime and determinant constraints). Each of the $e$ smaller rows has absolute sum at most
```math
 T_m=\sum_{[y]\text{ in }U_m}q^{\dim\ker(y-I)}
 =[t^m]\prod_{j\ge1}\frac{1-t^{2j}}{(1-qt^j)^2}.
```
The inequality follows by the triangle inequality in the central projection and the permutation of all classes by scalars. For the identity of series use §1 with all primes and trivial determinant twist: at block size one the unmarked series is $(1+t)/(1-qt)$ by its logarithm with $N_d=q^d-(-1)^d$. Marking the eigenvalue $1$ by $q$ per block gives an extra $(1-t)/(1-qt)$; take the product over all block sizes. Before division by $a_D$, the total possible loss is bounded by
```math
 E=\sum_{e\mid u}\ \sum_{\substack{v\mid\gcd(g,n/e)\\ m=n/(ev)\ \mathrm{odd}}}
 \varphi(e)\varphi(v)eT_m. \tag{4}
```
This only enlarges the sum: $a_D\mid u$ and the restriction $v\in J$ was dropped.

**Uniform cutoff.** The factors defining $T_m$ have nonnegative coefficients and are coefficientwise at most $(1-qt^j)^{-2}$. Isolating $j=1$ and evaluating the other majorants at $1/q$ gives
```math
 T_m\le (m+1)q^m\prod_{i\ge1}(1-q^{-i})^{-2}\le4(m+1)q^m,
```
since $\prod_{i\ge1}(1-q^{-i})\ge1-\sum_{i\ge1}q^{-i}\ge1/2$. The weights in (4) sum to at most $un^2$ by $\sum_{e\mid u}\varphi(e)=u$, $e\le n$ and $\sum_{v\mid g}\varphi(v)=g\le n$. In every loss $m\le n/2$. Comparing with the main term and using $M\le4q/3$, it suffices that
```math
 q^{n/2-1}>\frac{16}{3}n^3(n+2).
```
This holds for $n\ge32$, $q\ge3$, and for $n\ge6$, $q\ge101$: check $(n,q)=(32,3),(6,101)$, then increase $n$ by two (the right side grows by a factor at most $(8/6)^3(10/8)<3$ for $n\ge6$). For $n=4$ only $m=1$ can be a loss and $T_1=2q$, giving $E\le32uq$, below the main term for $q\ge101$.

**Bounded integer check.** For reproducibility, the last step is finite arithmetic, not a table lookup. For every even $4\le n\le30$, odd $3\le q\le99$ (even including non-prime-powers here), and every divisor $u$ of $g$, form (4) by multiplying the displayed factors for $T_m$ through degree $m$. Retain the pair if $u(q^n-2q^{n/2}-3)\le MnE$ for some $u$. This leaves only
```math
(q,n)=(3,4),\ (3,6),\ (5,6),\ (3,10).
```
For each such pair, enumerate all subsets of the prime divisors of $q\prod_{i=1}^n(q^i-(-1)^i)$, all $|D|\mid g$, and all $r\bmod M$ divisible by $|D|$. These are all effective prime sets, central quotients and descended Weil rows. Evaluate (3) using (1); the coefficients of $\exp(\sum l_i t^i/i)$ are computed by $c_0=1$, $h c_h=\sum_{i=1}^h l_i c_{h-i}$. Every result is nonnegative. The complete integer loops for this bounded part of the proof are in the companion verifier (function `finite_tail`); no external character data or numerical approximations are inputs. This finishes the even-dimensional case.

**Exact support on special groups and scalar quotients.** For all $n\ge3$, put $g=\gcd(n,M)$ and $u=\gcd(n,a)$. On any quotient to which the row descends, its sum is zero exactly in the following cases:
1. $u\nmid r$ (the central character is nontrivial on the special group's $\pi$-scalar center);
2. $r=0$ and either $g=1$ with (O), or (X) holds, in the notation of §3.

The scalar permutation argument for case 1 works in both characteristics and both parities. Assume $u\mid r$. If $n$ is odd or $q$ is even, every summand of (3) is nonnegative. There is at least one compatible twist in its $e=v=1$ term, since the congruence $nk\equiv-r\bmod a$ is solvable. For $r\ne0$ this already gives strict positivity by §3. For $r=0$ take $k=0$: a zero requires (O) or (X). Under (O) one has $a=M$, so if $g>1$ the *nonzero* compatible twist $k=M/g$ gives a positive term. If $g=1$, the direct-product argument of §3 applies. Under (X) we have $a=1$, hence $e=1$; the $v=1$ terms vanish by §3 and the only additional term has $v=3$, $m=1$ and the zero component $w_{0,1}$. This proves the criterion in this parity range.

In the remaining range ($n$ even, $q$ odd), the main-term comparison above is **strict** outside the four residual pairs. For those pairs the same exact loop, limited to $u\mid r$, has minima $13,115,2004,9602$ for $(q,n)=(3,4),(3,6),(5,6),(3,10)$ respectively. Hence there are no further zeros. In particular, on any nonabelian simple $\mathrm{PSU}_n(q)$ with $n\ge3$, descent gives $g\mid r$ and (X) is excluded. **Every descended Weil row with positive full sum has strictly positive sum for every prime set.**

**Independent checks.** In addition to the bounded proof step, the Python verifier compares the formulas with explicit partition-labeled eigenvalue orbits, determinant weights, splitting and scalar fusion, and with matrix-group conjugacy in dimension three over $\mathbb F_4$. These sample checks are not used to extrapolate to other dimensions.

## 6. In dimension two every row works

In dimension two $\mathrm{SU}_2(q)\cong\mathrm{SL}_2(q)$ and $\mathrm{PSU}_2(q)\cong\mathrm{PSL}_2(q)$. In fact **Conjecture 3.5 holds for these two groups, on all irreducibles**. Here there is a shorter direct argument.

Write $d=\gcd(2,q-1)$, let $c=1$ or $d$, and quotient $\mathrm{SL}_2(q)$ by its scalar subgroup of order $c$. We may take $q\ge4$: for $q=2,3$ the groups are solvable, covered by Schroeder's Theorem 3.3. Use the ordinary rank-one tables ([Böhmler–Farrell–Lassueur, odd characteristic](https://arxiv.org/abs/2107.06241); [Farrell–Lassueur, even characteristic](https://arxiv.org/abs/2205.01401)). We spell out the entries needed. In addition to the trivial and Steinberg characters, the rows come from the degree $q+1$ principal series and the degree $q-1$ cuspidal series, indexed by nontrivial linear characters $\theta$ of the split or nonsplit torus, respectively, up to inversion. For a quotient one takes the parameters trivial on the kernel. A quadratic parameter gives a sum of two exceptional rows, which have equal local sums: the diagonal automorphism interchanges them and preserves orders ([White, character degrees and outer automorphisms](https://www.math.kent.edu/~white/papers/sl2.pdf)). Thus it suffices to treat the series characters *before* splitting.

The quotient tori have orders $(q-1)/c$ and $(q+1)/c$, and their common scalar subgroup has order $d/c$. Write $z=(d/c)_\pi$. If the central character is nontrivial on the $\pi$-scalars the row sum is zero by central multiplication, so assume triviality there. Those scalars contribute $z$ times the degree. At each such scalar times a nontrivial unipotent there are $d$ classes, included exactly when $p\in\pi$. The series values there are $+1$ and $-1$, respectively. On the noncentral split torus the principal value is $\theta(t)+\theta(t^{-1})$ and the cuspidal value is zero; on the noncentral nonsplit torus the principal value is zero and the cuspidal value is $-(\theta(t)+\theta(t^{-1}))$.

For either torus let $P$ be its $\pi$-subgroup. The noncentral classes correspond to inversion orbits in $P$ outside the scalars. Summing $\theta(t)+\theta(t^{-1})$ on these orbits gives
```math
 |P|\,[\theta|_P=1]-z+\epsilon .
```
Here $\epsilon$ is the extra $\theta(t)=\pm1$ if there is a noncentral inversion-fixed element and is zero otherwise. This follows by first summing $\theta$ over all of $P$ and then correcting the fixed orbits. If $c=1$ there is no such correction: the only possible involution in a torus of $\mathrm{SL}_2(q)$ is scalar.

Put $i=[p\in\pi]$. The principal sum is at least $z(q+id)-1>0$. The cuspidal sum is at least
```math
 z(q-id)-\frac{q+1}{2c}-[c=2],
```
since $\theta$ is nontrivial on the whole torus, so if it is trivial on $P$ then $|P|$ is at most half the torus order. For $c=1$ this is nonnegative for $q\ge5$ by $d\le2$, and for $q=4$ by $d=1$. For $c=2$ one has $q\ge5$ odd and $q-2-(q+1)/4-1\ge0$. Finally the Steinberg row has degree $q$, value zero on nontrivial unipotent parts, and values $+1,-1$ on noncentral split and nonsplit semisimple classes. There are at most $(q+1)/(2c)$ noncentral nonsplit classes, by counting inversion pairs with at most one noncentral involution and deleting at least the identity. Hence this row too has positive sum. This covers every row of the two stated groups. In fact for $c=d$ and $q\ge4$ even the cuspidal lower bound is strictly positive: it is at least $(q-3)/2$ for even $q$ and $(3q-13)/4$ for odd $q$. Thus every simple projective group in this dimension has full support for every prime set.

## 7. Alternating groups when two is allowed

The $S_n$ result for arbitrary prime sets is already [Sundaram's Theorem 3.6](https://arxiv.org/abs/2107.06389). Simply restricting the symmetric-group character would give the *wrong centralizer* for some classes of $A_n$. Here is how to select the required summands when $2\in\pi$.

Fix $n\ge2$ and let $`k=(\mathrm{lcm}(1,\ldots,n))_\pi`$. Use the actual $`S_n`$-modules with Frobenius characteristics $`H_\lambda[F]`$ of [Sundaram, Theorem 5.6, identities (5.6.1) and (5.6.8)](https://arxiv.org/pdf/1603.05898). Here $`F_j`$ is induced from the linear character of the cyclic group generated by a $j$-cycle sending the generator to $\exp(2\pi i k/j)$; $`H_\lambda[F]`$ assembles its symmetric powers at the part multiplicities of $\lambda$. Write $`p_j`$ for the power sums. The two identities, **through degree $n$**, are
```math
\begin{aligned}
\sum_\lambda H_\lambda[F]t^{|\lambda|}
  &=\prod_{d\mid k}(1-p_dt^d)^{-1},\\
\sum_\lambda (-1)^{|\lambda|-\ell(\lambda)}H_\lambda[F]t^{|\lambda|}
  &=\prod_{\substack{d\mid k\\d\ {\rm odd}}}(1+p_dt^d).
\end{aligned}
```
In the second formula the general identity has extra factors $(1-p_{2d}t^{2d})^{-1}$ for $d\mid k$ but $2d\nmid k$. None contributes here: if $2d\le n$, $d\mid k$ and $2\in\pi$, then $2d\mid k$.

Take the half-sum in degree $n$. The left side is the character (in Frobenius notation) of the direct sum indexed by the **even** permutation types. On the right, the first product counts all $\pi$-types; the second counts just those with distinct odd parts. A coefficient of $p_\mu$ in a Frobenius characteristic is the class value divided by the $S_n$-centralizer order. Thus at an even $\pi$-element this module has value half that order, except that it has the full order for distinct odd parts. This is exactly the $A_n$-centralizer: an even-length cycle or a swap of two equal odd cycles is an odd permutation in the centralizer; for distinct odd cycles the centralizer is generated by those cycles and lies in $A_n$. Off the $\pi$-elements the value is zero. Restriction therefore gives $\Pi_{\pi,A_n}$, including its values on both halves of a split class. The extra even-part factors explain why this proof does not cover general $\pi$ omitting two.

## 8. A closure property beyond simple groups

Fix $\pi$, and suppose $\Pi_{\pi,H}$ is a character. Write $s(\alpha)=S_\pi(H,\alpha)$, so $s(\alpha)$ is a nonnegative integer for **any** character $\alpha$ of $H$, including products. Let $\ell$ be prime and $W=H^\ell\rtimes C_\ell$, with the generator rotating the factors. We prove that $\Pi_{\pi,W}$ is a character.

In the base, the local classes are cyclic rotation orbits of $\ell$-tuples from $\mathrm{Cl}_\pi(H)$. In each nonidentity top coset, conjugacy classes are indexed by a single class of $H$: conjugation by the base puts all coordinates but one equal to the identity and leaves the cyclic product, up to conjugacy, in the last coordinate. Rotation makes no further identifications. The $\ell$-th power has this product in every coordinate up to conjugacy. Thus a coset class is included exactly when $\ell\in\pi$ and the product is a $\pi$-element.

By Clifford theory the irreducibles are of two kinds. A nonconstant tuple of irreducible characters $\alpha_1,\ldots,\alpha_\ell$ of $H$ has trivial rotation stabilizer, so its outer tensor product induces irreducibly. The character vanishes off the base. On a free tuple of classes the induced trace counts each rotation once; a constant tuple needs $\ell-1$ additional copies relative to summation over ordered tuples. Its local sum is consequently
```math
 \prod_i s(\alpha_i)+(\ell-1)s\Big(\prod_i\alpha_i\Big)\ \ge 0 .
```
For a constant tuple $\alpha^{\boxtimes\ell}$ the tensor representation extends by cyclically permuting its tensor factors. Twisting this extension by the $\ell$ top characters gives all irreducibles above the tuple. Put $a=s(\alpha)$ and $b=s(\alpha^\ell)$, with $\alpha^\ell$ the **tensor power**, not an Adams operation. In the base, weighted orbit counting gives $(a^\ell+(\ell-1)b)/\ell$: the fixed tuples for a nonidentity rotation are constant. In a nonidentity coset the trace on the tensor power is $\alpha$ of the cycle product, times the top character. Hence the additional contribution, if $\ell\in\pi$, is $(\ell-1)a$ for the untwisted extension and $-a$ for each other one.

It remains to check $a^\ell+(\ell-1)b\ge\ell a$. This holds for $a=0$, and for $a\ge2$ since $2^{\ell-1}\ge\ell$. If $a=1$, then $b\equiv a^\ell\bmod\ell$: expand the $\ell$-th power of the sum of the algebraic integers $\alpha(g_K)$ modulo $\ell$ in the ring of cyclotomic integers, then use that $a,b$ are rational integers. Thus $b\ge1$. This proves the closure assertion; it can be iterated, for example starting with $\mathrm{PSL}_2(q)$. Conversely, for a nontrivial irreducible $\alpha$ of $H$ apply the nonconstant-tuple formula to $(\alpha,1,\ldots,1)$. Without any sign assumption, the resulting sum is $(s(1)^{\ell-1}+\ell-1)s(\alpha)$, with strictly positive prefactor. Thus passage to this wreath product is an equivalence, not a reduction of arbitrary extensions to their composition factors. As a check, the verifier compares these formulas with the row-sum multisets computed directly from the permutation groups $A_5\wr C_2$ and $S_3\wr C_3$.

## 9. Exact character tables: sporadic groups and a counterexample search

On a sporadic simple group $G$, fix $\chi$ and sum its entries in blocks of **equal element order**. Each block sum $b_d$ is an integer since Galois automorphisms permute the classes of order $d$. The minimum over *all* sets of orders containing $1$ is exactly
```math
 \chi(1)+\sum_{d>1}\min(0,b_d).
```
It is attained by including precisely the negative blocks besides $1$. Computing this integer on all 1,396 rows of the 26 ordinary sporadic tables gives a minimum of **one in each group**. In particular every $\Pi_{\pi,G}$ contains every irreducible in these groups.

For a broader finite test, group columns by the product of the distinct primes in the order. The analogous bound certifies a row whenever it is nonnegative. Otherwise sum the blocks dividing each squarefree divisor of $|G|$ in turn; these are all effective prime sets. Using [GAP's Character Table Library](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/), version 1.3.11, the selection in the verifier covers 444 library table names (simple, almost-simple and quasisimple selections, with the sporadics named explicitly), 45,450 rows and 12,142,258 row/prime-set pairs. Seven additional constructed wreath-product tables cover 23,336 more pairs. There is no negative sum in these tests. They cover only the named finite data, not the infinite families containing them.

**Replay.** From this directory run `python3 -I verify.py` for the integer recurrences, the finite proof step of §5 and the independent checks. For §9 run `python3 -I verify.py --tables gap` with GAP and CTblLib installed. The infinite unitary and rank-one results have no dependency on a character-table library.

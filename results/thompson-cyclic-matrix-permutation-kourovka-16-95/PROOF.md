# A rank-one case of Thompson's permutation-cyclicity conjecture

**Result.** Over $\mathbb F_2$, $\mathbb F_3$ and $\mathbb F_4$, in **every dimension**, every invertible rank-one perturbation of a scalar permutation matrix has a cyclic column ordering. There is no restriction on the supports of the two factors of the perturbation. Over **every fixed finite field**, the same rank-one conclusion holds in **all sufficiently large dimensions** with an explicit cutoff. The proof also gives infinite families over infinite fields of positive characteristic.

“Cyclic” means that the minimal and characteristic polynomials agree. It does **not** mean that the column permutation must be a single cycle: our main construction uses two. Thompson's [Kourovka Notebook problem 16.95](https://arxiv.org/abs/1401.0300) asks for the conclusion for *all* invertible matrices; we do not prove that assertion.

## Theorem

Let $F$ have characteristic $p>0$. Suppose $A\in\mathrm{GL}_n(F)$ and $\mathrm{rank}(A-\lambda Q)\le1$ for a permutation matrix $Q$ and $\lambda\in F^\times$. Some permutation matrix $P$ makes $AP$ cyclic in each of these regimes:

1. $n=k+m$ with both $k,m$ powers of $p$, allowing $p^0=1$.
2. $F=\mathbb F_{p^d}$ and $n=k+m$, where $k$ is a power of $p$ (possibly $1$) and $m$ is a positive multiple of $h=p^b$ for some $b\ge1$ with $h\ge d(p-1)$.

In $\mathbb F_2$ and $\mathbb F_4$, take $h=2$: use $k=1$ in odd dimensions at least three and $k=2$ in even dimensions at least four. Part 1 covers dimension two; dimension one is immediate. For $\mathbb F_p$, taking $h=p$ covers all $n\equiv1\pmod p$ and all multiples $n\ge2p$ of $p$.

Scale and multiply on the right by $Q^{-1}$ to reduce to $A=I+uv^\top$. A zero update needs only an $n$-cycle. We may interchange $u,v$: if $A^\top P$ is cyclic, its transpose $P^{-1}A$ is cyclic and is similar to $AP^{-1}$. We test cyclicity over an algebraic closure. Indeed the degree of the minimal polynomial is unchanged by scalar extension (linear independence of powers is a rank condition); by Jordan form, cyclicity is equivalent to eigenspace dimension at most one at every eigenvalue there.

## Making a vector cyclic for one cycle

Call a length $m$ **admissible** over $F$ if every $m$-tuple of nonzero *sum* is a cyclic vector for some $m$-cycle. For a prescribed order, identify the coordinate basis with $1,t,\ldots,t^{m-1}$ in $F[t]/(t^m-1)$. A shift is multiplication by $t$; the vector with coordinate polynomial $f$ is cyclic exactly when $\gcd(f,t^m-1)=1$. Every $p$-power is admissible, since then the only root to avoid is $1$.

For part 2 we partition the tuple into blocks of $h$ elements, all with sum zero except one. With $L=m/h$, put each block at positions $j,j+L,\ldots,j+(h-1)L$ for some $0\le j<L$. Every $m$th root $\zeta$ has $\zeta^L=1$, since $h$ is a $p$-power. Thus $f(\zeta)$ is the nonzero exceptional sum times a power of $\zeta$. This proves admissibility once the partition is obtained.

**For the two binary-characteristic fields in the headline**, this construction just pairs equal entries opposite one another, leaving one unequal pair. In an even-length tuple over either field, the number of elements of odd multiplicity is even. Nonzero sum forces exactly two: in $\mathbb F_4$ the sum of all four elements is zero.

Here is the general block argument, related to the [Erdős–Ginzburg–Ziv theorem](https://www.renyi.hu/~p_erdos/1961-25.pdf). While the remaining length is greater than $h$, choose $2h$ positions with nonzero sum. At length $2h$ take all. At a greater length, if every $2h$-sum vanished, single exchanges would force all entries equal, contradicting the nonzero total in a length divisible by $p$.

For these positions introduce variables $t_i\in\mathbb F_p$ and put $z_i=t_i^{p-1}$. Require that the selected entries (where $z_i=1$) sum to zero, by one equation $\sum_i a_{ij}z_i=0$ for each of the $d$ additive coordinates. Also require $e_{p^s}(z)=0$ for $0\le s<b$, where $e_j$ denotes the elementary symmetric polynomial. On support size $w$, this value is the $s$th base-$p$ digit of $w$ in $\mathbb F_p$: compare coefficients of $X^{p^s}$ in $(1+X)^w=\prod_s(1+X^{p^s})^{w_s}$. Thus $h$ divides $w$. The sum of the degrees of these equations is at most

$$
d(p-1)+(p-1)\sum_{s=0}^{b-1}p^s=d(p-1)+h-1<2h.
$$

The number of solutions is a multiple of $p$: sum the indicator $\prod_j(1-g_j^{p-1})$ of the common zeros of the equations $g_j=0$. Every monomial has some exponent less than $p-1$ and sums to zero over that variable. Besides the zero solution there must be a nonzero one. Its support cannot be all $2h$ positions by choice of their sum, so has size $h$. Remove this zero-sum block and repeat. The final block retains the original nonzero total.

## A two-cycle criterion

Partition the coordinates into $S,B$ of sizes $k,m$, where $k$ is a $p$-power and $m$ is admissible. It suffices that

$$
\sum_{i\in B}u_i\ne0,\qquad
\left(\sum_{i\in S}v_i,\sum_{i\in B}v_i\right)\ne(0,0).
$$

Take any cycle on $S$, and on $B$ an $m$-cycle for which $u|_B$ is cyclic. Call their product $P$. Over the closure, $\ker(P-I)$ consists of vectors constant on each cycle, and the range of $P-I$ consists of vectors summing to zero on each cycle (by inclusion and dimensions). Hence $u$ is outside the range. For any $T$, column $u$ outside its range and row $\ell$, the kernel of $T+u\ell$ is $\ker T\cap\ker\ell$: cancellation with a nonzero multiple of $u$ is impossible. At $T=P-I$ the row $\ell=v^\top P$ is nonzero on the two-dimensional kernel by the second sum condition, cutting the dimension to one.

At $z\ne1$ the short cycle has no eigenvalue $z$. If the long cycle has eigenvalue $z$, its eigenspace is one-dimensional, and $u|_B$ is outside the range of $P|_B-zI$, because that proper invariant subspace cannot contain a cyclic vector. The same kernel intersection bounds the new nullity by one. If neither cycle has eigenvalue $z$, a rank-one update of an invertible matrix has nullity at most one. Thus $AP=P+u(v^\top P)$ is cyclic.

## Finding the partition

First dispose of two exceptional shapes in every characteristic.

* **Disjoint supports.** List the support of $u$ before the support of $v$ and take the forward cycle. Nonfinal column $j$ is $e_{j+1}+v_{j+1}u$. Any nonzero correction lies strictly above position $j+1$. This is upper Hessenberg with subdiagonal ones; the Krylov columns of the first coordinate vector are triangular with diagonal ones.
* **A constant factor.** Transpose if necessary to have $u=c\mathbf1$, $c\ne0$, and $v\ne0$. The invariant line $F\mathbf1$ has eigenvalue $r=1+c\sum v_i$; on its quotient $AP$ acts as $P$. For an $n$-cycle the quotient is cyclic with characteristic polynomial $(t^n-1)/(t-1)$, since a quotient of a cyclic module is cyclic. For a singleton and an $(n-1)$-cycle, the quotient is isomorphic to the long cycle module: subtract the singleton coordinate times $\mathbf1$ to obtain the unique representative zero at the singleton. If $r\ne1$, it cannot be a root of both quotient polynomials, since $r^n=r^{n-1}=1$ would imply $r=1$. Choose the quotient missing $r$. Eigenspaces at other eigenvalues inject into the quotient, while that at $r$ is the line. If $r=1$, fix an index with $v_i\ne0$ and cycle the others. At $1$ the kernel intersection argument applies since $u_i$ and $v_i$ are nonzero. Other eigenspaces inject into the cyclic quotient.

Now suppose both factors are nonconstant and their supports meet. Write $U=\sum u_i$, $V=\sum v_i$. If either is nonzero, interchange the factors if needed so $V\ne0$. Some $m$-subset $B$ has nonzero $u$-sum: otherwise exchanging a single index forces $u$ constant. The $v$-condition is automatic. Thus assume $U=V=0$. If either part is a singleton, take its index in the common support. Both factors sum nontrivially on both parts.

Otherwise both $k,m$ are divisible by $p$. We need a $k$-subset with both sums nonzero. Write $a_i=(u_i,v_i)$. Two points differ in both coordinates: take a pair differing in the first, and if they agree in the second compare them to a point with different second coordinate. In characteristic two, if $\min(k,m)=2$, use a doubly differing pair as the smaller part; totals are zero.

For the remaining cases suppose that every $k$-subset has product of its two sums zero. For any disjoint index pairs $(i,j)$ and $(s,t)$, make four $k$-subsets by taking one index from each pair along with $k-2$ common outside indices. Taking the mixed difference of the four products yields

$$
(u_i-u_j)(v_s-v_t)+(v_i-v_j)(u_s-u_t)=0. \tag{1}
$$

In characteristic two, (1) is a vanishing determinant: disjoint differences are parallel, with zero differences allowed. If three points $a,b,c$ were noncollinear, every further point would lie on the line through $a$ parallel to $b-c$ and the line through $b$ parallel to $a-c$. Their unique intersection is $d=a+b+c$. There are at least two further indices here. The disjoint differences from $a,b$ to the two copies of $d$ are not parallel, a contradiction. Thus the points are collinear. Neither coordinate is constant, so $v_i=\alpha u_i+\beta$ with $\alpha\ne0$. Since $k=0$ in $F$, the two subset sums are proportional, and some $k$-subset has nonzero $u$-sum by a single exchange.

In odd characteristic $k,m\ge3$. Remove one pair differing in both coordinates. By (1) all remaining points lie on a line of nonzero finite slope $c$. Two disjoint unequal pairs among them would give $2c\,\Delta u\,\Delta u'\ne0$ in (1). Hence all but at most one of the remaining points are equal: after choosing an unequal pair the other (at least two) points must be equal, and at least one member of the pair must equal them, or two disjoint unequal pairs would exist. Thus at least $n-3$ points equal a baseline $(a,b)$. Take any outlier and $k-1$ baseline copies; since $k=0$ in $F$, the two sums are its deviations from the baseline. By supposition each outlier deviates in at most one coordinate. Nonconstancy supplies a horizontal and a vertical deviation; take both together with $k-2$ baseline copies. Both sums are nonzero after all.

We have the required partition, which finishes the theorem.

## The remaining ternary dimensions

Over $F=\mathbb F_3$ the rank-one result in fact holds in **every dimension**. The theorem already covers dimensions $0,1\bmod 3$ except $n=3$, which is known over every field by [Chen](https://zenodo.org/records/22186784). Dimension two is immediate: a nonscalar $2\times2$ matrix is cyclic, and a nonzero scalar times a swap is cyclic. It remains to treat $n=2\bmod3$, $n\ge5$.

We may use Chen's Corollary 8.10: it suffices if one factor is constant on the support of the other, even with one exception. The rest of this section treats cases not covered by that result. Again put $U=\sum u_i$, $V=\sum v_i$. We use a 2-cycle on $S=\{i,j\}$ and a cycle on the other $n-2$ coordinates if

$$
U-u_i-u_j\ne0,\qquad v_i\ne v_j,\qquad
V\ne0\ \text{or}\ v_i+v_j\ne0. \tag{2}
$$

In fact the long cycle can make $u|_B$ cyclic by admissibility. The short cycle has eigenvalues $1,-1$. At $1$ the preceding argument applies; at $-1$ the row $v^\top P$ sees the short-cycle eigenvector $e_i-e_j$. If both cycles have eigenvalue $-1$, the column $u$ is also outside the range by its long component, so the intersection argument cuts nullity two to one. If only the short cycle has this eigenvalue, apply the intersection argument to the transpose: a row nonzero on the old kernel is outside the old row space. At every other eigenvalue the previous proof is unchanged.

If either total is nonzero, assume $V\ne0$ by transposing. If (2) fails for every pair, any two indices of different $v$-values satisfy $u_i+u_j=U$. Thus $u$ is constant on each $v$-class. If there are three classes their constants must all be equal. Otherwise, barring constant factors, there are two classes with distinct $u$-values $a,b$ and distinct $v$-values $c,d$. From $U=a+b$ and $n=2\bmod3$, each class has size $1\bmod3$: if the first size is $w$, then $(w-1)(a-b)=0$. Hence $c+d=V\ne0$. Two distinct nonzero ternary elements would sum to zero, so one class has $v=0$; $u$ is constant on the support of $v$, as desired.

Now $U=V=0$. If either factor has zeros, transpose so that $v$ does. Try a pair from the support of $v$ and its complement. Both its $v$-sum and $v$-difference are nonzero. If all such pairs have $u_i+u_j=0$, then $u$ is constant on the support of $v$. Otherwise (2) applies.

It remains that both factors take only the values $+1,-1$. Count the four coordinate pairs $(u_i,v_i)$ in the table

| | $v_i=1$ | $v_i=-1$ |
|---|---:|---:|
| $u_i=1$ | $a$ | $b$ |
| $u_i=-1$ | $c$ | $d$ |

Each row and column sum is $1\bmod3$, since each sign total as a field element vanishes and $n=2\bmod3$. Thus $a\equiv d\equiv r$, $b\equiv c\equiv1-r\pmod3$.

Suppose a pair of opposite cells contains at least three copies of a type $x$ and at least two of $-x$. Put three copies of $x$ and two consecutive copies of $-x$ in a 5-cycle. Each coordinate sum on it is nonzero. For either factor, at a nontrivial fifth root $\zeta$ its coordinate polynomial is a nonzero multiple of a monomial times $1+\zeta$: the constant background has zero Fourier value and the two defects are adjacent. Thus $u$ is cyclic on this cycle, and $v^\top P$ is nonzero on every one of its eigenspaces (evaluate at reciprocal roots for the dual test). The remaining length $n-5$ is a positive multiple of three: it cannot be zero since the full totals vanish. Give it an order making $u|_B$ cyclic, as its sum is nonzero. At any eigenvalue of either cycle, $u$ is outside the range of $P-zI$. If both cycles have the eigenvalue then $v^\top P$ sees the short eigenspace; otherwise the old nullity was already one. The rank-one argument proves cyclicity.

If there are not enough copies, consider the residues of the table. For $r=0$ or $1$ one diagonal consists of multiples of three and the other of counts $1\bmod3$. One entry in the former must be zero and one in the latter must be one, or a suitable opposite pair exists. They are adjacent cells, so some sign occurs just once in $u$ or in $v$. Chen's one-exception case applies. For $r=2$, every count is at least two. Unless all four equal two, one is at least five and its opposite has at least two. Finally, if all are two, fix one $(1,1)$ singleton. On the other seven positions list the three $u=1$ entries followed by the four $u=-1$ entries. This vector has nonzero sum. At any nontrivial seventh root $\zeta$ its polynomial equals $2(1+\zeta+\zeta^2)\ne0$, since a root of order seven does not have order three. Thus the long vector is cyclic, the singleton sees $v$, and the two-cycle criterion applies directly. This completes the proof over $\mathbb F_3$.

## All sufficiently large dimensions over each finite field

Fix **any** finite field $F=\mathbb F_q$, $q=p^d$. The rank-one assertion holds for all $n\ge N(q)$, with the following explicit (very large) sufficient bound. Take $h$ as in part 2 of the theorem, $D=q^2+1$, and set

$$
H=\prod_{j=1}^{D}(q^j-1),\qquad N(q)=q^2(D+hH+h).
$$

The point of this bound is its uniformity in the entries of $A$, not its numerical size. The short cycle will no longer have $p$-power length. Instead, we choose its length so that its nontrivial eigenvalues cannot be roots of any of a bounded number of low-degree coordinate polynomials.

Among the coordinate pairs $(u_i,v_i)$ let $(a,b)$ be a most frequent type. It occurs at least $n/q^2$ times. Write the deviations from this type as $w_i=(u_i-a,v_i-b)$, ignoring zero deviations. If either factor has at most one exception to its baseline, the result also follows directly. Transpose to put such a factor in $u$. Constant factors were handled above. A factor supported at one index is cyclic (or dually cyclic) for any full cycle, so the update cannot produce nullity greater than one. Otherwise write $u=a\mathbf1+c e_j$ with $a,c\ne0$. Unless $v$ is supported at $j$, fix an index $i\ne j$ with $v_i\ne0$ and cycle the rest. At $1$ both singleton entries are nonzero. At each nontrivial root of the long cycle the constant part of its $u$-polynomial vanishes, leaving a nonzero monomial. The kernel intersection argument again gives cyclicity. Otherwise at least two deviations are nonzero in each coordinate.

**Bounded packet.** We can select a packet $E$ of at most $D$ exceptional indices so that each coordinate differs from its baseline somewhere in $E$, and the sum of the deviations *outside* $E$ has both coordinates nonzero. First take two disjoint sets $E_0,T$, each either a singleton nonzero in both coordinates or a horizontal and a vertical nonzero deviation together. To do this, if there are at least two doubly nonzero deviations, take one for each set. If there is just one, take it for one set and use the two pure directions for the other. If there are none, there are two of each pure direction. In particular the sum on $T$ is nonzero in both coordinates. Initially take all exceptional indices outside $T$ for $E$. Keep $E_0$ and shorten $E\setminus E_0$ without changing its sum in the additive group $F^2$: as long as at least $q^2$ terms remain, two of the partial sums (including the empty sum) agree, so a nonempty zero-sum subsequence can be removed. Thus $|E|\le 2+(q^2-1)=D$, and the outside sum still equals the sum on $T$.

Since $h$ and $H$ are coprime, choose $D\le k<D+hH$ by the Chinese remainder theorem with

$$
k\equiv n\pmod h,\qquad k\equiv1\pmod H.
$$

Use the indices in $E$ consecutively at the start of a $k$-cycle, filling all remaining positions with copies of the baseline pair. Enough such copies exist by the bound on $n$. The complementary length $m=n-k$ is a positive multiple of $h$. On it the sums of **both** factors are nonzero: the baseline contributes $m(a,b)=0$ and the outside deviation sums are nonzero. Order this long cycle to make its $u$-vector cyclic by admissibility.

On the $k$-cycle consider any $k$th root $\zeta\ne1$. The constant part in either coordinate polynomial disappears since $\sum_{j<k}\zeta^j=0$. What remains is the value at $\zeta$ of a **nonzero** polynomial of degree at most $D-1$ (each coordinate has a deviation in $E$). It cannot vanish: if it did, $\zeta$ would have degree $e\le D-1$ over $\mathbb F_q$, hence order dividing $q^e-1$, which is coprime to $k$. The argument works at reciprocal roots as well. For clarity, on a single cycle the range of $P-zI$ corresponds to the ideal $(t-z)$ in the cycle module, i.e. to polynomials vanishing at $z$. A right $z$-eigenvector has coordinates proportional to successive powers of $z^{-1}$; thus a row sees this eigenspace exactly when its polynomial is nonzero at $z^{-1}$. These statements do not require diagonalizability.

Consequently at every eigenvalue $z$ of $P$, the column $u$ is outside the range of $P-zI$: use its cyclic long component at long eigenvalues and the short evaluation at short-only eigenvalues. At $1$ the row $v^\top P$ sees the long fixed vector by its sum; at any other shared eigenvalue it sees the short eigenvector by the reciprocal-root test. The kernel intersection therefore has dimension at most one. Away from the spectrum of $P$ rank one again bounds the nullity by one. This proves the uniform large-dimension result.

## Finite checks and scope

The separate exact enumeration in [verify.py](verify.py) also covers **all** invertible binary matrices in dimensions five and six without a rank restriction. In dimension five the minimum number of cyclic column orders is $24=4!$, verifying Chen's proposed sharp counting bound there over $\mathbb F_2$. The dimension-six check is for existence only. An additional unrestricted existence check at dimension seven visits 28,892,664 orbit-cover representatives; the same pure Python enumeration is available with the optional `--seven` flag (long run).

For coverage, encode a column by its binary integer and maximize the ordered sequence of (column weight, column integer) pairs lexicographically over all row and column reorderings. Columns must be sorted decreasingly by this key. Adjacent bit positions equal throughout the earlier columns cannot first differ with the more significant bit zero: swapping those rows would increase the key. The enumeration imposes these necessary tests and independence; unique representatives are unnecessary. Every orbit is visited. Row and column reorderings preserve the number of good orders because $Q^{-1}(QAR)PQ=A(RPQ)$. The exact test is independence of $I,B,\ldots,B^{n-1}$; a cyclic-vector shortcut can prove success, but its failure is not a noncyclicity test.

The checker also constructs and tests rank-one witnesses over small fields and rejects a deliberately noncyclic product. Such checks do not replace the all-dimensional proof. The [Lean file](../../lean/Conjectures/ThompsonCyclicMatrix.lean) formalizes the kernel and nullity steps, not the ordering theorem.

**Prior work.** [Dixon's 2016 preprint](https://arxiv.org/abs/1606.02238v2) was withdrawn; the erroneous criterion is not a counterexample to Thompson. [Haoyu Chen](https://zenodo.org/records/22186784) proved all fields for $n\le3$, many characteristics for $n=4$, the rank-one case for $n=5$ in characteristic zero and small positive characteristics, and sparse or constant-on-support rank-one families in every dimension. His [claims inventory](https://github.com/chy4pro/kourovka-16-95/blob/main/CLAIMS.md) distinguishes finite checks from characteristic-wide results. [Brent Jonah](https://zenodo.org/records/24548659) independently verified the sharp $4\times4$ binary count. We do not settle general rank in arbitrary dimension, Chen's deflated Conjecture J, or the general sharp counting conjecture.

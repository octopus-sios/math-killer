# Jack positivity for near-Pieri hooks and Mickler's three-box window rule

Write $g^\lambda_{\mu\nu}=\langle J_\mu J_\nu,J_\lambda\rangle_a$ for the **integral-form scalar product**, and $c^\lambda_{\mu\nu}$ for the ordinary Schur Littlewood–Richardson multiplicity.

**Theorem.** If $\nu=(2,1^{m-2})$ or $\nu=(m-1,1)$, $m\ge2$, and $c^\lambda_{\mu\nu}\le3$, then $g^\lambda_{\mu\nu}\in\mathbb Z_{\ge0}[a]$. There is no bound on the sizes of $\mu,\lambda$ or on $m$. In particular the coefficientwise positivity conjecture holds without any restriction on the output for multiplication by $J_{21},J_{31}$ or $J_{211}$.

**Window rule.** [Mickler, Conjecture 3.3](https://arxiv.org/html/2401.01582v3#S3.Thmtheorem3) holds: his specified 26-term sum evaluates to the windowed coefficient for **all** four nonnegative spacing parameters and has weight zero. We prove equality of rational functions, not just agreement of residues at a list of poles. We do not assert the later seven-parameter extension.

The finite calculation below is on **indeterminate column heights and gaps**, not a table of Jack coefficients. For example, the theorem includes $\mu=(3^h,2^h,1^h)$, $\lambda=(4^h,3^h,2^h,1^h)$ and $\nu=(2,1^{4h-2})$ for every $h\ge1$; these all have multiplicity three. [Stanley, §8, especially pp. 112–114](https://math.mit.edu/~rstan/pubs/pubfiles/73.pdf#page=37) treated maximal fillings, and discussed $(2,1)$ at multiplicity **one**. The product rules of [Naqvi](https://arxiv.org/abs/1406.3391), [Matveev–Wei](https://arxiv.org/abs/2301.06500) and [Alexandersson–Mickler](https://arxiv.org/abs/2309.13870) likewise do not give the multiplicity-two and -three assertion here. The general positivity conjecture is not settled by this result.

## 1. Two Pieri steps

Use English row indices increasing downwards. For a cell of arm $A$ and leg $l$ write $L=aA+l+1$, $U=a(A+1)+l$, $b=L/U$. Let $H_\rho$ be the product of the lower hooks and denote the product of the upper hooks by the same letter with a prime. The monic Jack basis is $P_\rho=J_\rho/H_\rho$, and the squared norm of $J_\rho$ is $H_\rho H^{\prime}_\rho$. Thus

$$
g^\lambda_{\mu\nu}=H_\mu H^{\prime}_\lambda [P_\lambda](P_\mu J_\nu).
$$

The [vertical Pieri formula](https://arxiv.org/abs/2301.06500) (Macdonald, VI (6.24), specialized at $q=t^a$, $t\to1$) gives $[P_\beta](P_\gamma e_r)=\psi_{\beta/\gamma}$ for a vertical $r$-strip, zero otherwise. Here

$$
\psi_{\beta/\gamma}=\prod_{s\in C\setminus R}\frac{b_\beta(s)}{b_\gamma(s)},
$$

where the product uses old cells in a column but not a row of the added strip. Set $\theta=a-1$ and $\nu=(2,1^{m-2})$. Adding a box to $P_{1^{m-1}}=e_{m-1}$ gives $P_\nu$ with coefficient one, and $e_m$ with coefficient $ma/(a+m-1)$ (telescope the hooks in the column). Since $H_\nu=(m-2)!(a+m-1)$,

$$
J_\nu=(m-2)!\big((\theta+m)e_{m-1}e_1-ma e_m\big). \tag{1}
$$

If $\mu\not\subseteq\lambda$ or the sizes mismatch, Pieri gives zero. If $\lambda/\mu$ is not vertical, the only possible two-step path has one row of size two and $m-2$ singleton rows; all other row-size patterns give zero. In this possible case the **transpose** skew diagram has column lengths $2,1,\ldots,1$. Filling each column by $1,2,\ldots$ from the top gives the unique tableau of maximal weight $\nu'=(m-1,1)$ (the single $2$ must be in the double column). It is semistandard and its reading word is lattice. Stanley's Proposition 8.6 gives the positive hook product for the transpose. Jack duality gives

$$
g^{\lambda'}_{\mu'\nu'}(a)=a^{2|\lambda|}g^\lambda_{\mu\nu}(1/a)
$$

([Bravi–Gandini, Proposition 24](https://arxiv.org/abs/2107.00453)). Thus it suffices to handle vertical strips. The same duality and invariance of Schur multiplicities give the near-row theorem at the end: reversing coefficients preserves nonnegativity (polynomiality follows from the [Knop–Sahi integrality theorem](https://arxiv.org/abs/q-alg/9610016)).

## 2. Strip coordinates and the bulk hooks

Group the new cells of a vertical strip by column, from right to left. Group $i$ has column $c_i$, height $h_i\ge1$, top row $r_i$ and bottom row $b_i=r_i+h_i-1$. In that column $\mu$ has height $r_i-1$ and $\lambda$ has height $b_i$. The row intervals are disjoint and ordered, so $r_{i+1}>b_i$. Put

$$
p_i=ac_i-b_i,\qquad v_i=\theta+h_i,\qquad x_{ij}=p_i-p_j\quad(i<j).
$$

An admissible last box for $e_{m-1}e_1$ is exactly the bottom box of any one group: it is removable in $\lambda$ and the remaining difference is vertical. Thus there are $t$ paths if there are $t$ groups. At $a=1$, (1) in monic form is $s_\nu=e_{m-1}e_1-e_m$ and all Pieri weights are one. Hence $c^\lambda_{\mu\nu}=t-1$.

The normalization of the one-step Pieri coefficient is

$$
B=H_\mu H^{\prime}_\lambda\psi_{\lambda/\mu}.
$$

This is already a product of positive hooks. For each old cell it takes $L_\mu U_\lambda$ except in $C\setminus R$, where it takes $U_\mu L_\lambda$; for each new cell it takes $U_\lambda$. We will remove the following subproduct:

$$
D=\prod_i v_i\prod_{i<j}(x_{ij}-v_j)(x_{ij}+v_i). \tag{2}
$$

In fact $v_i=U_\lambda(r_i,c_i)$. For $i<j$, $x_{ij}-v_j=L_\mu(b_i,c_j)$ and $x_{ij}+v_i=U_\lambda(r_i,c_j)$. Both old cells lie in a changed row, so these hooks really occur in $B$. For $h_i=1$ they use the same location but different shapes; no hook occurrence is used twice. Consequently $B/D\in\mathbb Z_{\ge0}[a]$, **without** a sign inference from polynomial division.

## 3. The only ratios that do not telescope

Let $\kappa$ omit the bottom new box of group $k$ from $\lambda$. Divide $\psi_{\kappa/\mu}\psi_{\lambda/\kappa}$ by $\psi_{\lambda/\mu}$. Outside the changed rows, all changes telescope. Inside them a factor survives only when a column is changed in a different step from the row:

* In group $k$ itself, the $h_k-1$ earlier new cells have arm zero. Increasing their legs by one gives the telescoping factor $ah_k/v_k$ (also one when $h_k=1$).
* For a group $j<k$, the cells of its rows in column $c_k$ change arm first and finish their leg change at the last step. Write $x=p_j-p_k$. For row $b_j-u$, the ratio from the last step is $(x+u+1)(x+u+\theta)/((x+u)(x+u+a))$. Multiplying for $0\le u<h_j$ gives $(x+h_j)(x+\theta)/(x(x+v_j))$.
* For $j>k$ only the old cell $(b_k,c_j)$ contributes. Its leg increases by $h_j$ before its row changes. With $x=p_k-p_j$, its old lower and upper hooks are $x-v_j,x-h_j$; after the leg change they are $x-\theta,x$. Its factor is $(x-h_j)(x-\theta)/(x(x-v_j))$.

All other changed row/column intersections are simultaneous and excluded from both Pieri products. In the field of rational functions, define

$$
T_k=\frac{h_k}{v_k}\prod_{j\ne k}
\frac{(p_j-p_k+h_j)(p_j-p_k+\theta)}
     {(p_j-p_k)(p_j-p_k+v_j)} .
$$

The path ratio is $aT_k$. Substitution in (1) proves the reduction, for **every** $t$:

$$
g^\lambda_{\mu\nu}=a(m-2)!\,(B/D)\,K_t,\qquad
K_t=D\left((\theta+m)\sum_k T_k-m\right). \tag{3}
$$

The reduction even gives integrality of the **kernel** for arbitrary $t$. Treat the positions, heights and $\theta$ as independent. After multiplication by $D$, the only possible poles in (3) are simple differences of positions. At a collision of positions $i,j$, only $T_i,T_j$ can have a pole. Measured in $p_j-p_i$, the first has residue $\theta h_i h_j/(v_i v_j)$ times the product over the other indices; the second has the opposite residue and the same other factors. All poles thus cancel. Algebraically, multiplying by the Vandermonde gives an integer polynomial divisible by each of its distinct monic linear factors, hence by their product. This establishes polynomiality of the reduced expression, but does not establish the signs of its coefficients.

## 4. Exact sign certificate

Put $z_i=h_i-1$ and $w_i=a(c_i-c_{i+1}-1)+(r_{i+1}-b_i-1)$. These are respectively nonnegative integers and polynomials in $a$ with nonnegative integer coefficients. Successive differences satisfy

$$
p_i-p_{i+1}=1+v_{i+1}+w_i .
$$

First treat $a,z_1,\ldots,z_t,w_1,\ldots,w_{t-1}$ as **independent** variables, building all differences by adding these successive gaps. We give the recurrence used by [the verifier](verify.py) so the sign test can be reproduced without a symmetric-functions library. For each $k$ let

$$
\begin{aligned}
d_k &=v_k\prod_{j<k}(x_{jk}+v_j)\prod_{j>k}(x_{kj}-v_j),\\
n_k &=h_k\prod_{j<k}(x_{jk}+h_j)(x_{jk}+\theta)
             \prod_{j>k}(x_{kj}-h_j)(x_{kj}-\theta).
\end{aligned}
$$

Then $D=\prod d_k$ and $T_k=n_k/(d_k\prod_{j\ne k}|p_j-p_k|)$, where each absolute difference denotes $x_{\min(j,k),\max(j,k)}$. Set $E_{ii}=n_i$ and compute

$$
E_{ij}=\frac{d_jE_{i,j-1}+d_iE_{i+1,j}}{x_{ij}},\qquad
K_t=(\theta+m)E_{1t}-mD. \tag{4}
$$

Indeed $E_{ij}$ is the sum over $i\le k\le j$ of $n_k/d_k$ times $\prod_{l=i}^j d_l$, divided termwise by the product of the absolute differences from $p_k$ to the other points of the interval. In the recurrence each interior term recovers its denominator because $x_{ik}+x_{kj}=x_{ij}$; the endpoint terms are immediate.

Exact expansion gives:

| $t$ | nonzero monomials of $K_t$ | sum of coefficients | least nonzero coefficient |
|---:|---:|---:|---:|
| 1 | 0 | 0 | — |
| 2 | 59 | 192 | 1 |
| 3 | 4,006 | 829,440 | 1 |
| 4 | 524,730 | 334,430,208,000 | 1 |

The verifier multiplies sparse integer polynomials by the displayed linear factors, divides by a monic linear form in a gap variable with **zero remainder checked**, and tests the sign of every surviving coefficient. Its five-bit exponent slots are disjoint: $n_i$ has degree at most $2t-1$, and each interval extension adds at most $t-1$ after division, so the largest undivided degree is at most $t^2+1\le17$. For instance, $K_2=h_1h_2(x_{12}+h_1)(x_{12}-h_2)(v_1+v_2)$. Substituting the actual excess heights and gaps in the table and multiplying the hooks in (3) proves the theorem. The calculation makes no sign claim for $t\ge5$.

## 5. Identification of the three-box window

Take $t=3$, $h_1=h_2=h_3=1$. Write $x=p_1-p_2$, $y=p_2-p_3$, $z=x+y$. The six cells of the window in $\lambda$ are the three new corners and the three pair intersections. Outside them the hooks of $B/D$, after division by the outside part of $j_\lambda=H_\lambda H^{\prime}_\lambda$, give precisely Mickler's window factor $F_R$: the lower-hook ratio along a touched row, the upper-hook ratio along a touched column, and one elsewhere. In this singleton case **all** inside hooks from $B$ are in $D$, so (3) gives

$$
\frac{g^\lambda_{\mu,21}}{j_{\lambda,\mathrm{out}} F_R}
    = a K_3\big|_{h_1=h_2=h_3=1}. \tag{5}
$$

Mickler uses the coefficient of $J_\lambda$ in the product, which is $g^\lambda_{\mu,21}/j_\lambda$. Therefore the left side of (5) is exactly the windowed coefficient in his convention after clearing the inside norm $j_{\lambda,R}$.

To evaluate his diagrams, read each printed array top line first, left to right (French diagrams). The lists below give the pair (lower hook, upper hook); let $C=(1,a)$, $M(d)=(d-a,d-1)$ and $N(d)=(d+1,d+a)$:

* $\mu$: $M(y),M(z),M(x)$;
* $\nu$: $C,(a+2,2a+1),C$;
* $\lambda$: $C,N(y),C,N(z),N(x),C$.

These follow from the arm and leg at each intersection; in $\lambda$ both have increased by one. Use the printed choices in the numerator arrays and the **opposite** choices in the last array, since the inside norm clears its denominator. Multiplying the selected hooks and summing with the 26 prescribed integer weights gives exactly the polynomial on the right of (5). This last polynomial identity is checked in two ways: §4's integer verifier specializes the three excess heights to zero and compares every coefficient; [the Lean module](../../lean/Conjectures/StanleyJackNearPieri.lean) proves the corresponding denominator-cleared identity over every commutative ring. The weighted number of lower choices in the first six slots minus that in the last six is zero. This proves both assertions of Conjecture 3.3. No conjectural rule is used to obtain (5).

The four spacing parameters enter only through $x,y$, which were left symbolic. For example at $x=y=a+1$ (the unexpanded window) the integral answer is $6a^4(a+2)(2a+1)(2a^2+11a+2)$. This example alone would not establish the rule at any other spacings. The [subsequent seven-parameter conjecture](https://arxiv.org/abs/2605.10608) also changes the second input shape and is not the assertion proved here.

**Reproduction.** Run `python3 -I verify.py` in this directory. In addition to the universal identities, it compares the reduction with cell-by-cell Pieri on diagrams with idle rows, nonconsecutive columns and repeated heights, and rejects a perturbed polynomial. Lean checks algebraic identities for two columns and for the three-singleton case (including the 26-term rule); the passage from Jack functions to these polynomials is the written argument above.

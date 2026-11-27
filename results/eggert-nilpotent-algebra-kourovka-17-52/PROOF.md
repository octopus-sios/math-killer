# Eggert's dimension bound in characteristic two

**Theorem (characteristic-two case of Kourovka 17.52).** Let $R$ be a finite-dimensional commutative associative nilpotent algebra over a finite field $k$ of characteristic two. Let $R^{(2)}=\{x^2:x\in R\}$. Then

$$
2\dim_k R^{(2)}\leq\dim_k R.
$$

There are no restrictions on the number of generators, the grading, the nilpotency class, or the dimension of the square image. The argument also works over any perfect field of characteristic two. It does **not** prove the conjectured factor $p$ at odd primes.

The idea is to test products against one linear functional with algebraically independent coefficients. Over its rational function field, even a single equation $\lambda(x^2)=0$ detects **vector** vanishing $x^2=0$. A maximal isotropic ideal for the product pairing then bounds the rank of squaring from both sides.

If the algebra or its square image is zero, the inequality is immediate. In the proof below one may therefore suppose both are nonzero.

## The generic square test

Fix a $k$-basis $e_1,\ldots,e_d$ of $R$, put $L=k(t_1,\ldots,t_d)$, and write $V=L\otimes_k R$. Define $\lambda:V\to L$ by $\lambda(e_i)=t_i$, using the same symbols for the extended basis. Put

$$
B=\operatorname{span}_L\{x^2:x\in V\},\qquad r=\dim_L B.
$$

In characteristic two squaring is additive, and $(\sum_i a_i e_i)^2=\sum_i a_i^2 e_i^2$. Thus $B$ is the column space of the matrix of the $e_i^2$ in the given basis. This constant matrix has the same rank over $k$ and $L$. Over $k$, perfectness makes its column space precisely $R^{(2)}$, hence $r=\dim_k R^{(2)}$. Over $L$, we use the **span**; $L$ is not perfect.

For $x\in V$ each coordinate $c_j$ of $x^2$ belongs to the square subfield $L^2$: the structure constants belong to $k=k^2$. The elements $t_1,\ldots,t_d$ are linearly independent over $L^2$. Indeed, in a relation $\sum_j t_j h_j^2=0$ clear a common squared denominator. Every monomial of $t_j$ times a squared polynomial has an odd exponent at $j$ and even exponents everywhere else. The supports for different $j$ cannot cancel. Consequently

$$
\lambda(x^2)=0 \quad\Longrightarrow\quad x^2=0. \tag{1}
$$

This assertion would in general be false for an ordinary functional over $k$.

## An isotropic ideal

Give $V$ the symmetric $L$-bilinear form $H(u,v)=\lambda(uv)$. Write $N=V^\perp$ for its radical. Orthogonals are taken in $V$ with respect to $H$. Associativity and commutativity give $H(au,v)=H(u,av)$, so the orthogonal of any ideal is again an ideal, as is $N$.

Choose a totally $H$-isotropic ideal $I$ of maximum dimension; zero is eligible. Put $J=I^\perp$. Since $I+N$ is another totally isotropic ideal, $N\subseteq I\subseteq J$. We claim

$$
VJ\subseteq I. \tag{2}
$$

The form on $J/I$ is well-defined. Multiplication by any $a\in V$ preserves $I,J$ and acts self-adjointly there. If $V(J/I)\ne0$, nilpotence provides a largest $m\geq1$ with $V^m(J/I)\ne0$, where $V^m$ denotes the span of $m$-fold products. This last image is totally isotropic: in pairing two such products acting on vectors, move all $m$ multipliers from the first factor to the second. The resulting $2m$-fold action is zero since $2m\geq m+1$. The last image is invariant, and its inverse image in $J$ would be a totally isotropic ideal strictly containing $I$. This proves (2).

## The two dimension bounds

* If $x\in I$ then $\lambda(x^2)=0$, hence $x^2=0$ by (1). Extend a basis of $I$ to one of $V$. The squares of only the remaining $d-\dim I$ vectors can contribute to $B$, so $r\leq d-\dim I$.
* If $x\in J$, then for every $a\in V$, $H(a,x^2)=H(ax,x)=0$: by (2), $ax\in I$ and $x\in I^\perp$. Thus $x^2\in N$. Extend a basis of $J$ to one of $V$. Its squares show that $r\leq\dim N+\operatorname{codim}_V J$. The induced form on $V/N$ is nondegenerate, and $J/N$ is the orthogonal of $I/N$ there. Therefore $\operatorname{codim}_V J=\dim I-\dim N$, giving $r\leq\dim I$.

Combining the two bounds proves $2r\leq d$. The use of scalar extension has not changed $d$ or the square-matrix rank $r$. The bound is sharp: in $xk[x]/(x^{2m+1})$, the even powers have dimension $m$ and the algebra has dimension $2m$.

## Sources and scope

The primary statement is [Kourovka Notebook, problem 17.52](https://arxiv.org/abs/1401.0300) (see `SOURCE.tex`). Eggert's [original paper](https://msp.org/pjm/1971/36-3/pjm-v36-n3-p06-p.pdf) asks about successive power images; applying the theorem to each image gives the corresponding inequalities in characteristic two. [Bergman's survey, §6](https://arxiv.org/abs/1206.0326) discusses the general conjecture, the known dimension-at-most-four case, and the failure of a proposed general proof. [Korbelář](https://doi.org/10.1016/j.jalgebra.2010.04.026) establishes the inequality when the power image is at most two-generated, and [McLean](https://doi.org/10.1080/00927870600938415) treats standard graded cases. Neither a grading nor a generator bound enters the proof above.

By [Amberg and Kazarin, Lemma 7.1](https://doi.org/10.1017/CBO9780511721212.005), the fixed-prime reduction mentioned in 17.52 gives a linear sectional-rank bound in Kourovka 11.44 for a finite 2-group that is the product of two abelian subgroups. This is not the general group-theoretic statement with arbitrary factors or arbitrary primes.

The exact checker `verify.py` tests the generic-field argument and finite algebra examples. The universal proof is the dimension argument, not an extrapolation from those tests.

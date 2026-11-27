# The square-root overgroup bound is sharp

**Theorem.** Let $n\ge 4096$, let $G=A_n$, and put $g=(1\,2\,3\,4)(5\,6)$. If a finite group $H$ contains a copy of $G$ in which the image of $g$ is a square in $H$, then
$$
|H|\ \ge\ 2|A_n|^2.
$$
Equality is attainable with *all* elements of $G$ squares. Thus the answer to [Kourovka Notebook 18.46](https://arxiv.org/html/1401.0300v50) is **yes**, for infinitely many groups, even if just one specified root is required.

The previous lower bound of Baranov and Klyachko uses a reflection in a dihedral group of order $2p$ for primes $p\equiv3\pmod 4$; this forces order at least $(2p)^2$. See their [main theorem, Theorem 1 and Question 1](https://arxiv.org/pdf/1101.3019). We use alternating groups instead. The proof uses the classification of finite simple groups (CFSG).

## 1. Reduction to a simple group

For any finite nonabelian simple $G$ and fixed $g\in G$, take a least-order finite overgroup $H$ in which $g$ has a square root, allowing any embedding. Such hosts exist by the wreath construction below. Every nontrivial normal subgroup $K$ of $H$ contains $G$: otherwise $K\cap G$ is a proper normal subgroup of $G$, hence trivial. The smaller quotient $H/K$ then retains both the embedding and the square-root equation.

Take a minimal nontrivial normal subgroup $N$ of $H$. It is a direct product $S^t$ of isomorphic simple groups permuted transitively by $H$; $S$ is nonabelian since $G\le N$. Indeed, take a minimal nontrivial normal subgroup of $N$. Its $H$-conjugates generate $N$ and distinct conjugates commute. If they were abelian, $N$ would be abelian. Each therefore has trivial center, since its center is normal in $N$. So each meets the product of the others trivially. This gives a direct product, in which each factor must itself be simple by minimal normality in $N$.

At least one coordinate projection embeds $G$ into $S$, by simplicity. Since $N$ fixes each factor by conjugation, transitivity implies $[H:N]\ge t$. If $t\ge2$, we get
$$
|H|\ \ge\ t|S|^t\ \ge\ 2|G|^2.
$$
If $t=1$, the normal subgroup $C_H(S)$ meets $S$ trivially, as $S$ is centerless. It cannot contain $G\le S$, so it is trivial. Conjugation identifies $H$ with a subgroup of $\operatorname{Aut}(S)$, with $S$ acting by inner automorphisms. A counterexample to the claimed lower bound would therefore give
$$
G\le S\le H\le\operatorname{Aut}(S),\qquad |S|<2|G|^2.
$$
No normality of the given copy of $G$ is assumed.

## 2. The simple group cannot be of Lie type or sporadic

First, any embedding $A_n\hookrightarrow\operatorname{PGL}_d(k)$ over an algebraically closed field satisfies
$$
d\ \ge\ \lfloor n/5\rfloor+1.
$$
There is a direct product of $b=\lfloor n/5\rfloor$ copies of $A_5$ on disjoint five-letter blocks. Lifts to $\operatorname{GL}_d(k)$ from **distinct** factors commute: for fixed $Y$ lifting an element of one factor and variable $X$ lifting an element of another, $XYX^{-1}Y^{-1}$ is scalar. This scalar is independent of the lift $X$ and is multiplicative in its projective class, so defines a homomorphism $A_5\to k^\times$. It is trivial because $A_5$ is perfect.

Take $r=2$ in characteristic different from two, and $r=3$ in characteristic two. Choose an element of order $r$ from each factor; the images generate $C_r^b$. Rescale the lifts so that their $r$th powers are one. These commuting matrices are simultaneously diagonalizable since $r$ is invertible in $k$. Their projective classes belong to a group of size $r^{d-1}$: normalize the last diagonal entry to one, leaving at most $r$ choices for each other entry. Thus $b\le d-1$. This estimate applies to embeddings over finite fields by scalar extension.

We now apply CFSG and the standard order formulas; see R. Wilson, [*The Finite Simple Groups*](https://doi.org/10.1007/978-1-84800-988-2), Chapters 1, 3–5. Let $G=A_n$ with $n\ge4096$.

**Sporadic groups** cannot contain $G$ by order. Even the Monster has order less than $10^{54}$, while $n!/2\ge2^{n-2}$.

**Exceptional groups of Lie type** have faithful projective representations in defining characteristic of degree at most $248$. The degrees $7,26,27,56,248$ suffice for the untwisted types $G_2,F_4,E_6,E_7,E_8$; degrees $4,7,26,8,27$ suffice for the Suzuki, small Ree, large Ree, triality and twisted $E_6$ families, respectively (also restricting to the Tits derived subgroup). See Howlett, Rylands and Taylor, [*Matrix generators for exceptional groups of Lie type*](https://www.maths.usyd.edu.au/u/bobh/hrt.pdf), and the [matrix construction tables](https://magma.maths.usyd.edu.au/magma/handbook/text/805). But restriction to $G$ gives degree at least $\lfloor4096/5\rfloor+1=820$.

**Classical groups of Lie type:** use the natural projective dimension $d$. For field parameter $q$ of characteristic $p$, the $p$-part of the order of $S$ is $q^a$. In the linear and unitary families $a=d(d-1)/2$; in types $B_l,C_l$ it is $l^2$ with $d=2l+1,2l$, respectively; in the two even-dimensional orthogonal families $d=2l$, $a=l(l-1)$. Here the dimensions are large, so the low-dimensional exceptions do not occur; the central divisors are prime to $p$. In particular, $4a\ge(d-2)^2$. By the projective degree estimate, $d-2\ge n/5-2\ge n/6$, giving $a\ge n^2/144$.

Take $j$ such that $2^j\le n<2^{j+1}$. For $j\ge12$ we have $2^j\ge288(j+1)$: it holds at $12$ and doubling preserves it. Thus $a\ge2n(j+1)$ and
$$
|S|\ \ge\ 2^a\ \ge\ 2^{2n(j+1)}\ >\ (n!)^2\ >\ 2|A_n|^2.
$$

This leaves only $S=A_m$. We have $m\ge n$ from $|S|\ge|A_n|$, and $m<2n$ since $(2n)!>(n!)^2$.

## 3. The remaining action has no root

For $m\ge n\ge4096$, $\operatorname{Aut}(A_m)=S_m$. Consider the embedded $G$ acting on these $m$ letters. On a nontrivial orbit a point stabilizer has index at most $m<2n$. Such a proper subgroup must be a natural point stabilizer by Dixon–Mortimer, [*Permutation Groups*](https://doi.org/10.1007/978-1-4612-0731-3), Theorem 5.2A (take parameter $2$; $2n<\binom n2$ and none of the exceptions apply). Thus each nontrivial orbit is equivariantly isomorphic to the natural $n$-letter action. Since the embedding is faithful and $m<2n$, there is exactly one such orbit; all other points are fixed.

In this representation $g$ still has exactly one two-cycle. If $h^2=g$, then $h$ commutes with $g$ and preserves the two points of least $g$-period two. The square of any permutation of that pair fixes both points, whereas $g$ interchanges them. This rules out the last possible smaller host.

Finally, take $(G\times G)\rtimes\langle\tau\rangle$ with $\tau$ of order two interchanging the factors. The diagonal copy is embedded, and $((x,1)\tau)^2=(x,x)$ for every $x\in G$. Its host has order $2|G|^2$, giving equality.

## Verification scope

The result for arbitrary overgroups is the written proof above, not a finite search. The Lean module proves the unique-two-cycle obstruction and applies it to the explicit witness with an arbitrary type of fixed points. The Python verifier checks the explicit permutation for $n=4096$, the threshold arithmetic, and a corrupted witness which actually is a square. Neither treats CFSG as a machine-verified step.

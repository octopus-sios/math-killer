# The square-root overgroup bound is sharp

**Theorem.** Let $n\ge 4096$, let $G=A_n$, and put $g=(1\,2\,3\,4)(5\,6)$. If a finite group $H$ contains a copy of $G$ in which the image of $g$ is a square in $H$, then
$$
|H|\ \ge\ 2|A_n|^2.
$$
Equality is attainable with *all* elements of $G$ squares. Thus the answer to [Kourovka Notebook 18.46](https://arxiv.org/html/1401.0300v50) is **yes**, for infinitely many groups, even if just one specified root is required.

There is also a small sharp witness for simultaneous roots: the dihedral group of order eight has minimum host order $128$ (Section 4).

The previous lower bound of Baranov and Klyachko uses a reflection in a dihedral group of order $2p$ for primes $p\equiv3\pmod 4$; this forces order at least $(2p)^2$. See their [main theorem, Theorem 1 and Question 1](https://arxiv.org/pdf/1101.3019). We use alternating groups instead. The alternating-group proof uses the classification of finite simple groups (CFSG).

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

## 4. A sharp example of order eight (without CFSG)

For **simultaneous** roots the symmetry group of a square already suffices. Let $D=\langle r,s\mid r^4=s^2=1,\ srs=r^{-1}\rangle$, of order eight. We show that its least host has order $128$. The proof uses the following reductions and an exhaustive integer calculation on tables of order **16**, not a database of small groups.

Suppose $H$ is a least simultaneous host for $D$ and $|H|<128$. A normal subgroup disjoint from $D$ could be factored out, so no such nontrivial subgroup exists. Also $D$ cannot be normal in $H$: its cyclic rotation group is characteristic, and $s$ acts on it by inversion, which is not a square in $\operatorname{Aut}(C_4)\cong C_2$. A square root of $r$ has order eight; this excludes odd index $[H:D]$, since then $D$ would be a Sylow $2$-subgroup and has no element of order eight. The only orders left are $16,32,48,64,80,96,112$.

- For a $2$-group $H$ every square belongs to the Frattini subgroup $K=\Phi(H)$. As $H$ is noncyclic, $H/K$ is elementary abelian of order at least four. If $|K|\le 8$, then $D\le K$ would imply $D=K$, contrary to nonnormality. Otherwise $|H|=64$, $|K|=16$ and $H/K\cong C_2^2$.
- At order $80$ the number of Sylow $5$-subgroups is $1$ or $16$. A normal one is disjoint from $D$. In the second case the $64$ nonidentity elements of order five leave just $16$ elements for a Sylow $2$-subgroup, so it is unique. Whenever the Sylow $2$-subgroup is normal here, it is a smaller simultaneous host: the roots we need are themselves $2$-elements.
- At order $16p$ for $p=3,7$, a nonnormal Sylow $2$-subgroup has $p$ conjugates. The action on them has solvable image by Burnside's two-prime theorem. A solvable transitive group of prime degree $p$ is contained in the affine group of order $p(p-1)$: a minimal nontrivial normal subgroup of the image is elementary abelian and transitive (its orbits form a block system), hence regular, cyclic of order $p$. Its normalizer in $S_p$ is the affine group. The image thus has order $p$ or $2p$, since $\gcd(16,p-1)=2$. In the first case the kernel is a normal Sylow $2$-subgroup. In the second, all squares in the image lie in its subgroup of order $p$, so the $2$-group $D$ maps trivially. It would equal the kernel of order eight.
- At order $96$ the nonnormal Sylow $2$-subgroups form a set of three. The transitive image is $C_3$ or $S_3$. The former again gives a normal Sylow $2$-subgroup. In the latter, all squares project into $A_3$, so $D$ lies in the kernel $K$ of order $16$.

It remains to eliminate two cases: $D\le K\trianglelefteq H$ with $|K|=16$ and quotient $V=C_2^2$ or $S_3$. Here $D$ has index two in $K$. We describe the finite test in full.

**Generating all marked kernels.** For a group $B$ and a coset representative $x$ with $x^2\in B$ normalizing $B$, let $f$ be conjugation by $x$ on $B$, and $a=x^2$. Then $f(a)=a$ and $f^2=\operatorname{Inn}(a)$, with $\operatorname{Inn}(a)(u)=aua^{-1}$. Take $B=D$ and enumerate every such pair $(f,a)$. The table on normal forms $u x^i$, $i=0,1$, is forced: multiply $u x^i$ and $v x^j$ with coefficient $u f^i(v)$, multiplying that coefficient on the right by $a$ if $i=j=1$, and take exponent $i+j\bmod 2$. This includes every possible marked $K$. The verifier labels the elements of $D$ by $r^i s^j$, and the elements of $K$ by $r^i s^j x^k$. It enumerates automorphisms by trying all images of the displayed generators, evaluating these normal forms, and checking bijectivity and compatibility with right multiplication by each generator. That check implies compatibility with every product.

**Testing the quotient cosets.** Now take $B=K$. The same necessary pair $(f,a)$ for a coset $Kx$ of order dividing two in $H/K$ gives its whole set of squares:
$$
U(f,a)=\{u f(u)a:u\in K\}.
$$
Conjugation on $K$ induces a homomorphism $H/K\to\operatorname{Out}(K)$; the class of $Kx$ maps to $[f]$. Write $T=\{u^2:u\in K\}$, a set, not the subgroup generated by squares.

1. For quotient $V$, take the three nonidentity cosets in the order $v,w,vw$. Their data must satisfy $[f_3]=[f_1][f_2]=[f_2][f_1]$. For each compatible triple the test asks if $T\cup U_1\cup U_2\cup U_3$ contains the marked $D$. We allow all triples satisfying this necessary condition; no sufficiency assertion about lifting an outer action is needed.
2. For quotient $S_3$ only its identity and its three transpositions can contribute squares in $K$. If $3$ does not divide $|\operatorname{Aut}(K)|$, an element of order three in the preimage of $A_3$ centralizes $K$. That preimage is then the direct product of $K$ and a cyclic group of order three. Its unique Sylow $3$-subgroup is normal in $H$ and disjoint from $D$, impossible. In all other cases the three transposition cosets are conjugate, so their square sets are carried to one another by automorphisms of $K$. For each pair $(f,a)$ the test asks whether even the larger union of $T$ and all $\alpha(U(f,a))$, for $\alpha\in\operatorname{Aut}(K)$, contains $D$.

Running the adjacent Python verifier produces **16** labelled kernel tables. **None** permits either cover. As a control, replacing $D$ by only its four rotations *does* permit a cover in the $V$ test. This finishes the finite exclusion. The wreath product on $D$ has order $128$, giving equality. Unlike the alternating-group theorem, the dihedral conclusion requires the roots to be present simultaneously.

## Verification scope

The result for arbitrary $A_n$ with $n\ge4096$ is a written proof using CFSG. Lean proves the unique-two-cycle obstruction for the explicit witness with arbitrary fixed points; it does not formalize CFSG. The Python verifier checks the degree-$4096$ instance data and a corrupted square permutation. For the independent $D$ example it exhausts the two finite coset tests in Section 4 from the group law alone, without GAP, floats, or stored catalogues.

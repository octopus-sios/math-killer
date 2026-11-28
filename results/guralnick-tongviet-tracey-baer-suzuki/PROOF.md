# A prime-order commutator criterion for the normal $p$-subgroup

**Theorem A (Conjecture 2).** If $x$ has prime order $p$ in a finite group $G$ and $x\notin O_p(G)$, then some commutator $[x,g]=x^{-1}x^g$ has order greater than one and coprime to $p$.

**Theorem B (cases of Conjecture 1).** Put $f_x(g)=g^{-1}g^x$ and $\Gamma_k(x)=f_x^k(G)$. Let $x$ be a $p$-element. If every product of two members of $\Gamma_k(x)$ is a $p$-element for some $k\ge1$, then $x\in O_p(G)$ in each of the following cases:

- $p=2$, for **every** finite group $G$;
- $G=\mathrm{PSL}_2(q)$ or $\mathrm{PGL}_2(q)$ for a prime power $q\ge4$, for every $p$.

These are the conjectures of [Guralnick, Tong-Viet and Tracey (GTT), JLMS 111 (2025), e70057](https://doi.org/10.1112/jlms.70057); see the [source statements](SOURCE.tex). The second result does not settle Conjecture 1 in general at odd primes. We write $x^g=g^{-1}xg$. The identity counts as a $p$-element.

## 1. What a nonzero pair of character values detects

Two elements $a,b$ *invariably generate* a finite group $H$ if every choice of one conjugate of each generates $H$. In a transitive $H$-set, if $a$ and $b$ each have a fixed point, then some conjugate of $b$ fixes a point fixed by $a$. Thus, if $a,b$ invariably generate $H$, such a set must be a singleton.

**Scalar-action lemma.** Suppose $a,b$ invariably generate $H$ and $\chi$ is an irreducible complex character of $H$ with $\chi(a)\chi(b)\ne0$. In a representation affording $\chi$, every normal $p$-subgroup $P$ for an odd prime $p$ acts by scalars.

First, for any normal subgroup $C$, the isotypic summands of the restricted representation form a transitive $H$-set by irreducibility. An element with nonzero trace fixes some summand (an operator permuting summands without a fixed one has zero diagonal blocks). Hence there is just one summand. In particular an abelian normal subgroup acts by scalars.

We next show the same for a normal odd $p$-subgroup $C$ of nilpotency class at most two. Let $\rho$ be its single irreducible constituent, on a space $V$. We give the orbit-basis argument explicitly; this basis is the class-two finite [orbit method of Mihailovs](https://arxiv.org/abs/math/0001092). Write $D=C'$. This central subgroup acts under $\rho$ by a linear character $\eta$. Set

$$
R=\{u\in C:\eta([u,c])=1\text{ for all }c\in C\}.
$$

This is the subgroup acting by scalars under $\rho$, by Schur's lemma. Write $\rho(r)=\tau(r)I$ on $R$. On the set $C$ put the abelian group law $u+v=uv[u,v]^{-1/2}$, using the unique square root in $D$. Centrality and bimultiplicativity of the commutator give commutativity and associativity (in either bracketing the correction to $uvw$ is the product of the three pair corrections). Every automorphism of $C$ preserves this law. The subgroup $R$ contains $D$, and $\tau$ is also an additive character of $R$: the commutator correction for two of its elements is in $\ker\eta$.

Consider the set $\Omega$ of additive characters $\lambda$ of $C$ extending $\tau$. It is nonempty by character extension for finite abelian groups; it is a torsor for the character group of $C/R$. It is $H$-invariant because $\rho$ is invariant up to equivalence. Conjugation by $c\in C$ translates an extension by the character $u\mapsto\eta([u,c])$ or its inverse, according to action convention. These characters exhaust the dual of $C/R$: the alternating pairing induces an injection of $C/R$ into its dual, and the orders agree. Thus $\Omega$ is transitive even under $C$.

Here is why a nonzero trace forces a fixed point on **this** set. In $\operatorname{End}(V)$ form

$$
B_\lambda=\sum_{uR\in C/R}\lambda(u)^{-1}\rho(u).
$$

The summand is independent of the representative: multiplication by $r\in R$ introduces the same factor $\tau(r)$ in numerator and denominator, since $\eta([u,r])=1$. The matrices $\rho(u)$ for coset representatives form a basis. Indeed, the character of $\rho$ is zero off $R$ (conjugate $\rho(u)$ to a nontrivial scalar times itself), and on $R$ has absolute value $\dim V$. Character orthogonality gives $(\dim V)^2=|C:R|$, and the representative matrices are pairwise orthogonal in the trace inner product in a unitary realization. Fourier inversion on $C/R$, using any one extension as origin, now gives the basis $\{B_\lambda:\lambda\in\Omega\}$.

For $h\in H$, choose a unitary intertwiner $T_h$ implementing its conjugation action on $\rho$. Conjugation by $T_h$ **permutes** the basis above, without scalar factors, by the action on $\Omega$. Its trace on $\operatorname{End}(V)$ is both the number of fixed points and $|\operatorname{tr}(T_h)|^2$. On the full representation space $V\otimes M$ (with multiplicity space $M$), the operator for $h$ has the form $T_h\otimes S_h$: after removing $T_h$ on the first factor it commutes with $C$. Therefore $\chi(h)\ne0$ implies $\operatorname{tr}(T_h)\ne0$. Applying this to $a,b$ forces $\Omega$ to be a singleton, hence $R=C$. This proves scalar action for $C$.

Finally pass to the image of the representation, where the representation is faithful, the two traces are unchanged and the two elements still invariably generate. Denote the image of $P$ by $U$. Its second center $Z_2(U)$, the inverse image of $Z(U/Z(U))$, is normal in the image group and has class at most two. By the preceding argument it consists of scalars and so lies in $Z(U)$. If $U$ were nonabelian, the nontrivial $p$-group $U/Z(U)$ would have nontrivial center, a contradiction. Thus $U$ is abelian and acts by scalars, as claimed.

## 2. Lifting a class product, not an arbitrary commutator

**Lifting lemma.** Let $P\unlhd H$ be a $p$-group for $p$ odd. Use bars for images in $L=H/P$, and suppose a Sylow $p$-subgroup of $L$ is cyclic. Let $x,y\in H$ with $y$ of order prime to $p$. If $\bar x,\bar y$ invariably generate $L$ and $\bar y\in(\bar x^{-1})^L\bar x^L$, then $y\in(x^{-1})^H x^H$.

Take a counterexample of least order. Then $x,y$ invariably generate $H$ itself. Indeed, any proper subgroup containing a conjugate of each maps onto $L$, with kernel its intersection with $P$. The same hypotheses hold there for the two conjugates, so minimality puts the conjugate of $y$ in the required product, which suffices in $H$.

Put $N=[P,H]$. For a fixed target $y$, the number of representations in the prescribed product of classes is, by the class multiplication formula,

$$
\frac{|x^H|^2}{|H|}\sum_{\chi\in\operatorname{Irr}(H)}
          \frac{|\chi(x)|^2\,\overline{\chi(y)}}{\chi(1)}.
$$

By the scalar-action lemma every nonzero summand comes from a representation trivial on $N$. Thus the **sum** equals the corresponding sum in $H/N$. If $N\ne1$, the quotient, with kernel $P/N$ over the same $L$, satisfies the lifting lemma by minimality. Its count is positive. The prefactors in both groups are positive, so the count upstairs is positive too.

It remains that $P$ is central. A Sylow $p$-subgroup $J$ of $H$ is abelian since $J/P$ is cyclic. Transfer $H\to J/[J,J]=J$ takes $z\in P$ to $z^{[H:J]}$: each coset representative contributes $z$, by centrality. This is injective on $P$, so $P\cap H'=1$. Lift a product for $\bar y$ to $w\in (x^{-1})^H x^H$. We have $w\in H'$ and $w^{o(\bar y)}\in P\cap H'=1$. Thus $w$ and $y$ are both of order prime to $p$ in the same coset of the central $p$-group $P$. They commute and their quotient is both a $p$-element and of order prime to $p$. Hence $w=y$, proving the lemma.

## 3. Application to prime-order elements

Assume Theorem A fails, with $|G|$ least. Use the minimal-counterexample reduction of GTT, Corollary 6.5. Here $p$ is odd, $P=O_p(G)$ does not contain $x$, and in $L=G/P$ the subgroup generated by $s=xP$ is cyclic of order $p$ and weakly subnormal: it is subnormal in every proper overgroup but not in $L$. Indeed the corresponding property holds upstairs, and $O_p(L)=1$. In the soluble case $L=Q\rtimes\langle s\rangle$ as in GTT, Theorem 1; otherwise $L$ is quasisimple with cyclic Sylow $p$-subgroups by GTT, Theorem 3 (the two odd-prime outer cases there require order $p^2$, not $p$). In the soluble case the Sylow $p$-subgroup is cyclic too.

We specify the quotient input used here: there is a nonidentity $p'$-element $v\in(s^{-1})^L s^L$ such that **$s,v$ invariably generate $L$**. In the soluble case choose $v=[s,h]$ with $h\in Q$ and nonzero commutator image in $Q/\Phi(Q)$; this is possible by the nontrivial irreducible action. All conjugates of $v$ still have nonzero image there. The orbit of any such image under $s$ spans, so $\langle s,v^b\rangle$ contains $Q$ by the Frattini property, for every $b\in L$.

In the nonsoluble case this is the quotient-class selection in the **proof** of GTT, Theorem 6.2, from the paragraph introducing invariable generation through cases (1)–(4), before the argument on the abelian kernel. That selection uses the weakly subnormal cyclic-Sylow pair in the quotient: the unique maximal subgroup containing $s$ is its cyclic subgroup's normalizer. In the simple quotient the authors select a commutator class of $p'$-elements avoiding every conjugate of this maximal subgroup (the sporadic table cases; a 3-cycle in the alternating case; a nonsplit torus element in defining characteristic in rank one; and the regular semisimple class product in the remaining Lie cases). This is exactly the stated invariable generation test. To pass from the simple group to its quasisimple cover $L$, note that $Z(L)$ has order prime to $p$ since $O_p(L)=1$. The image of $\langle s\rangle$ in the simple group is still weakly subnormal by passage to preimages of proper overgroups. A commutator lifting the selected commutator is still of order prime to $p$. A subgroup $H_0$ mapping onto $L/Z(L)$ is all of $L$, since $L=L'=(H_0Z(L))'\le H_0$. Hence the selection lifts. Only the quotient-level selection, not a lift through $P$, is taken from GTT.

Take any lift of $v$ to $G$ and retain its $p'$-part $y$; this still maps to $v$. The lifting lemma puts $y$ in $(x^{-1})^G x^G$. Conjugating a representation $y=(x^a)^{-1}x^b$ by $a^{-1}$ gives the commutator $[x,ba^{-1}]$, of the same nontrivial $p'$-order. This contradicts the counterexample and proves Theorem A. An almost-simple result alone, such as [Tong-Viet's almost-simple theorem](https://arxiv.org/abs/2507.10882v4), would not justify this lifting step.

## 4. Products of iterated commutators in rank one

For Theorem B let $S$ denote the eventual image of $f_x$ on $G$. These images decrease and stabilize since $G$ is finite. We have $1\in S=f_x(S)$ and $S^x=S$. Under the hypothesis, $S^2=\{ab:a,b\in S\}$ consists of $p$-elements; this includes $S$ itself. If $\langle S\rangle$ is a $p$-group, then $\langle S,x\rangle$ is a $p$-group and iterating $f_x$ on it eventually gives only the identity, by nilpotence. Thus $S=\{1\}$. By Baer's theorem on left Engel elements of finite groups, $x$ lies in the Fitting subgroup, hence in $O_p(G)$. We will use this criterion also when $S$ lies in a product of $p$-groups.

**Nonsplit torus test.** Let $D$ be a full nonsplit torus in $\mathrm{PGL}_2(q)$, and $A\subseteq\mathrm{PSL}_2(q)$ a $D$-conjugation-invariant subset containing $1$. Suppose $A^2$ consists of $p$-elements, where either $p$ is odd and divides $q+1$, or $p=2$ and $q\equiv3\pmod4$. Then $A$ preserves the unordered pair of eigenlines of $D$.

Indeed the eigenlines are interchanged by Frobenius over $\mathbb F_q$. On them the eigenvalue ratios of $D$ run through $U=\{s:s^{q+1}=1\}$ in $\mathbb F_{q^2}^\times$: multiplication by $u\in\mathbb F_{q^2}^\times$ on the plane has ratio $u/u^q$ and scalar kernel $\mathbb F_q^\times$. Every determinant-one lift of a member of $A^2$ is semisimple with both eigenvalues in $U$. To see this, its order divides twice a power of $p$ (just a power of $p$ in even characteristic), prime to the characteristic. Nonsplit eigenvalues are inverse Frobenius conjugates. In the split case an eigenvalue in $\mathbb F_q^\times$ has order dividing $\gcd(q-1,2p^j)$ for some $j$, hence is $\pm1$ if $p$ is odd and divides $q+1$. For $p=2$ the same conclusion follows because $q-1$ is twice an odd number.

Lift a member of $A$ to a determinant-one matrix, written in the eigenbasis as

$$
M=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
$$

If $bc=0$, it fixes one eigenline and hence both, since it is defined over $\mathbb F_q$. Otherwise, for torus conjugates $M^t$ the product traces range over

$$
a^2+d^2+bc\, B,\qquad B=\{s+s^{-1}:s\in U\}.
$$

This follows by diagonal conjugation, which scales the two off-diagonal entries by reciprocal ratios. All these traces lie in $B$, by the eigenvalue restriction. Since $bc\ne0$, the displayed set has exactly $|B|$ elements and so equals $B$. In odd characteristic both $2$ and $-2$ occur. The corresponding semisimple products are $I$ and $-I$. Thus there are conjugates equal to $M^{-1}$ and $-M^{-1}$; their diagonal entries are unchanged from $M$. Comparing with $(d,a)$ and $(-d,-a)$ gives $a=d=0$. This matrix swaps the lines. In even characteristic trace $0$ occurs, and semisimplicity gives product $I$. Comparing diagonals with $M^{-1}$ gives $a=d$, so $M$ itself has trace zero. As $M$ lifts a $p$-element of odd order in even characteristic, it is semisimple, and must be $I$. This contradicts $bc\ne0$. The test follows.

First take $G=\mathrm{PSL}_2(q)$ or $\mathrm{PGL}_2(q)$. The stable image is contained in $\mathrm{PSL}_2(q)$ since the projective determinant quotient is abelian. Every automorphism induced by $\mathrm{PGL}_2(q)$ centralizing $x$ preserves $S$. The case $x=1$ needs no argument. A nonidentity split semisimple $x$ acts on the upper unipotent root group by a multiplier different from one; $f_x$ maps that group bijectively onto itself, supplying elements of defining characteristic in every image, contrary to the product condition in cross characteristic. For a nonsplit $x$ in the cases of the torus test, we have $S\subseteq N$, the line-pair stabilizer. Its subgroup fixing both lines is $D$ and has index at most two. Since $x\in D$, we have $f_x(N)\subseteq D$ and $f_x(D)=\{1\}$, so $S=\{1\}$.

If $p$ is odd and is the defining characteristic, take the eigenline of the unipotent $x$ as the first coordinate line. Its centralizer contains all $u(t)=I+tE_{12}$. For a lift $M$ as above of an element of $S$,

$$
\operatorname{tr}(M u(t)^{-1} M u(t))=\operatorname{tr}(M^2)-c^2t^2 .
$$

These traces must all belong to $\{2,-2\}$ since the products are projectively unipotent or the identity. For $c\ne0$ there are $(q+1)/2>2$ traces, since $q\ge5$ here. Thus all $M$ are upper triangular. Applying $f_x$ sends the triangular subgroup into the upper unipotent group, which centralizes $x$. Again $S=\{1\}$. This proves the rank-one assertion for odd $p$, and handles in particular the single-component $p=2$, $q\equiv-1\pmod8$ case of GTT, Proposition 6.6(ii): an element of order at least eight there is nonsplit since $q-1$ is twice an odd number.

## 5. The prime two for arbitrary finite groups

Fix $p=2$ and take a counterexample of least order. By GTT, Proposition 6.6, only its cases (ii) and (iii) are possible. Case (ii) was just excluded. In (iii), $G=E\langle x\rangle$ with $E=T_1\times\cdots\times T_t$ minimal normal, $t>1$ and $x$ cycling its simple factors. In particular $f_x(G)\subseteq E$. The stable image computed on $E$ is exactly $S$, by the inclusions $f_x^j(E)\subseteq f_x^j(G)\subseteq f_x^{j-1}(E)$ for $j\ge1$.

Put $T=T_1$, let $\alpha$ be the automorphism induced on $T$ by $x^t$, and let $A$ be the first projection of $S$. Then $1\in A$, all products in $A^2$ are $2$-elements (lift the two factors independently to $S$), and $A$ is invariant under **every** automorphism $\beta$ of $T$ commuting with $\alpha$. Indeed, transport $\beta$ by $x^i$ to the factor $T^{x^i}$ for $0\le i<t$. The product automorphism commutes with $x$ on $E$, with consistency at the last factor exactly because $\beta\alpha=\alpha\beta$. It commutes with $f_x$ there and therefore preserves the stable image. All other projections of $S$ are transports of $A$, since $S^x=S$. In particular, if $\langle A\rangle$ is a $2$-group, so is $\langle S\rangle$.

There is a second exclusion: if $\alpha$ normalizes any nontrivial abelian odd-order subgroup $B_0$ of $T$, the product $B$ of its $t$ transports is an abelian odd-order group normalized, but not centralized, by $x$ (the factors move). On $B$ the map $f_x$ is the endomorphism $x-1$ in additive notation. Its image is nonzero and $x-1$ acts bijectively on that image: averaging the powers of $x$ splits $B$ into the fixed subgroup and the image, since multiplication by $o(x)$ is invertible. So $S$ contains a nonidentity odd-order element, impossible.

The induced group $N_G(T)/C_G(T)$ is generated by the inner group $T$ and $\alpha$. In the projective linear cases of Proposition 6.6(iii), $T=\mathrm{PSL}_2(q)$ for a Mersenne prime $q\ge7$ and $\alpha\in\mathrm{PGL}_2(q)$ is a $2$-element. If $\alpha$ is split or trivial it normalizes an odd unipotent root group, giving the second exclusion. Otherwise its nonsplit torus $D$ centralizes it, and the torus test puts $A$ in the line-pair stabilizer of order dividing $2(q+1)$. This is a power of two, giving the first exclusion.

In the exceptional $\mathrm M_{10}$ case $T\cong A_6$. The following finite lemma does not require picking a model for the outer automorphism. For **every** automorphism $\alpha$ of $A_6$ of $2$-power order, either it normalizes a nontrivial abelian odd-order subgroup, or the set

$$
D_\alpha=\{v\in A_6:v\text{ and every }v\alpha^i(v)\text{ have }2\text{-power order}\}
$$

generates a group of order eight. Since $A$ is $\alpha$-invariant and $A^2$ consists of $2$-elements, $A\subseteq D_\alpha$. The lemma therefore gives one of the same two exclusions for **every** $t$, not just for a bounded number of components. This finishes Theorem B.

**Finite lemma verification.** The [exact enumerator](verify.py) forms the Cayley table of the even permutations on six letters. It chooses a generating pair of orders $2,4$ with product of order $5$. Any automorphism takes it to a pair with these same orders. For each such pair the code propagates images along a spanning tree of right generator edges and checks bijectivity and *every* generator edge. This gives exactly the automorphisms: the edge identities give a homomorphism by induction on words. For each automorphism of $2$-power order it first tests for a nonidentity odd-order element whose orbit commutes pairwise; this is equivalent to the first alternative. Otherwise it forms $D_\alpha$ by multiplication and closes it under generation. The counts are:

| Automorphism order | Normalizes an abelian odd subgroup as above | Other, with generated group of order eight |
|---:|---:|---:|
| 1 | 1 | 0 |
| 2 | 111 | 0 |
| 4 | 360 | 0 |
| 8 | 180 | 180 |

Run **python3 verify.py** in this directory. Besides certifying the finite lemma, it contrasts pure and mixed-order commutator lifts with the very same quotient element in a group of order 648 with extraspecial $3$-core. This illustrates the obstruction addressed by Theorem A; the proof of that theorem is not an extrapolation from the example.

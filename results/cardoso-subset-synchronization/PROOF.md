# Cardoso's subset bound for weakly oriented circular automata

**Theorem.** Let a complete synchronizing automaton on $n$ states have a letter acting as an $n$-cycle. Suppose there is a cyclic order on the states in which the inverse image of each interval under each letter is an interval (the empty and full sets are allowed). Then every specified nonempty $m$-subset $S$ can be synchronized in at most

$$
B(n,m)=(n-1)^2-\left(\left\lceil n/m\right\rceil-1\right)
             \left(2n-m\left\lceil n/m\right\rceil-1\right)
$$

letters. This is sharp for every $n,m$ within this class, since it contains the Černý automata.

**Scope and prior work.** These are the *weakly oriented circular* automata. [Cardoso's thesis](https://repositorio-aberto.up.pt/bitstream/10216/73496/2/32442.pdf), Conjecture 5.1.1, asks for the same bound without structural assumptions. Its Theorems 5.2.2–3 give sharpness in the Černý series; Theorem 5.7.8 proves the upper bound in our class when the circular letter has jump $\pm1$ in the preserved order **or** some letter has rank $n-1$. Theorem 5.7.9 gives a weaker bound for the rest of the class. We remove both qualifications. We do **not** prove the conjecture for all circular automata, all weakly oriented automata, or all synchronizing automata.

## The interval growth budget

Identify the cyclic order with $\mathbb Z/n\mathbb Z$. Write $I(i,l)$ for the $l$ consecutive states starting at $i$. The circular letter $a$ is a rotation by a unit: its inverse takes adjacent pairs to adjacent pairs, hence it is a symmetry of the cycle, and a reflection cannot be an $n$-cycle for $n>2$. No bound on its jump is needed. The word length is measured in letters, not in displacements around the circle.

It suffices to treat $n=5$ and $n\ge7$: one state is trivial, and for $n=2,3,4,6$ every unit jump is $\pm1$, a case of Cardoso's Theorem 5.7.8. Singletons need no letters. For a pair, a shortest path to a singleton visits each unordered pair at most once, giving $\binom n2=B(n,2)$. For $m\ge3$, by Cardoso's Theorem 5.7.8 we need only the case with no rank-$(n-1)$ letter. At least one letter is singular, since the automaton synchronizes. Fix a letter $b$ of rank at most $n-2$. In fact the proof below works whenever **any** such letter exists.

Set
$$
\gamma=\left\lfloor\frac{n-1}{m}\right\rfloor,\qquad
\varepsilon=n-m\gamma,\qquad L=n-\gamma,\qquad d=L-2 .
$$
Thus $1\le\varepsilon\le m$. The $d$ growth stages have lengths $l=2,\ldots,L-1$. For each $l$ choose a letter $b_l$ as follows. Use $b$ if at least one $l$-interval has a strictly larger inverse image under $b$; otherwise use any letter for which this happens. Such a letter exists: for each letter the inverse sizes of the $n$ intervals sum to $nl$, because each output belongs to $l$ intervals. If none grew under any letter, all these inverse images would themselves be $l$-intervals. Iteration would preserve that size even under a reset word, which is impossible for $0<l<n$. Let $e_l$ be the number of growing intervals for the chosen letter; $1\le e_l<n$ by the same sum.

Suppose one $l$-interval can be synchronized in $u$ letters. Prepending $a$ moves it backwards around a cycle of all $n$ positions. In at most $n-e_l$ rotations we encounter a growing interval; prepend $b_l$ and take an $(l+1)$-subinterval of its inverse image. This produces an $(l+1)$-interval synchronizable in at most $u+n+1-e_l$ letters. Taking a subinterval is legitimate: a word constant on a set is constant on every subset.

There are **two distinct starting intervals** of size two, each synchronized by $b$. Indeed each proper nonempty fibre of size $s$ gives $s-1$ adjacent pairs, and their total is $n-\operatorname{rank}(b)\ge2$. A constant letter makes the result immediate. At the first stage we may choose either start, so at most $n-e_2-1$ rotations are needed: equality in the single-start bound $n-e_2>0$ requires one consecutive run of *all* the nongrowing positions and starting at its first position. At most one start can do that.

Consequently an interval of size $L$ is synchronized by a word of length at most
$$
1+\sum_{l=2}^{L-1}(n+1-e_l)-1.
$$
Its complement has $\gamma$ states. Among the $n$ rotations of $S$, at most $m\gamma$ meet that complement: each pair consisting of one state of $S$ and one complement state forbids exactly one exponent. As $m\gamma<n$, an exponent at most $m\gamma$ suffices. The resulting bound for the **given** set $S$ is
$$
\operatorname{rt}(S)\le d(n+1)-\sum_{l=2}^{L-1}e_l+m\gamma. \tag{1}
$$

## Counting growing positions across all lengths

Write $c_i$ for the size of the $b$-fibre over $i$. Since $\sum_i(c_i-1)=0$, there is a periodic integer function $F$ with $F(i+1)-F(i)=c_i-1$. An $l$-interval starting at $i$ has inverse size $l+F(i+l)-F(i)$. Thus $e_l$ is at least the number of strict rises $F(i+l)>F(i)$, even when we switched away from $b$.

We claim that
$$
\sum_{l=2}^{L-1}e_l\ge 2d-2. \tag{2}
$$

First suppose some upper level set of $F$ has size between $2$ and $n-2$. Take $D$ to be its smaller side (the upper set or its complement), $k=|D|$, so $2\le k\le\lfloor n/2\rfloor$. Under translation by $l$, the numbers crossing a cut in the two directions are equal. Every crossing *into* the upper set is a strict rise. Hence
$$
e_l\ge k-o_l,\qquad o_l=|\{i\in D:i+l\in D\}|.
$$
Over all nonzero shifts, $\sum_{l=1}^{n-1}o_l=k(k-1)$: each ordered pair of distinct elements contributes to exactly one shift. Therefore the stage sum is at least $kd-k(k-1)$. If $k=2$ or $d\ge k+1$ this is at least $2d-2$, since the difference is $(k-2)(d-k-1)$.

Here $d\ge\lfloor n/2\rfloor$: use $\gamma\le(n-1)/3$ for $n\ge10$, and substitute $n=5,7,8,9$ directly. It remains to check $d=k\ge3$, which implies $n\ge7$. In that case $\gamma=n-k-2\ge2$. Consider the $k$ clockwise distances between consecutive points of $D$. Their sum is $n$, so the sum of their excesses over one is $n-k=\gamma+2$. At most two distances exceed $\gamma$, since three such distances would have excess at least $3\gamma>\gamma+2$. Thus at least $k-2$ ordered pairs give **backward** shifts in $\{n-\gamma,\ldots,n-1\}$, outside the stages. Removing these from the overlap budget raises the lower bound to $k^2-k(k-1)+(k-2)=2k-2$, as needed.

Finally, suppose no upper level set has size between $2$ and $n-2$. The nonempty proper upper cuts have distinct sizes drawn from $\{1,n-1\}$ (take one cut per distinct value above the minimum). With only two heights, one height would occur at a unique state, so $F$ would have exactly one descending step around the circle. A constant $F$ would have none. Both possibilities are excluded: every output missing from $b$ gives a descending step, and there are at least two. There are therefore three heights, with a unique minimum $u$, a unique maximum $v$, and all other values intermediate. For any nonzero $l$ there is a rise starting at $u$ and one ending at $v$. They are distinct except at $l=v-u$. This gives at least $2d-1$ rises in total and completes (2).

## Closing the ceiling arithmetic

By (1) and (2),
$$
\operatorname{rt}(S)\le 2+(n-1)d+m\gamma .
$$
Since $\lceil n/m\rceil=\gamma+1$, direct subtraction gives
$$
B(n,m)-\bigl(2+(n-1)d+m\gamma\bigr)
=\gamma(m-\varepsilon)+\varepsilon-3.
$$
For $\gamma\ge1$ the right side is at least $m-3\ge0$. For $\gamma=0$ we have $m=n=\varepsilon$ and obtain the same inequality. This proves the theorem. In the rank-at-most-$n-2$ branch just proved, the argument even saves at least $m-3$ letters from Cardoso's bound.

The improvement comes from counting the placements at which a letter can extend an interval **in aggregate** over the different lengths. The plain per-stage bound of $n$ letters, with no credit for multiple placements, does not suffice. The proof uses the interval and rotation hypotheses at the growth stages; a general automaton need not let us reuse a level cut in this way.

**A family outside the earlier hypotheses.** For odd $n\ge 9$ coprime to three, take $a:i\mapsto i+3$ and let $b$ send $0$ to $1$ and $5$ to $6$, fixing every other state. Its fibres occur in cyclic order, so inverse intervals are intervals. Here $F$ is $-1$ on $\{1,6\}$ and zero elsewhere. A two-point set on an odd cycle is not fixed by any nonzero translation, so there is a growing $b$-placement at every proper length. Starting from a double fibre, successive extensions synchronize the whole set. No letter has rank $n-1$. In an order in which the only cyclic letter $a$ has jump $\pm1$, the points $0$ and $1$ are not adjacent. Hence the fibre $b^{-1}(1)=\{0,1\}$ is not an interval in that order.

**Verification scope.** The Lean module proves the ordered-pair overlap budget, its aggregate consequence for any finite abelian group with two same-shift descents when the stage set has more than half the group, the finite-orbit steering lemma with multiple starts, and the closing integer inequality. It does not formalize the complete automaton theorem. The companion Python script checks the growth inequality on all corank-at-least-two indegree profiles through rotation at $n=8,9,10$, constructs actual synchronizing words for every subset of size at least three in six example automata, compares with exact subset BFS, and rejects a shortened witness. These tests are checks on the argument, not the reason it holds for unbounded $n$.

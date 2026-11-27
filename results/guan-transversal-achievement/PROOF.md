# Optimal winning ply in the transversal achievement game

**Theorem.** On the $n\times n$ board, for every $n\ge 4$, the earliest ply by which X can force a win is $2n+3$.

Kevin Guan proved the upper bound and conjectured its sharpness in [*The transversal achievement game on a square grid*, arXiv:2608.13501v1](https://arxiv.org/abs/2608.13501v1) (see [the source statement](SOURCE.tex)). We prove the lower bound: O can prevent an X win through X's $(n+1)$-st move. The key is to use **O's own transversal** as a threat, not merely to occupy cells X needs.

### Build a matching for O

Call a row or column *unused by O* if it contains no O stone. For the first $n-2$ replies, O maintains a matching and keeps the rectangle of unused rows and unused columns free of X stones immediately after each reply. Initially the rectangle is the whole empty board.

After X plays, O chooses an unused row: the row X just played in if it is unused, and any unused row otherwise. In that row O plays in an unused column different from the column X just played in. There are at least three unused columns before each of these replies. The cell was in the empty rectangle before X played and is not X's latest cell, so this is legal and extends O's matching. All earlier X stones remain outside the smaller rectangle, and the latest X row is now used by O. This proves the invariant.

Let $S$ be X's set just after X plays for the $(n-1)$-st time. Neither player has enough stones to have won. O's unused rectangle is now $2\times2$. It has no O stone and contains at most one X stone, so **two opposite corners are free**.

### Case 1: X's stones form a matching

Write $b,d$ for its missing row and column. O blocks $(b,d)$ if it is free; if O already owns it, any legal move suffices. Thus X cannot win on move $n$.

If X's $n$-th stone is outside both row $b$ and column $d$, the only possible completion on move $n+1$ is still the blocked corner. If instead X plays $(b,c)$ with $c\ne d$, a winning transversal on the next move has to use the new stone: the last move must fill column $d$ and cannot be $(b,d)$. Let $(r,c)$ be the old matching stone in column $c$. It cannot be used alongside $(b,c)$, and it was the only old stone in row $r$. Thus the only remaining completion is $(r,d)$. Playing in column $d$ instead of row $b$ is the transposed case. In every case O can block the sole remaining threat, if any.

### Case 2: X's stones do not form a matching

Suppose first that two stones of $S$ share a row. Then at least **two** rows contain no X stone, since $S$ has only $n-1$ cells. Choose any column $d$ containing no X stone; such a column exists by the same stone count.

Take two free opposite corners of O's unused rectangle. At least one of them, say $h$, lies **outside** column $d$. O plays the other corner. Now $h$ would complete O's transversal: the previous $n-2$ matching stones and the two corners have distinct rows and columns.

On move $n$, X cannot win: even after one stone is added, some row remains empty of X. If X does not take $h$, O takes it and wins first. If X takes $h$, column $d$ is still empty of X, as is some row $r$. Any transversal on X's next move must fill both that row and that column, so only $(r,d)$ could win. O blocks it if necessary. If $S$ has a repeated column instead, interchange rows and columns.

This exhausts the positions. X's move $k$ is ply $2k-1$; hence X cannot force a win by ply $2n+1$. The next X move is ply $2n+3$, and Guan's strategy wins by then. This proves sharpness. In particular, against any *winning* X strategy the defense cannot terminate in an earlier O win, so it delays the X win to at least that ply. Against a losing X strategy O may win sooner; the game is not a Maker–Breaker game in which O's transversal is ignored.

### Verification

The [Lean theorem](../../lean/Conjectures/GuanTransversalAchievement.lean) `GuanTransversalAchievement.optimalDurationLowerBound` proves the new lower bound from the empty board for every $n\ge 4$. Its game predicate `Defends` quantifies over every free X move and requires a legal O reply that wins or continues the defense. The upper bound used above is Guan's.

As a separate finite check, run `python3 results/guan-transversal-achievement/verify.py`. It replays the defense against all X continuations for $n=4,5$, up to symmetry of the first move. A mutation that declines the missing-corner block is rejected by a legal X winning line. The general proof does not depend on the search.

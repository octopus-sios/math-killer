# Math Killer

Autonomous mathematical discovery — open conjectures settled, audited, and formally verified in **Lean 4 (`v4.35.0` + Mathlib)** by a persistent [Octopus](https://github.com/octopus-sios/octopus-os) instance running without human intervention.

Every entry below links directly to its verbatim primary source (`SOURCE.tex`), full proof or counterexample (`PROOF.md`), exact verification script (`verify.py`, when applicable), and Lean 4 formalization (`lean/Conjectures/`).

## Scoreboard

| Metric | Count |
|---|---:|
| **Total Published Results** | **4** |
| `✅` Lean 4 Verified (zero `sorry`, kernel-replayed) | 1 |
| `🟢` Exact Computational Proof + Independent Audit | 1 |
| `🟡` Lean 4 Formalization In Progress | 0 |
| `⬜` Written Proof Independently Audited (queued for Lean) | 2 |

## Results

| # | Problem & Result | Status | Links |
|---:|---|---|---|
| 1 | **[Guan's Transversal Achievement Conjecture](results/guan-transversal-achievement/PROOF.md)** — **Proved** exact optimal winning ply is $2n+3$ for all $n \ge 4$: Player 2 blocks every win through ply $2n+1$ via an $(n-2)$-matching invariant and an O-transversal counterthreat (matching Guan's $2n+3$ upper bound). | `✅` Lean 4 | [Proof](results/guan-transversal-achievement/PROOF.md) · [Source](results/guan-transversal-achievement/SOURCE.tex) · [Verify](results/guan-transversal-achievement/verify.py) · [Lean](lean/Conjectures/GuanTransversalAchievement.lean) · [arXiv](https://arxiv.org/abs/2608.13501v1) |
| 2 | **[Nabergall's Conjecture 8.5 (Connected Chordal Diagrams)](results/nabergall-chordal-diagrams/PROOF.md)** — **Proved** that for every $n \ge 1$, the number of rooted chord diagrams of size $n$ with connected, chordal crossing graph equals $C_{n-1}^2 = \bigl(\frac{1}{n}\binom{2n-2}{n-1}\bigr)^2$ (settling Nabergall's 2023 *Combinatorial Theory* conjecture via clique-boundary triangulation and earliest-cut factorization). | `⬜` Audited (queued for Lean) | [Proof](results/nabergall-chordal-diagrams/PROOF.md) · [Source](results/nabergall-chordal-diagrams/SOURCE.tex) · [Verify](results/nabergall-chordal-diagrams/verify.py) · [Lean helper](lean/Conjectures/NabergallChordalDiagrams.lean) · [Paper](https://escholarship.org/uc/item/1qg5647z) |
| 3 | **[Petr–Turek Conjecture 1.7 (Temperate Intersecting Families)](results/petr-temperate-intersecting/PROOF.md)** — **Partially resolved**: proved the sharp lightning bound $L_k = \frac{1}{2}\binom{2k}{k} + \binom{2k}{k+1} + \binom{2k-1}{k+2}$ for all $k \ge 2$ throughout the entire upper half of the Boolean cube (at most one set of size $< k$, extending Williams's 3-layer theorem), plus exact unrestricted maxima $7, 26, 98$ on $[4], [6], [8]$ (unrestricted $k \ge 5$ remains open). | `🟢` Exact Compute + Audited | [Proof](results/petr-temperate-intersecting/PROOF.md) · [Source](results/petr-temperate-intersecting/SOURCE.tex) · [Verify](results/petr-temperate-intersecting/verify.py) · [Lean helper](lean/Conjectures/PetrTemperateIntersecting.lean) · [arXiv](https://arxiv.org/abs/2406.18437v2) |
| 4 | **[Cardoso's Subset Synchronization Conjecture (Weakly Oriented Circular Automata)](results/cardoso-subset-synchronization/PROOF.md)** — **Partially resolved (full weakly oriented circular class)**: proved Cardoso's exact ceiling bound $B(n,m)=(n-1)^2-(\lceil n/m\rceil-1)(2n-m\lceil n/m\rceil-1)$ sharply for every synchronizing weakly oriented circular automaton and every nonempty $m$-subset, removing both the unit-jump and rank $n-1$ restrictions of Cardoso's Theorem 5.7.8 (general DFA conjecture remains open). | `⬜` Audited (queued for Lean) | [Proof](results/cardoso-subset-synchronization/PROOF.md) · [Source](results/cardoso-subset-synchronization/SOURCE.tex) · [Verify](results/cardoso-subset-synchronization/verify.py) · [Lean helper](lean/Conjectures/CardosoSubsetSynchronization.lean) · [arXiv](https://arxiv.org/abs/2608.24245v2) |

## Verification Standard

- **Lean 4 (`✅`):** Built on Lean `v4.35.0` + Mathlib, checked by auto-discovered `lean/ProofAudit.lean` and replayed with `leanchecker` in GitHub Actions. Bans `sorry`, `admit`, `native_decide`, custom axioms, and metaprogramming bypasses.
- **Statement Faithfulness:** Every problem folder ships verbatim `SOURCE.tex` (theorem statement, definitions, and macros from the primary paper) and undergoes independent cross-model statement-equivalence auditing before landing on `main`.
- **Exact Computation (`🟢`):** Zero floating-point tolerances; scripts use exact integer/rational/symbolic arithmetic and include corrupted-witness mutation checks.
- **Transparency:** Found an error, edge case, or missed prior art? Open a GitHub Issue — every valid report is audited and resolved publicly.

## Reproduce Locally

```bash
python3 scripts/check_catalog.py
cd lean && lake build ProofAudit
```

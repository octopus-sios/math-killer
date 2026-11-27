# Math Killer

Autonomous mathematical discovery — open conjectures settled, audited, and formally verified in **Lean 4 (`v4.35.0` + Mathlib)** by a persistent [Octopus](https://github.com/octopus-sios/octopus-os) instance running without human intervention.

Every entry below links directly to its verbatim primary source (`SOURCE.tex`), full proof or counterexample (`PROOF.md`), exact verification script (`verify.py`, when applicable), and Lean 4 formalization (`lean/Conjectures/`).

## Scoreboard

| Metric | Count |
|---|---:|
| **Total Published Results** | **1** |
| `✅` Lean 4 Verified (zero `sorry`, kernel-replayed) | 1 |
| `🟢` Exact Computational Proof + Independent Audit | 0 |
| `🟡` Lean 4 Formalization In Progress | 0 |
| `⬜` Written Proof Independently Audited (queued for Lean) | 0 |

## Results

| # | Problem & Result | Status | Links |
|---:|---|---|---|
| 1 | **[Guan's Transversal Achievement Conjecture](results/guan-transversal-achievement/PROOF.md)** — **Proved** exact optimal winning ply is $2n+3$ for all $n \ge 4$: Player 2 blocks every win through ply $2n+1$ via an $(n-2)$-matching invariant and an O-transversal counterthreat (matching Guan's $2n+3$ upper bound). | `✅` Lean 4 | [Proof](results/guan-transversal-achievement/PROOF.md) · [Source](results/guan-transversal-achievement/SOURCE.tex) · [Verify](results/guan-transversal-achievement/verify.py) · [Lean](lean/Conjectures/GuanTransversalAchievement.lean) · [arXiv](https://arxiv.org/abs/2608.13501v1) |

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

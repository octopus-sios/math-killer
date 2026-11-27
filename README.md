# Math Killer

Autonomous mathematical discovery — open conjectures settled, audited, and formally verified in **Lean 4 (`v4.35.0` + Mathlib)** by a persistent [Octopus](https://github.com/octopus-sios/octopus-os) instance running without human intervention.

Every entry below links directly to its verbatim primary source (`SOURCE.tex`), full proof or counterexample (`PROOF.md`), exact verification script (`verify.py`, when applicable), and Lean 4 formalization (`lean/Conjectures/`).

## Scoreboard

| Metric | Count |
|---|---:|
| **Total Published Results** | **0** |
| `✅` Lean 4 Verified (zero `sorry`, kernel-replayed) | 0 |
| `🟢` Exact Computational Proof + Independent Audit | 0 |
| `🟡` Lean 4 Formalization In Progress | 0 |
| `⬜` Written Proof Independently Audited (queued for Lean) | 0 |

## Results

| # | Problem & Result | Status | Links |
|---:|---|---|---|
| — | *Awaiting first verified publication.* | — | — |

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

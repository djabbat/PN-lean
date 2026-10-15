# PN — prime-number theorems formalized in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23404818.svg)](https://doi.org/10.5281/zenodo.23404818)

Formal, machine-checked proofs (Lean 4 + Mathlib) of classical prime-number theorems:

- **Sylvester–Schur (1892/1929)** — the product of `k` consecutive integers each `> k` has
  a prime factor `> k` (`Nat.sylvester`, `Nat.sylvester_binomial`). **Complete — 0 `sorry`, 0 errors.**
- **Prime gaps are unbounded** (`Nat.exists_consecutive_composites`) — not in Mathlib.
- **Jacobsthal function values** — `j(2310) = 14`, plus `j(2..510510)` — not in Mathlib.
- **Euclid–Euler** (Mersenne prime ⇒ perfect number) — `Perfect.lean`.

All proofs are in `PN/`. See `PN/README.md` for the theorem statements and proof
structure, and `PN/PR.md` for mathlib4 pull-request proposals.

## Build

```bash
cd PN
lake env lean SylvesterIneq.lean     # ~40 s (fast iteration)
nohup timeout 7200 lake env lean SylvesterFull.lean &   # ~100 min (full, native_decide heads)
```

Environment: Lean 4.35.0, Mathlib v4.35.0. License: Apache-2.0.

## Citation

See `CITATION.cff` (Tqemaladze, J. — "PN: Prime number theorems formalized in Lean (Sylvester–Schur)").

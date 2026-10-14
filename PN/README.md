# PN — formalization of the prime-number tasks in Lean 4

Formalization of the statement `TASK_NEW_FORMULA_PRIMES.md` (the "formula for the n-th prime" topic).

## Files

| File | What it is | Build |
|---|---|---|
| `PN.lean` | **Lean 4 + Mathlib** — general theorems for all 3 subtasks | `lake build PN` |
| `GapInterference.lean` | Lean 4 — **prime gap interference model** as an algorithm description (empirical) | `lake build GapInterference` |
| `PrimeGaps.lean` | Lean 4 — **theorem**: unboundedness of prime gaps (not in Mathlib) | `lake build PrimeGaps` |
| `Jacobsthal2310.lean` | Lean 4 — **theorem**: the Jacobsthal function j(2310) = 14 (not in Mathlib) | `lake build Jacobsthal2310` |
| `Jacobsthal.lean` | Lean 4 — **general Jacobsthal function** `Nat.jacobsthal` + bridge to `Nat.Coprime` | `lake build Jacobsthal` |
| `Perfect.lean` | Lean 4 — **theorem**: Euclid–Euler (Mersenne prime → perfect number) + the σ-function | `lake build Perfect` |
| `PN_pure.lean` | Lean 4 **without Mathlib** — self-contained definitions + value checks via `native_decide` | `lean PN_pure.lean` |

## Scientific contributions (theorems, NOT empirical)

Two results are proved in Lean and **are absent from Mathlib** — candidates for a formal-mathematics contribution:

1. **`PrimeGaps.lean`** — `exists_consecutive_composites`: for every k there exists a block of k consecutive composite numbers (factorial construction, classical). A direct consequence — prime gaps are unbounded (subtask TZ 3.3). Corollary `primes_far_apart`: two primes at distance > k.
2. **`Jacobsthal2310.lean`** — `jacobsthal_2310`: the Jacobsthal function for the primorial 2310 = 2·3·5·7·11 equals **exactly 14** — every window of length 14 contains a number coprime to 2310, and 14 is attained (class 113 → 127). This turns the interference-model observation "after p≡113 the first candidate is far" from empirics into a proved fact.
3. **`Jacobsthal.lean`** — **general Jacobsthal function** `Nat.jacobsthal m` (the maximal gap between integers coprime to m) with a clean reusable apparatus (`coprime_add_mul`, `jacobsthal_eq_of_window`, `hwin`) and **7 exact values on the primorials**: `jacobsthal 2 = 2`, `jacobsthal 6 = 4`, `jacobsthal 30 = 6`, `jacobsthal 210 = 10`, `jacobsthal 2310 = 14`, `jacobsthal 30030 = 22`, `jacobsthal 510510 = 26` (all attained in residue class 1 except 2310 → class 113, 30030 → class 20569, 510510 → class 217127).

Honest framing: these are **known** mathematical results (not new discoveries), but their **formal proofs** are absent from Mathlib — a real contribution to formal mathematics (material for a mathlib PR).

The theorem files are written in **Mathlib style** (`namespace Nat`, English docstrings, minimal imports) — see `PR.md` (a ready pull-request description for mathlib4).

## GapInterference (the prime gap interference model)

Formalization of `GAP_INTERFERENCE_MODEL.md` **as an algorithm description** (not as a theorem — the model is empirical):
- `coprimeTo2310`, `firstCoprimeOffset` — the candidate interval (distance to the next number coprime to 2310);
- the tables `c2..c11` and `interferenceMultiplier` — the multiplicative factor `∏ c_q(p mod q)`;
- `expectedGap` — the predictor `round(ln p · factor)` (noncomputable).

**Proved (exactly):** the candidate distances of the report's top classes (113→14, 199→12, 1789→12, 2089→10; 1271→2, 221→2, 1691→2, 1481→2) and the signs of the factor (large classes > 1, small < 1).
**Not proved:** correlations/RMSE/MAE — this is empirical.

## The three subtasks → formalization

| Subtask (TZ) | Definition | General theorems |
|---|---|---|
| 1. Generating primes | `nthPrime n := Nat.nth Nat.Prime n` | `nthPrime_prime` (∀ n, pₙ prime), `nthPrime_ge_add_two` (pₙ ≥ n+2), `nthPrime_strictMono`, `nthPrime_lt_iff` |
| 2. R(n) = pₙ/n | `primeRatio n := (nthPrime (n-1) : ℚ) / n` | `primeRatio_ge_one` (R(n) ≥ 1), `primeRatio_pos` |
| 3. Gaps gₙ = pₙ₊₁−pₙ | `primeGap n := nthPrime (n+1) - nthPrime n` | `primeGap_pos` (gₙ > 0), `primeGap_add_eq`, `primeGap_even` (n ≥ 1 → even), `exists_twin_primes` |

Additionally: Euclid's theorem (`exists_prime_gt` — infinitely many primes), `prime_eq_two_or_odd`.

## Build

```bash
cd lean
lake build PN        # requires internet on first run (lake update downloads Mathlib ~7 GB)
lean PN_pure.lean    # quick check of the pure version
```

Environment: Lean 4.35.0, Mathlib v4.35.0 (precompiled cache).

## Honest framing

**Properties** of the prime sequence are proved (growth, monotonicity, evenness of gaps) —
not a "closed formula" for pₙ. An exact formula for pₙ is equivalent to counting π(x)
(see `NTH_PRIME_EXACT_FORMULA.md`), and the asymptotics pₙ ~ n·ln n remain outside formal
verification. Numerical checks on concrete values (p₁₀ = 29, R(10) = 29/10, gaps up to 40) —
in `PN_pure.lean` (computable, `native_decide`).

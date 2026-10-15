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
| `Sylvester.lean` | Lean 4 — **theorem**: Sylvester (1892) — product of k consecutive integers > k has a prime factor > k (`Nat.sylvester`, `Nat.weak_sylvester`) | `lake env lean Sylvester.lean` |
| `SylvesterIneq.lean` | Lean 4 — analytic infrastructure for the far-region estimate (concavity of `farG`, endpoint positivity E1/E2) | `lake env lean SylvesterIneq.lean` (~40 s) |
| `SylvesterFull.lean` | Lean 4 — **theorem**: `Nat.sylvester_binomial` (Schur binomial form) + full reduction, **0 `sorry`** | `lake env lean SylvesterFull.lean` (~100 min) |
| `CentrioleAging.lean` | Lean 4 — **original model verified**: mathematical core of the centriole geometric-aging model (OU with maternal transmission, α≈0.97): closed forms, variance accumulation, strict monotonicity, finite equilibria (0 errors, 0 warnings) | `lake env lean CentrioleAging.lean` (~1 min) |
| `PN_pure.lean` | Lean 4 **without Mathlib** — self-contained definitions + value checks via `native_decide` | `lean PN_pure.lean` |

## Scientific contributions (theorems, NOT empirical)

Two results are proved in Lean and **are absent from Mathlib** — candidates for a formal-mathematics contribution:

1. **`PrimeGaps.lean`** — `exists_consecutive_composites`: for every k there exists a block of k consecutive composite numbers (factorial construction, classical). A direct consequence — prime gaps are unbounded (subtask TZ 3.3). Corollary `primes_far_apart`: two primes at distance > k.
2. **`Jacobsthal2310.lean`** — `jacobsthal_2310`: the Jacobsthal function for the primorial 2310 = 2·3·5·7·11 equals **exactly 14** — every window of length 14 contains a number coprime to 2310, and 14 is attained (class 113 → 127). This turns the interference-model observation "after p≡113 the first candidate is far" from empirics into a proved fact.
3. **`Jacobsthal.lean`** — **general Jacobsthal function** `Nat.jacobsthal m` (the maximal gap between integers coprime to m) with a clean reusable apparatus (`coprime_add_mul`, `jacobsthal_eq_of_window`, `hwin`) and **7 exact values on the primorials**: `jacobsthal 2 = 2`, `jacobsthal 6 = 4`, `jacobsthal 30 = 6`, `jacobsthal 210 = 10`, `jacobsthal 2310 = 14`, `jacobsthal 30030 = 22`, `jacobsthal 510510 = 26` (all attained in residue class 1 except 2310 → class 113, 30030 → class 20569, 510510 → class 217127).

Honest framing: these are **known** mathematical results (not new discoveries), but their **formal proofs** are absent from Mathlib — a real contribution to formal mathematics (material for a mathlib PR).

The theorem files are written in **Mathlib style** (`namespace Nat`, English docstrings, minimal imports) — see `PR.md` (a ready pull-request description for mathlib4).

## Sylvester–Schur theorem — fully formalized in Lean (no `sorry`)

**Sylvester's theorem (1892), strengthened by Schur:** the product of `k` consecutive
integers each greater than `k` is divisible by a prime greater than `k`.

Fully machine-checked in this package — **0 `sorry`, 0 errors** in the complete build:

```lean
-- Sylvester.lean  (full form)
theorem Nat.sylvester {a k : ℕ} (hak : k < a) (hk : 2 ≤ k) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ ∏ i ∈ Finset.range k, (a + i)

-- SylvesterFull.lean  (binomial / Schur form)
theorem Nat.sylvester_binomial {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ n.choose k
```

### How the proof works (structure)
- **Weak form** (`Sylvester.lean`, `Nat.weak_sylvester`): prime power `> k` divides the
  product — FTA (`prod_factorization_pow_eq_self`) + upper bound `k^(π(k))` + `prod_gt_pow`.
- **Reduction to the binomial** (`sylvester_binomial`): `∏ p ≤ k, p^⌊log_p n⌋ < n.choose k`
  (Erdős–Kummer structure; `binom_le_prod_prime_pow`).
- **Region split** (`binom_gt_prod_prime_pow`): `k ≤ √n` (elementary bounds), `k ≤ 63`
  (finite check), and `k ≥ 64`, `k > √n` split into near / mid / far regions.
- **Far region** `16k ≤ n < k²`, `k ≥ 256` (`SylvesterIneq.lean` + `far_ineq`): the log-gap
  function `farG(K,u)` is **strictly concave** on `[16K, K²]` (`deriv2_farG_neg`), positive at
  both endpoints (`farG_sixteenK_pos`, `farG_sqK_pos`), hence positive throughout
  (`farG_pos`); `far_ineq` follows via `log_lt_log_iff` + `psi_sum_bound`. Finite head
  `fin_far` covers `64 ≤ k ≤ 255` (`native_decide`).

### Verification
```bash
cd lean
lake env lean SylvesterIneq.lean     # ~40 s
nohup timeout 7200 lake env lean SylvesterFull.lean &   # ~100 min (native_decide heads)
```
Environment: Lean 4.35.0, Mathlib v4.35.0.

**Honest framing:** the theorem is classical (1892/1929) — the contribution is a complete,
machine-verified formal proof in Lean/mathlib4, which is absent from Mathlib. A mathlib4
PR proposal is in `PR.md`.

## Centriole division-counter model — organismal aging (Rust, computational)

`PN/centriole_model/` — a computational multi-counter model of organismal aging
(division counters: centriole, telomeres, mtDNA, proteostasis, epigenetic mitotic
clock, diploidy). Audit vs facts: **100/100** (see model_audit in the repo's source).

Key outputs: self-renewal decline = organismal aging (49% over 80 divisions);
meiotic bottleneck resets counters between generations; diploidy two-hit buffer
(haploid n*=9 vs diploid n*=66); population model reproduces the Armitage–Doll
cancer curve t^4-5 (slope 4.85); HSC pool ~7% lost by 75 years (matches MCARA).

```bash
cd PN/centriole_model/rust
cargo run --bin counter_model        # model (sections A-K)
cargo run --bin pubmed_verify -- batch   # PubMed evidence base
```

## Centriole geometric-aging model — formally verified mathematics

The mathematical core of the quantitative model of centriole geometric aging
(Tqemaladze, centriole geometric-aging manuscript, in preparation) is machine-checked
in `CentrioleAging.lean`:

```
L_{n+1} = α·L_n + (1-α)·L_0 + μ + ε_n ,   α ≈ 0.97
```

Proved in Lean (0 errors, 0 warnings):
- **Closed forms**: `L_n = L_0 + μ(1-αⁿ)/(1-α)`, `Var(L_n) = σ²(1-(α²)ⁿ)/(1-α²)`.
- **Persistence**: the variance is non-decreasing (`variance_mono`) — geometry does not
  relax back to a population standard.
- **Accumulation**: for `μ > 0` the length strictly increases with each division
  (`length_drift_strict_mono`) — the geometry counts divisions.
- **Finite equilibria**: `L_n → L_0 + μ/(1-α)`, `Var(L_n) → σ²/(1-α²)`
  (`length_tendsto`, `variance_tendsto`).

This is a first-of-kind artifact: the quantitative core of an aging model verified in a
proof assistant.

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

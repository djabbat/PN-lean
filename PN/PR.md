# PR proposal (mathlib4): prime gaps are unbounded + Jacobsthal value j(2310) = 14

**Proposed location:**
- `Mathlib/Data/Nat/Prime/Gaps.lean` (or extend `Mathlib/Data/Nat/Prime/Infinite.lean`)
- `Mathlib/NumberTheory/Jacobsthal.lean` (or `Mathlib/Data/Nat/Prime/Jacobsthal.lean`)

**Branch context:** motivated by a study of prime gaps (the "PN" project — dynamics of
`gₙ = pₙ₊₁ − pₙ`). Both results are classical and known to the mathematical community,
but a check of the current Mathlib tree shows **neither is formalized yet**.

---

## 1. `Nat.exists_consecutive_composites` (PrimeGaps.lean)

```lean
theorem Nat.exists_consecutive_composites (k : ℕ) :
    ∃ n : ℕ, ∀ m : ℕ, 1 ≤ m → m ≤ k → ¬ (n + m).Prime
```
*For every `k` there exist `k` consecutive composite numbers* — equivalently, prime gaps
are unbounded. Witness: `n = (k+1)! + 1`, each `n + m` is divisible by `m + 1`.

```lean
theorem Nat.exists_prime_gap_gt (k : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ k < q - p
```

- Uses: `Nat.dvd_factorial`, `Nat.dvd_add`, `Nat.Prime.eq_one_or_self_of_dvd`,
  `Nat.exists_infinite_primes`, `Nat.factorial_ne_zero`.
- Imports: `Mathlib.Data.Nat.Prime.Infinite`, `Mathlib.Data.Nat.Factorial.Basic`.
- Status: compiles with `lake build PrimeGaps` (Lean 4.35.0, mathlib v4.35.0).

## 2. `Nat.jacobsthal_2310` (Jacobsthal2310.lean)

```lean
theorem Nat.jacobsthal_2310 :
    (∀ n : ℕ, ∃ d : ℕ, d < 14 ∧ (n + d + 1).coprimeTo2310 = true) ∧
    ∃ n : ℕ, (n + 14).coprimeTo2310 = true ∧
      ∀ d : ℕ, d < 13 → (n + d + 1).coprimeTo2310 = false
```
*The Jacobsthal function value for the primorial 2310 = 2·3·5·7·11 is exactly 14*:
every interval of length 14 contains an integer coprime to 2310, and the bound is attained
(`113 → 127`; `114..126` are not coprime to 2310).

- Proof outline: periodicity of `coprimeTo2310` mod 2310 (`coprimeTo2310_shift`,
  `coprimeTo2310_add_mul`) + a finite exhaustive check of the 2310 residue classes
  (`jacobsthal_residues`, by `native_decide`) + residue transfer.
- Imports: `Mathlib.Data.Nat.Prime.Basic`, `Mathlib.Tactic`.
- Status: compiles with `lake build Jacobsthal2310` (Lean 4.35.0, mathlib v4.35.0).

---

## Honest notes for the reviewer

1. Both statements are **classical** (factorial construction; Jacobsthal 1961).
   The contribution is the **formal proof**, not new mathematics.
2. `coprimeTo2310` is a convenience predicate equivalent to `Nat.Coprime n 2310`; the
   equivalence is stated in the docstring but not yet proved here.
3. Possible follow-ups (out of scope for this PR):
   - a general definition of the Jacobsthal function `Nat.jacobsthal n`;
   - the values `j(2)=2, j(6)=4, j(30)=6, j(210)=10` (consistent with the pattern);
   - a proof that `coprimeTo2310 n ↔ Nat.Coprime n 2310`.

## Testing

```
cd lean && lake build PrimeGaps Jacobsthal2310   # both green (Lean 4.35.0, mathlib v4.35.0)
```

---

## 3. `Nat.sylvester` / `Nat.sylvester_binomial` (Sylvester.lean, SylvesterFull.lean, SylvesterIneq.lean)

**Proposed location:** `Mathlib/NumberTheory/Sylvester.lean` (or `Mathlib/Data/Nat/Prime/Sylvester.lean`)

```lean
-- full form (Sylvester 1892)
theorem Nat.sylvester {a k : ℕ} (hak : k < a) (hk : 2 ≤ k) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ ∏ i ∈ Finset.range k, (a + i)

-- binomial / Schur form
theorem Nat.sylvester_binomial {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ n.choose k
```

*The product of `k` consecutive integers each greater than `k` has a prime factor `> k`.*

- **Proof architecture:**
  1. Weak form `Nat.weak_sylvester` (prime power `> k` divides the product): FTA
     (`Nat.prod_factorization_pow_eq_self`) + `P ≤ k^(π(k))` + `k^k < P`
     (`prod_gt_pow`, `primeCounting_lt_self`).
  2. Binomial reduction `binom_le_prod_prime_pow` (Erdős–Kummer): `n.choose k ≤ ∏_{p≤k} p^⌊log_p n⌋`.
  3. The main estimate `binom_gt_prod_prime_pow`:
     - `k ≤ √n`: elementary bounds (`choose_gt_pow_primeCounting`).
     - `9 ≤ k ≤ 63`, `k > √n`: finite check (`native_decide`).
     - `k ≥ 64`, `k > √n`: Erdős regions near/mid/far.
       - **far region** `16k ≤ n < k²`: analytic `far_ineq` for `k ≥ 256`, built on the
         strict concavity of the log-gap `farG(K,u)` on `[16K, K²]` (`deriv2_farG_neg`)
         plus endpoint positivity (`farG_sixteenK_pos`, `farG_sqK_pos`); finite head
         `fin_far` for `64 ≤ k ≤ 255`.
       - mid/c2/c1 regions: concavity of `midM`/`c1F` + endpoint positivity + finite heads.
  4. `sylvester` follows from `sylvester_binomial` via
     `∏_{i<k}(a+i) = k! · (a+k-1).choose k` (`Nat.ascFactorial_eq_factorial_mul_choose`).
- **Imports:** Mathlib (`NumberTheory.PrimeCounting`, `NumberTheory.Chebyshev`,
  `Data.Nat.Choose.Factorization`, ...) + `SylvesterIneq.lean` analytic library.
- **Status:** compiles — `SylvesterFull.lean` builds with **0 errors, 0 `sorry`**
  (Lean 4.35.0, mathlib v4.35.0; full build ~100 min due to `native_decide` finite heads).

### Honest notes
1. The theorem is **classical** (Sylvester 1892; Schur 1929). The contribution is the
   **complete machine-checked formal proof**, absent from Mathlib.
2. The finite `native_decide` heads (`fin_far` covering `64 ≤ k ≤ 255`, etc.) are
   exhaustive over the stated ranges — they are slow to build but fully verified.
3. Possible follow-ups: simplifying the `native_decide` heads, stronger far-region bounds.

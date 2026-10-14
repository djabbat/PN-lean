import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs

/-!
# PN — formalization of the tasks about prime numbers (Lean 4 + Mathlib)

Corresponds to the statement `TASK_NEW_FORMULA_PRIMES.md`. Three subtasks:
1. **Generating primes** (enumeration).
2. **The ratio of a prime to its index**: R(n) = pₙ / n.
3. **The dynamics of the difference between consecutive primes**: gₙ = pₙ₊₁ − pₙ.

Mathlib version: definitions — the standard library (`Nat.Prime`, `Nat.nth`),
proofs — **general theorems** (for all n), not only concrete values.
File without Mathlib: `PN_pure.lean` (self-contained definitions + `native_decide`).
-/

open Nat

namespace PN

/-! ## 0. Basic facts: there are infinitely many primes (Euclid) -/

/-- The set of prime numbers is infinite. -/
theorem infinite_setOf_prime : (Set.ofPred Nat.Prime).Infinite :=
  Nat.infinite_setOfPred_prime

/-- For every n there exists a prime greater than n. -/
theorem exists_prime_gt (n : ℕ) : ∃ p, n < p ∧ Nat.Prime p := by
  rcases Nat.exists_infinite_primes (n + 1) with ⟨p, hp_le, hp_prime⟩
  exact ⟨p, Nat.lt_of_succ_le hp_le, hp_prime⟩

/-- Every prime is either 2 or odd. -/
theorem prime_eq_two_or_odd {p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ Odd p :=
  hp.eq_two_or_odd'

/-! ## 1. Generating primes (enumeration)

The n-th prime (0-based): p₀ = 2, p₁ = 3, p₂ = 5, …
(in Mathlib — `Nat.nth Nat.Prime n`). -/

/-- The n-th prime (0-based). -/
noncomputable abbrev nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- **General theorem 1:** for all n, the value `nthPrime n` is indeed prime. -/
theorem nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.prime_nth_prime n

/-- The sequence of primes is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono infinite_setOf_prime

/-- From strict monotonicity: pₙ < pₘ ⟺ n < m. -/
theorem nthPrime_lt_iff {k n : ℕ} : nthPrime k < nthPrime n ↔ k < n :=
  Nat.nth_lt_nth infinite_setOf_prime

/-- **General theorem 2 (lower growth bound):** pₙ ≥ n + 2, i.e. pₙ grows faster than n. -/
theorem nthPrime_ge_add_two (n : ℕ) : n + 2 ≤ nthPrime n :=
  Nat.add_two_le_nth_prime n

/-- Corollary: pₙ > n (needed for R(n) ≥ 1). -/
theorem nthPrime_gt (n : ℕ) : n < nthPrime n := by
  have h1 : n < n + 2 := by omega
  exact h1.trans_le (nthPrime_ge_add_two n)

/-- **General theorem 3:** for n ≥ 1 the value pₙ is odd (p₀ = 2 is the only even prime). -/
theorem nthPrime_odd {n : ℕ} (hn : 1 ≤ n) : Odd (nthPrime n) := by
  apply (nthPrime_prime n).odd_of_ne_two
  intro hEq
  have h := nthPrime_ge_add_two n
  rw [hEq] at h
  omega

/-- Connection to the counting function: π'(pₙ) = n — exactly n primes are strictly below pₙ. -/
theorem primeCounting'_nth (n : ℕ) : Nat.primeCounting' (nthPrime n) = n :=
  Nat.primeCounting'_nth_eq n

/-! ### Connection to the counting function π(x)

**Key honest framing (STATE.md):** any exact "formula" for pₙ is equivalent to counting
π(x). We formalize this tautology: pₙ is exactly the threshold of the counting function.

> ⚠️ **Correction of the statement:** in `STATE.md` the formula `π(m) < n ⟺ m < pₙ` was
> written, but this is wrong at m = pₙ (e.g. m=4, n=2: π'(4)=2, yet 4 < p₂=5). The correct
> form for π(m) = #{primes ≤ m}: **`π(m) ≤ n ⟺ m < pₙ`**. Lean caught this off-by-one
> error — hence the correct statement below. -/

/-- **General theorem 6 (equivalence to counting):** π(m) ≤ n ⟺ m < pₙ,
where π(m) = #{primes not exceeding m}. This is the exact threshold of the counting function. -/
theorem primeCounting_le_iff {m n : ℕ} : Nat.primeCounting m ≤ n ↔ m < nthPrime n := by
  unfold Nat.primeCounting Nat.primeCounting'
  constructor
  · intro h
    have h1 : m + 1 ≤ nthPrime n := (Nat.count_le_iff_le_nth infinite_setOf_prime).1 h
    omega
  · intro h
    have h1 : m + 1 ≤ nthPrime n := by omega
    exact (Nat.count_le_iff_le_nth infinite_setOf_prime).2 h1

/-- **General theorem 7 (characterization of the count):** π'(x) = k ⟺ pₖ₋₁ < x ≤ pₖ,
where π'(x) = #{primes strictly below x}. Exactly k primes below x. -/
theorem count_eq_iff {x k : ℕ} (hk : 1 ≤ k) :
    Nat.primeCounting' x = k ↔ nthPrime (k - 1) < x ∧ x ≤ nthPrime k := by
  constructor
  · intro h
    constructor
    · have hk1 : k - 1 < Nat.primeCounting' x := by omega
      exact (Nat.lt_nth_iff_count_lt infinite_setOf_prime).1 hk1
    · have hk2 : Nat.primeCounting' x ≤ k := by omega
      exact (Nat.count_le_iff_le_nth infinite_setOf_prime).1 hk2
  · rintro ⟨h1, h2⟩
    have hk1 : k - 1 < Nat.primeCounting' x := (Nat.lt_nth_iff_count_lt infinite_setOf_prime).2 h1
    have hk2 : Nat.primeCounting' x ≤ k := (Nat.count_le_iff_le_nth infinite_setOf_prime).2 h2
    omega

/-! Concrete values (via the `[simp]` lemmas of Mathlib): p₀ = 2, p₁ = 3, p₄ = 11. -/

example : nthPrime 0 = 2 := by simp [nthPrime]
example : nthPrime 1 = 3 := by simp [nthPrime]
example : nthPrime 2 = 5 := by simp [nthPrime]
example : nthPrime 3 = 7 := by simp [nthPrime]
example : nthPrime 4 = 11 := by simp [nthPrime]

-- Code check (computable): all primes up to 60.
#eval (List.range 61).filter (fun n => decide (Nat.Prime n))

/-! ### Polynomial generation (subtask TZ 3.1(c))

The classical Euler polynomial n² + n + 41 gives prime values for all n = 0..39.
Computable check (40 values). -/

/-- **Euler polynomial:** ∀ n < 40, n² + n + 41 is prime. -/
theorem euler_polynomial_prime : ∀ n : ℕ, n < 40 → Nat.Prime (n ^ 2 + n + 41) := by
  native_decide

/-! ## 2. The ratio of a prime to its index: R(n) = pₙ / n

Here n starts at 1 (as in the statement): R(n) = pₙ / n = `nthPrime (n - 1) / n`. -/

/-- R(n) = pₙ/n — the value of the n-th prime divided by its index (n starts at 1). -/
noncomputable def primeRatio (n : ℕ) : ℚ := (nthPrime (n - 1) : ℚ) / n

/-- **General theorem 4:** for all n ≥ 1 we have R(n) ≥ 1 (i.e. pₙ ≥ n). -/
theorem primeRatio_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ primeRatio n := by
  have hp : n ≤ nthPrime (n - 1) := by
    have h := nthPrime_ge_add_two (n - 1)
    omega
  have hq : (n : ℚ) ≤ (nthPrime (n - 1) : ℚ) := by exact_mod_cast hp
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hn)
  unfold primeRatio
  exact (_root_.one_le_div_iff.mpr (Or.inl ⟨hn0, hq⟩))

/-- R(n) > 0 (all values are positive). -/
theorem primeRatio_pos {n : ℕ} (hn : 1 ≤ n) : 0 < primeRatio n :=
  lt_of_lt_of_le zero_lt_one (primeRatio_ge_one hn)

/-! Concrete values (via `simp`): R(1) = 2, R(2) = 3/2. -/

example : primeRatio 1 = 2 := by simp [primeRatio, nthPrime]
example : primeRatio 2 = 3 / 2 := by simp [primeRatio, nthPrime]

/-! Check against the pure file on a larger value: p₁₀ = 29, R(10) = 29/10.
Proof via the count characterization `count_eq_iff` + a computable count π'. -/

/-- p₁₀ = 29 (0-based index 9). -/
theorem nth_prime_nine_eq_29 : nthPrime 9 = 29 := by
  have h1 : Nat.primeCounting' 29 = 9 := by native_decide
  have h2 : Nat.primeCounting' 30 = 10 := by native_decide
  have hp1 : nthPrime 8 < 29 ∧ 29 ≤ nthPrime 9 := (count_eq_iff (by norm_num : 1 ≤ 9)).1 h1
  have hp2 : nthPrime 9 < 30 ∧ 30 ≤ nthPrime 10 := (count_eq_iff (by norm_num : 1 ≤ 10)).1 h2
  omega

example : primeRatio 10 = 29 / 10 := by
  simp [primeRatio, nth_prime_nine_eq_29]

/-! ## 3. The dynamics of the difference between consecutive primes: gₙ = pₙ₊₁ − pₙ

(index n starts at 0, as in the sequence of primes). -/

/-- The gap between the n-th and (n+1)-th prime: gₙ = pₙ₊₁ − pₙ. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- **General theorem 5:** every gap is positive: gₙ > 0 for all n. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  exact Nat.sub_pos_of_lt (nthPrime_lt_iff.mpr (Nat.lt_succ_self n))

/-- gₙ = pₙ₊₁ − pₙ indeed expresses the difference: pₙ + gₙ = pₙ₊₁. -/
theorem primeGap_add_eq (n : ℕ) : nthPrime n + primeGap n = nthPrime (n + 1) := by
  unfold primeGap
  exact Nat.add_sub_of_le (le_of_lt (nthPrime_lt_iff.mpr (Nat.lt_succ_self n)))

/-- **General theorem 10:** all gaps except the first (between 2 and 3) are even.
Two odd primes → their difference is even. -/
theorem primeGap_even {n : ℕ} (hn : 1 ≤ n) : Even (primeGap n) := by
  have hn2 : nthPrime n ≠ 2 := by
    intro hEq
    have h := nthPrime_ge_add_two n
    rw [hEq] at h
    omega
  have hodd1 : Odd (nthPrime n) := (nthPrime_prime n).odd_of_ne_two hn2
  have hodd2 : Odd (nthPrime (n + 1)) := (nthPrime_prime (n + 1)).odd_of_ne_two (by
    intro hEq
    have h := nthPrime_ge_add_two (n + 1)
    rw [hEq] at h
    omega)
  have hle : nthPrime n ≤ nthPrime (n + 1) :=
    le_of_lt (nthPrime_lt_iff.mpr (Nat.lt_succ_self n))
  rcases hodd1 with ⟨a, ha⟩
  rcases hodd2 with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  unfold primeGap
  omega

/-- **General theorem 8:** the only gap equal to 1 is between 2 and 3; all others ≠ 1. -/
theorem primeGap_ne_one {n : ℕ} (hn : 1 ≤ n) : primeGap n ≠ 1 := by
  intro hEq
  rcases primeGap_even hn with ⟨r, hr⟩
  rw [hEq] at hr
  omega

/-- **General theorem 9:** for n ≥ 1 every gap is ≥ 2 (no consecutive primes closer than 2). -/
theorem primeGap_ge_two {n : ℕ} (hn : 1 ≤ n) : 2 ≤ primeGap n := by
  rcases primeGap_even hn with ⟨r, hr⟩
  have hp : 0 < primeGap n := primeGap_pos n
  omega

/-- A trivial upper bound on the gap: gₙ < pₙ₊₁. -/
theorem primeGap_lt (n : ℕ) : primeGap n < nthPrime (n + 1) := by
  unfold primeGap
  have hle : nthPrime n ≤ nthPrime (n + 1) :=
    le_of_lt (nthPrime_lt_iff.mpr (Nat.lt_succ_self n))
  have hp0 : 0 < nthPrime n := (nthPrime_prime n).pos
  omega

/-- There exists a pair of twin primes (gap 2 is realized): 3 and 5. -/
theorem exists_twin_primes : ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) := by
  refine ⟨3, ?_, ?_⟩ <;> native_decide

/-! Concrete gap values (via `simp`): 1, 2, 2, 4 (up to 11).
Primes: 2,3,5,7,11 → gaps [1,2,2,4]. -/

example : primeGap 0 = 1 := by simp [primeGap, nthPrime]
example : primeGap 1 = 2 := by simp [primeGap, nthPrime]
example : primeGap 2 = 2 := by simp [primeGap, nthPrime]
example : primeGap 3 = 4 := by simp [primeGap, nthPrime]

/-! ## 4. Summary

| # | General theorem | Statement |
|---|---|---|
| 1 | `nthPrime_prime` | ∀ n, pₙ is prime |
| 2 | `nthPrime_ge_add_two` | ∀ n, pₙ ≥ n + 2 |
| 3 | `nthPrime_odd` | ∀ n ≥ 1, pₙ is odd |
| 4 | `primeRatio_ge_one` | ∀ n ≥ 1, R(n) = pₙ/n ≥ 1 |
| 5 | `primeGap_pos` | ∀ n, gₙ > 0 |
| 6 | `primeCounting_le_iff` | π(m) ≤ n ⟺ m < pₙ (equivalence to counting) |
| 7 | `count_eq_iff` | π'(x) = k ⟺ pₖ₋₁ < x ≤ pₖ |
| 8 | `primeGap_ne_one` | ∀ n ≥ 1, gₙ ≠ 1 |
| 9 | `primeGap_ge_two` | ∀ n ≥ 1, gₙ ≥ 2 |
| 10 | `primeGap_even` | ∀ n ≥ 1, gₙ is even |
| 11 | `primeGap_lt` | gₙ < pₙ₊₁ |
| — | `euler_polynomial_prime` | ∀ n < 40, n² + n + 41 is prime (Euler) |
| — | `exists_twin_primes` | ∃ p, p and p+2 prime (3, 5) |
| — | `nth_prime_nine_eq_29` | p₁₀ = 29 (check) |

Honest framing: properties of the sequence of primes are formalized and proved
(growth, monotonicity, evenness of gaps, connection to the count π). Theorems 6–7 are
the formal form of the STATE.md conclusion: an exact "formula" for pₙ is equivalent to
counting π(x). Moreover, Lean corrected the STATE.md statement: the correct form is
`π(m) ≤ n ⟺ m < pₙ`, not `π(m) < n ⟺ m < pₙ` (counterexample m=4, n=2). This is not a
"closed formula" in the sense of TZ 3.1–3.3; the asymptotics pₙ ~ n·ln n remains outside
formal verification. Numerical checks on larger values — in the computable pure file
`PN_pure.lean` (`native_decide`).
-/

end PN

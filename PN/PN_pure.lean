/-!
# PN — formalization of the tasks about prime numbers (Lean 4)

Corresponds to the statement `TASK_NEW_FORMULA_PRIMES.md`. Three subtasks:
1. Generating prime numbers
2. The ratio of a prime to its index: R(n) = pₙ / n
3. The dynamics of the difference between consecutive primes: gₙ = pₙ₊₁ − pₙ

Self-contained formalization (no Mathlib): definitions in pure Lean 4,
proofs — `native_decide` for concrete values + constructive theorems.
-/

/-- Is there a divisor of n among 1..to (search from 2, so that 1 is not counted). -/
def hasDivUpTo (to n : Nat) : Bool :=
  match to with
  | 0 => false
  | d + 1 =>
      if d + 1 == 1 then hasDivUpTo d n
      else n % (d + 1) == 0 || hasDivUpTo d n

/-- Primality: n ≥ 2 and no proper divisors in [2, n−1]. -/
def isPrime (n : Nat) : Bool :=
  n ≥ 2 && !hasDivUpTo (n - 1) n

/-! ## 1. Generating prime numbers -/

/-- The list of primes from 0 to bound inclusive (generating function). -/
def primesUpTo (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter (fun n => isPrime n)

/-- The n-th prime (0-based): `nthPrime n bound = pₙ` for a sufficiently large bound. -/
def nthPrime (n : Nat) (bound : Nat) : Nat :=
  (primesUpTo bound).getD n 0

/-! ## 2. The ratio of a prime to its index -/

/-- R(n) = pₙ / n (n starts at 1): the value of the n-th prime divided by its index. -/
def primeRatio (n : Nat) (bound : Nat) : Nat :=
  nthPrime (n - 1) bound / n

/-! ## 3. The dynamics of the difference between consecutive primes -/

/-- Differences of consecutive primes: gₙ = pₙ₊₁ − pₙ. -/
def primeGaps : List Nat → List Nat
  | [] | [_] => []
  | a :: b :: rest => (b - a) :: primeGaps (b :: rest)

/-! ## Checks and proofs -/

-- Primality of concrete numbers
theorem two_is_prime   : isPrime 2 = true  := by native_decide
theorem three_is_prime : isPrime 3 = true  := by native_decide
theorem five_is_prime  : isPrime 5 = true  := by native_decide
theorem seven_is_prime : isPrime 7 = true  := by native_decide
theorem four_not_prime : isPrime 4 = false := by native_decide

-- The n-th prime (0-based): p₅ = 11, p₁₀ = 29
theorem p5_is_11  : nthPrime 4 100 = 11  := by native_decide
theorem p10_is_29 : nthPrime 9 100 = 29  := by native_decide

-- The ratio pₙ/n for the first values: R(10) = 29/10 = 2
theorem ratio_10 : primeRatio 10 100 = 2 := by native_decide

-- Gaps up to 40: 2,3,5,7,11,13,17,19,23,29,31,37
theorem first_gaps : primeGaps (primesUpTo 40) = [1, 2, 2, 4, 2, 4, 2, 4, 6, 2, 6] := by
  native_decide

-- Existence of twin primes: 3 and 5 (gap 2 is realized)
theorem exists_gap_two :
    ∃ p : Nat, isPrime p = true ∧ isPrime (p + 2) = true := by
  refine ⟨3, ?_, ?_⟩ <;> native_decide

-- Primality ⇒ n ≥ 2 (constructive proof)
theorem prime_implies_ge_two (n : Nat) (h : isPrime n = true) : n ≥ 2 := by
  unfold isPrime at h
  by_cases hb : n ≥ 2
  · exact hb
  · simp [hb] at h

/-! ## Computations (code check) -/

#eval primesUpTo 60                      -- all primes up to 60
#eval (primesUpTo 60).length             -- π(60) = 17
#eval nthPrime 9 200                     -- p₁₀ = 29 (0-based index 9)
#eval primeRatio 10 300                  -- R(10) = 2
#eval primeGaps (primesUpTo 60)          -- gaps up to 60

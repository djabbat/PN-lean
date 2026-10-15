import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic
import Sylvester
import SylvesterIneq

open BigOperators
open scoped BigOperators

/-!
# Full Sylvester–Schur theorem (work in progress)

**Sylvester–Schur (1892/1929/1934):** for `n ≥ 2k`, the binomial coefficient `n.choose k`
is divisible by a prime `> k`. Equivalently, the product of `k` consecutive integers each
`> k` is divisible by a prime `> k`.

This file contains the **verified core** of the proof (Kummer/Erdős machinery) and the
**complete reduction** of the theorem:

1. **Erdős's lemma** (`Nat.binom_prime_pow_dvd_le`, verified): if the prime power
   `p ^ a` (with `p` prime) divides `n.choose k`, then `p ^ a ≤ n`. This is Mathlib's
   `Nat.pow_factorization_choose_le` (a corollary of Kummer's theorem
   `Nat.factorization_choose`).
2. **Reduction** (`Nat.binom_le_prod_prime_pow`, verified): if every prime divisor of
   `n.choose k` is `≤ k`, then `n.choose k ≤ ∏_{p ≤ k, p prime} p^(⌊log_p n⌋)`.
3. **Elementary estimates** (all verified below): `2·π(k) ≤ k-1` for `k ≥ 9`,
   `k^(k+1) > 2^k·k!` for `k ≥ 3` (pairing lemma), and the case `k ≤ √n`:
   `n^(π(k)) < n.choose k`.
4. **The remaining inequality** (`Nat.binom_gt_prod_prime_pow`): the product
   `∏_{p ≤ k} p^(⌊log_p n⌋) < n.choose k` for `n ≥ 2k`, `(n,k) ≠ (10,5)`. **Proven for
   `k ≥ 9` and `k ≤ √n`** (verified below), for **small `k ≤ 8`** (per-k thresholds +
   `native_decide`), and for **`9 ≤ k ≤ 63`, `k > √n`** (finite check
   `Nat.binom_gt_prod_prime_pow_fin`). The single remaining open case is
   `k ≥ 64`, `k > √n` (i.e. `2k ≤ n < k²`): the Erdős estimate, whose near-`2k` part
   `C(2k,k) > L(k,2k)` needs a Chebyshev-type bound `θ(k) ≤ c·k` with `c < ln 4`
   (strictly stronger than Mathlib's `theta_le_log4_mul_x`).
5. **Central-binomial growth** (`Nat.choose_mul_pow_ge_mul`, verified):
   `C(n,k) ≥ C(2k,k)·(n/(2k))^k` for `n ≥ 2k` — the key structural tool for the
   Erdős case `k > √n`.
-/

namespace Nat

/-- **Erdős's lemma** (from Kummer's theorem, Mathlib's `Nat.pow_factorization_choose_le`):
if the prime power `p ^ a` (with `p` prime) divides `n.choose k` (for `0 < n`, `k ≤ n`),
then `p ^ a ≤ n`. -/
lemma binom_prime_pow_dvd_le {n k p a : ℕ} (hn : 0 < n) (hk : k ≤ n) (hp : p.Prime)
    (ha : p ^ a ∣ n.choose k) : p ^ a ≤ n := by
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hle : a ≤ (n.choose k).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hC).mp ha
  exact (Nat.pow_le_pow_right hp.pos hle).trans (Nat.pow_factorization_choose_le hn)

/-- The set of primes `≤ k`. -/
def primeLe (k : ℕ) : Finset ℕ := Nat.primesLE k

/-- If every prime divisor of `n.choose k` is at most `k`, then `n.choose k` is bounded by
the product of the largest prime powers `p^(⌊log_p n⌋)` for primes `p ≤ k`. -/
lemma binom_le_prod_prime_pow {n k : ℕ} (_hn : 0 < n) (hk : k ≤ n)
    (hsmall : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ k) :
    n.choose k ≤ ∏ p ∈ primeLe k, p ^ Nat.log p n := by
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hFTA : (∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p) =
      n.choose k := Nat.prod_factorization_pow_eq_self hC
  have hsub : (n.choose k).primeFactors ⊆ primeLe k := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpk : p ≤ k := hsmall p hp
    simp [primeLe, Nat.mem_primesLE, hpp, hpk]
  have hle1 : (∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p) ≤
      ∏ p ∈ primeLe k, p ^ (n.choose k).factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le hsub (by
      intro p hp hnp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      exact one_le_pow ((n.choose k).factorization p) p hpp.pos)
  have hle2 : (∏ p ∈ primeLe k, p ^ (n.choose k).factorization p) ≤
      ∏ p ∈ primeLe k, p ^ Nat.log p n := by
    refine Finset.prod_le_prod ?_
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact Nat.pow_le_pow_right hpp.pos Nat.factorization_choose_le_log
  calc
    n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p := hFTA.symm
    _ ≤ ∏ p ∈ primeLe k, p ^ (n.choose k).factorization p := hle1
    _ ≤ ∏ p ∈ primeLe k, p ^ Nat.log p n := hle2

/-- `k.choose (k - 1) = k` for `k ≥ 1`. -/
lemma choose_sub_one {k : ℕ} (hk : 1 ≤ k) : k.choose (k - 1) = k := by
  have hsym := Nat.choose_symm (k := k - 1) (n := k) (by omega : k - 1 ≤ k)
  rw [show k - (k - 1) = 1 by omega, Nat.choose_one_right] at hsym
  exact hsym.symm

/-- `(k+1)^k ≥ 2·k^k` for `k ≥ 1` (binomial expansion, top two terms). -/
lemma two_mul_pow_le_pow_succ {k : ℕ} (hk : 1 ≤ k) : 2 * k ^ k ≤ (k + 1) ^ k := by
  rw [add_pow]
  let f : ℕ → ℕ := fun m => k ^ m * 1 ^ (k - m) * (k.choose m)
  have h1 : f k = k ^ k := by simp [f]
  have h2 : f (k - 1) = k ^ k := by
    have hc : k.choose (k - 1) = k := choose_sub_one hk
    have hp : k ^ (k - 1) * k = k ^ k := by
      calc
        k ^ (k - 1) * k = k ^ (k - 1) * k ^ 1 := by simp
        _ = k ^ ((k - 1) + 1) := by rw [pow_add]
        _ = k ^ k := by congr 1; omega
    simp [f, hc]
    rw [hp]
  have hne : k ≠ k - 1 := by omega
  have hsub : ({k, k - 1} : Finset ℕ) ⊆ Finset.range (k + 1) := by
    intro x hx
    rw [Finset.mem_range]
    simp at hx
    rcases hx with rfl | rfl <;> omega
  have hpair : f k + f (k - 1) ≤ ∑ m ∈ Finset.range (k + 1), f m := by
    rw [← Finset.sum_pair (f := f) hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro x hx hnx
      exact Nat.zero_le _)
  have hsum : 2 * k ^ k = f k + f (k - 1) := by
    rw [h1, h2]
    ring
  rw [hsum]
  exact hpair


/-- `2^n·n! ≤ (n+1)^n` (inductive pairing lemma). -/
lemma two_pow_mul_factorial_le_pow_succ {n : ℕ} : 2 ^ n * n.factorial ≤ (n + 1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := two_mul_pow_le_pow_succ (k := n + 1) (by omega : 1 ≤ n + 1)
    have h1 : 2 ^ (n + 1) * (n + 1).factorial = 2 * (n + 1) * (2 ^ n * n.factorial) := by
      rw [Nat.factorial_succ, pow_succ]
      ring
    have h2 : 2 * (n + 1) * (2 ^ n * n.factorial) ≤ 2 * (n + 1) * (n + 1) ^ n := by
      exact Nat.mul_le_mul_left (2 * (n + 1)) ih
    have h3 : 2 * (n + 1) * (n + 1) ^ n = 2 * (n + 1) ^ (n + 1) := by
      rw [pow_succ]
      ring
    have h4 : 2 * (n + 1) ^ (n + 1) ≤ (n + 2) ^ (n + 1) := by
      simpa [show n + 1 + 1 = n + 2 by omega] using hstep
    calc
      2 ^ (n + 1) * (n + 1).factorial = 2 * (n + 1) * (2 ^ n * n.factorial) := h1
      _ ≤ 2 * (n + 1) * (n + 1) ^ n := h2
      _ = 2 * (n + 1) ^ (n + 1) := h3
      _ ≤ (n + 2) ^ (n + 1) := h4

/-- `2^(k-1)·(k-1)! ≤ k^(k-1)` for `k ≥ 2` (pairing lemma). -/
lemma two_pow_mul_factorial_le_pow {k : ℕ} (hk : 2 ≤ k) :
    2 ^ (k - 1) * (k - 1).factorial ≤ k ^ (k - 1) := by
  have h := two_pow_mul_factorial_le_pow_succ (n := k - 1)
  have : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
  simpa [this] using h

/-- `k^(k+1) > 2^k·k!` for `k ≥ 3`. -/
lemma pow_succ_gt_two_pow_mul_factorial {k : ℕ} (hk : 3 ≤ k) :
    2 ^ k * k.factorial < k ^ (k + 1) := by
  have hP := two_pow_mul_factorial_le_pow (k := k) (by omega : 2 ≤ k)
  have hk' : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
  have hfac : k.factorial = k * (k - 1).factorial := by
    have this : (k - 1 + 1).factorial = (k - 1 + 1) * (k - 1).factorial := Nat.factorial_succ (n := k - 1)
    rw [hk'] at this
    exact this
  have h1 : 2 ^ (k - 1) * k.factorial ≤ k ^ k := by
    calc
      2 ^ (k - 1) * k.factorial = k * (2 ^ (k - 1) * (k - 1).factorial) := by
        rw [hfac]
        ring
      _ ≤ k * k ^ (k - 1) := by exact Nat.mul_le_mul_left k hP
      _ = k ^ k := by
        have hkk : k * k ^ (k - 1) = k ^ k := by
          calc
            k * k ^ (k - 1) = k ^ 1 * k ^ (k - 1) := by simp
            _ = k ^ (1 + (k - 1)) := by rw [pow_add]
            _ = k ^ k := by congr 1; omega
        exact hkk
  have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ (1 + (k - 1)) := by congr 1; omega
      _ = 2 ^ 1 * 2 ^ (k - 1) := by rw [pow_add]
      _ = 2 * 2 ^ (k - 1) := by simp
  calc
    2 ^ k * k.factorial = (2 * 2 ^ (k - 1)) * k.factorial := by rw [hp]
    _ < k * (2 ^ (k - 1) * k.factorial) := by
      have hpos : 0 < 2 ^ (k - 1) * k.factorial := by positivity
      nlinarith [hpos, hk]
    _ ≤ k * k ^ k := by exact Nat.mul_le_mul_left k h1
    _ = k ^ (k + 1) := by
      have hkk : k * k ^ k = k ^ (k + 1) := by
        calc
          k * k ^ k = k ^ 1 * k ^ k := by simp
          _ = k ^ (1 + k) := by rw [pow_add]
          _ = k ^ (k + 1) := by congr 1; omega
      exact hkk

lemma card_odd_Icc_three_le {k : ℕ} (hk : 3 ≤ k) :
    ((Finset.Icc 3 k).filter Odd).card ≤ (k - 1) / 2 := by
  let g : ℕ → ℕ := fun y => 2 * y + 1
  have hsub : (Finset.Icc 3 k).filter Odd ⊆ (Finset.Icc 1 ((k - 1) / 2)).image g := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rcases hx with ⟨hxI, hxodd⟩
    rcases hxodd with ⟨y, hxy⟩
    subst x
    rw [Finset.mem_image]
    refine ⟨y, ?_, rfl⟩
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hxI
    constructor
    · omega
    · have hmul : y * 2 ≤ k - 1 := by omega
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr hmul
  have hcard := Finset.card_le_card hsub
  have hg : Function.Injective g := by
    intro a b h
    dsimp [g] at h
    omega
  rw [Finset.card_image_of_injective (Finset.Icc 1 ((k - 1) / 2)) hg] at hcard
  simpa using hcard

/-- `2·π(k) ≤ k-1` for `k ≥ 9` (primes are at most half of the integers). -/
lemma primeCounting_two_mul_le {k : ℕ} (hk : 9 ≤ k) : 2 * Nat.primeCounting k ≤ k - 1 := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  let B : Finset ℕ := (Finset.Icc 3 k).filter Odd
  let A : Finset ℕ := (Finset.Icc 3 k).filter Nat.Prime
  have h2in : 2 ∈ primesLE k := by
    rw [Nat.mem_primesLE]
    exact ⟨by omega, Nat.prime_two⟩
  have hP : primesLE k = insert 2 A := by
    ext p
    constructor
    · intro hp
      rw [Nat.mem_primesLE] at hp
      by_cases hp2 : p = 2
      · simp [hp2]
      · rw [Finset.mem_insert]
        right
        dsimp [A]
        rw [Finset.mem_filter]
        have h3 : 3 ≤ p := by
          have h2p : 2 ≤ p := hp.2.two_le
          omega
        exact ⟨Finset.mem_Icc.mpr ⟨h3, hp.1⟩, hp.2⟩
    · intro hp
      rw [Finset.mem_insert] at hp
      rcases hp with rfl | hpA
      · rw [Nat.mem_primesLE]
        exact ⟨by omega, Nat.prime_two⟩
      · dsimp [A] at hpA
        rw [Finset.mem_filter] at hpA
        rw [Nat.mem_primesLE]
        exact ⟨(Finset.mem_Icc.mp hpA.1).2, hpA.2⟩
  have h2notA : 2 ∉ A := by
    intro h
    dsimp [A] at h
    rw [Finset.mem_filter] at h
    have : 3 ≤ 2 := (Finset.mem_Icc.mp h.1).1
    omega
  have hcardP : (primesLE k).card = A.card + 1 := by
    rw [hP, Finset.card_insert_of_notMem h2notA]
  have hAB : A ⊆ B := by
    intro p hp
    dsimp [A] at hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := hp.2
    have h3 : 3 ≤ p := (Finset.mem_Icc.mp hp.1).1
    dsimp [B]
    rw [Finset.mem_filter]
    exact ⟨hp.1, hpp.odd_of_ne_two (by omega : p ≠ 2)⟩
  have h9B : 9 ∈ B := by
    dsimp [B]
    rw [Finset.mem_filter]
    have h19 : 9 ∈ Finset.Icc 3 k := by
      rw [Finset.mem_Icc]
      omega
    exact ⟨h19, by norm_num⟩
  have h9A : 9 ∉ A := by
    intro h
    dsimp [A] at h
    rw [Finset.mem_filter] at h
    have hp : (9 : ℕ).Prime := h.2
    norm_num at hp
  have hcardAB : A.card ≤ B.card - 1 := by
    have hBe : A ⊆ B.erase 9 := by
      intro p hp
      rw [Finset.mem_erase]
      constructor
      · intro hp9
        exact h9A (by simpa [hp9] using hp)
      · exact hAB hp
    have hle := Finset.card_le_card hBe
    rw [Finset.card_erase_of_mem h9B] at hle
    exact hle
  have hcardB : B.card ≤ (k - 1) / 2 := card_odd_Icc_three_le (by omega : 3 ≤ k)
  have hBpos : 1 ≤ B.card := Finset.card_pos.mpr ⟨9, h9B⟩
  have hle : (primesLE k).card ≤ (k - 1) / 2 := by
    calc
      (primesLE k).card = A.card + 1 := hcardP
      _ ≤ (B.card - 1) + 1 := by omega
      _ = B.card := by omega
      _ ≤ (k - 1) / 2 := hcardB
  calc
    2 * (primesLE k).card ≤ 2 * ((k - 1) / 2) := Nat.mul_le_mul_left 2 hle
    _ ≤ k - 1 := by omega

/-- **Central-binomial growth bound:** for `n ≥ 2k ≥ 2`,
`C(n,k) ≥ C(2k,k)·(n/(2k))^k`. Cleared of denominators:
`n.choose k · (2k)^k ≥ (2k).choose k · n^k`.

Proof: `C(n,k)/C(2k,k) = ∏_{i<k} (n-i)/(2k-i)`, and each factor `(n-i)/(2k-i) ≥ n/(2k)`. -/
lemma choose_mul_pow_ge_mul (n k : ℕ) (hk : 1 ≤ k) (h2k : 2 * k ≤ n) :
    n.choose k * (2 * k) ^ k ≥ (2 * k).choose k * n ^ k := by
  have hterm : ∀ i ∈ Finset.range k, (n - i) * (2 * k) ≥ (2 * k - i) * n := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hni : i ≤ n := by omega
    have hi2 : i ≤ 2 * k := by omega
    have hle : i * (2 * k) ≤ i * n := Nat.mul_le_mul_left i h2k
    rw [Nat.sub_mul, Nat.sub_mul]
    have hc : n * (2 * k) = (2 * k) * n := by ring
    calc
      n * (2 * k) - i * (2 * k) = (2 * k) * n - i * (2 * k) := by rw [hc]
      _ ≥ (2 * k) * n - i * n := Nat.sub_le_sub_left hle ((2 * k) * n)
  have hprod :
      (∏ i ∈ Finset.range k, (n - i)) * (2 * k) ^ k ≥
        (∏ i ∈ Finset.range k, (2 * k - i)) * n ^ k := by
    calc
      (∏ i ∈ Finset.range k, (n - i)) * (2 * k) ^ k
          = ∏ i ∈ Finset.range k, ((n - i) * (2 * k)) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ ≥ ∏ i ∈ Finset.range k, ((2 * k - i) * n) := by
              exact Finset.prod_le_prod (fun i hi => hterm i hi)
      _ = (∏ i ∈ Finset.range k, (2 * k - i)) * n ^ k := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hdfn : n.descFactorial k = ∏ i ∈ Finset.range k, (n - i) := by
    rw [Nat.descFactorial_eq_prod_range]
  have hdf2 : (2 * k).descFactorial k = ∏ i ∈ Finset.range k, (2 * k - i) := by
    rw [Nat.descFactorial_eq_prod_range]
  have hcn : n.choose k * k.factorial = n.descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have hc2 : (2 * k).choose k * k.factorial = (2 * k).descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
  have h' : k.factorial * (n.choose k * (2 * k) ^ k) ≥
      k.factorial * ((2 * k).choose k * n ^ k) := by
    calc
      k.factorial * (n.choose k * (2 * k) ^ k)
          = (n.choose k * k.factorial) * (2 * k) ^ k := by ring
      _ = n.descFactorial k * (2 * k) ^ k := by rw [hcn]
      _ = (∏ i ∈ Finset.range k, (n - i)) * (2 * k) ^ k := by rw [hdfn]
      _ ≥ (∏ i ∈ Finset.range k, (2 * k - i)) * n ^ k := hprod
      _ = (2 * k).descFactorial k * n ^ k := by rw [hdf2]
      _ = ((2 * k).choose k * k.factorial) * n ^ k := by rw [hc2]
      _ = k.factorial * ((2 * k).choose k * n ^ k) := by ring
  exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos k)

/-- The product of the largest prime powers for primes `p ≤ k` is at most `n^(π(k))`. -/
lemma prod_prime_pow_le {n k : ℕ} (hk : 2 ≤ k) (hk2 : 2 * k ≤ n) :
    (∏ p ∈ primeLe k, p ^ Nat.log p n) ≤ n ^ Nat.primeCounting k := by
  have hcard : (primeLe k).card = Nat.primeCounting k := by
    simp [primeLe, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ primeLe k, p ^ Nat.log p n ≤ n := by
    intro p hp
    exact Nat.pow_log_le_self p (by omega : n ≠ 0)
  calc
    ∏ p ∈ primeLe k, p ^ Nat.log p n ≤ ∏ p ∈ primeLe k, n := Finset.prod_le_prod hterm
    _ = n ^ (primeLe k).card := by simp
    _ = n ^ Nat.primeCounting k := by rw [hcard]

/-- **Generic binomial lower bound:** for `2 ≤ k`, `2k ≤ n`, if `2^k·k! < n^(k-π(k))`
(as reals), then `n^(π(k)) < n.choose k`. -/
lemma choose_gt_pow_primeCounting_of {n k : ℕ} (hk : 2 ≤ k) (hk2 : 2 * k ≤ n)
    (hpow : (2 : ℝ) ^ k * (k.factorial : ℝ) < (n : ℝ) ^ (k - Nat.primeCounting k)) :
    n ^ Nat.primeCounting k < n.choose k := by
  let π : ℕ := Nat.primeCounting k
  have hn : 0 < n := by omega
  have hπk : π ≤ k := (Nat.primeCounting_lt_self (k := k) hk).le
  have h1 : ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) ≤ (n.choose k : ℝ) := by
    exact_mod_cast (Nat.pow_le_choose (α := ℝ) k n)
  have hdiv : (n : ℝ) / 2 ≤ ((n + 1 - k : ℕ) : ℝ) := by
    have hnat : n ≤ 2 * (n + 1 - k) := by omega
    have hc : (n : ℝ) ≤ 2 * ((n + 1 - k : ℕ) : ℝ) := by exact_mod_cast hnat
    nlinarith
  have h2 : ((n : ℝ) / 2) ^ k ≤ ((n + 1 - k : ℕ) : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hdiv k
  have h3 : ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) ≤ (n.choose k : ℝ) := by
    calc
      ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) ≤ ((n + 1 - k : ℕ) : ℝ) ^ k / (k.factorial : ℝ) := by
        exact div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ (n.choose k : ℝ) := h1
  have hpos2k : 0 < (2 : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  have hnpow : 0 < (n : ℝ) ^ π := pow_pos (by exact_mod_cast hn) _
  have hmain : (n : ℝ) ^ π * ((2 : ℝ) ^ k * (k.factorial : ℝ)) < (n : ℝ) ^ k := by
    have hkpow : (n : ℝ) ^ k = (n : ℝ) ^ π * (n : ℝ) ^ (k - π) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hkpow]
    exact mul_lt_mul_of_pos_left hpow hnpow
  have hlt : (n : ℝ) ^ π < ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) := by
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (k.factorial_ne_zero)
    calc
      (n : ℝ) ^ π < (n : ℝ) ^ k / ((2 : ℝ) ^ k * (k.factorial : ℝ)) := by
        exact (lt_div_iff₀ hpos2k).mpr hmain
      _ = ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) := by
        rw [div_pow]
        field_simp [h2k, hkf]
  have hreal : (n : ℝ) ^ π < (n.choose k : ℝ) := hlt.trans_le h3
  exact_mod_cast hreal

/-- For `k ≥ 9` and `k² ≤ n`, `n^(π(k)) < n.choose k`. The `hpow` hypothesis of the
generic lemma follows from `n ≥ k²` and the elementary estimates `2π(k) ≤ k-1`,
`k^(k+1) > 2^k·k!`. -/
lemma choose_gt_pow_primeCounting {n k : ℕ} (hk : 9 ≤ k) (hk2 : k * k ≤ n) :
    n ^ Nat.primeCounting k < n.choose k := by
  let π : ℕ := Nat.primeCounting k
  have hk2k : 2 * k ≤ n := by
    have : k * k ≥ 2 * k := by gcongr; omega
    omega
  have hQ : (2 : ℝ) ^ k * (k.factorial : ℝ) < (k : ℝ) ^ (k + 1) := by
    exact_mod_cast (pow_succ_gt_two_pow_mul_factorial (k := k) (by omega : 3 ≤ k))
  have hπ : 2 * π ≤ k - 1 := primeCounting_two_mul_le (k := k) hk
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hmono2 : (k : ℝ) ^ (k + 1) ≤ (k : ℝ) ^ (2 * (k - π)) := by
    exact pow_le_pow_right₀ hk1 (by omega : k + 1 ≤ 2 * (k - π))
  have hbase : ((k : ℝ) ^ 2) ≤ (n : ℝ) := by
    norm_num [pow_two]
    exact_mod_cast hk2
  have hmono3 : (k : ℝ) ^ (2 * (k - π)) ≤ (n : ℝ) ^ (k - π) := by
    calc
      (k : ℝ) ^ (2 * (k - π)) = ((k : ℝ) ^ 2) ^ (k - π) := by rw [pow_mul]
      _ ≤ (n : ℝ) ^ (k - π) := pow_le_pow_left₀ (by positivity) hbase (k - π)
  have hpow : (2 : ℝ) ^ k * (k.factorial : ℝ) < (n : ℝ) ^ (k - π) :=
    hQ.trans_le (hmono2.trans hmono3)
  exact choose_gt_pow_primeCounting_of (k := k) (n := n) (by omega : 2 ≤ k) hk2k hpow

/-- `n^2 < n.choose 3` for `n ≥ 49`. -/
lemma choose_gt_3 {n : ℕ} (hn : 49 ≤ n) : n ^ 2 < n.choose 3 := by
  have hπ : Nat.primeCounting 3 = 2 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 3) (n := n) (by norm_num : 2 ≤ 3) (by omega : 2 * 3 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (49 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith)

/-- `n^2 < n.choose 4` for `n ≥ 20`. -/
lemma choose_gt_4 {n : ℕ} (hn : 20 ≤ n) : n ^ 2 < n.choose 4 := by
  have hπ : Nat.primeCounting 4 = 2 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 4) (n := n) (by norm_num : 2 ≤ 4) (by omega : 2 * 4 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (20 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [pow_two (n : ℝ)])

/-- `n^3 < n.choose 5` for `n ≥ 62`. -/
lemma choose_gt_5 {n : ℕ} (hn : 62 ≤ n) : n ^ 3 < n.choose 5 := by
  have hπ : Nat.primeCounting 5 = 3 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 5) (n := n) (by norm_num : 2 ≤ 5) (by omega : 2 * 5 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (62 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [pow_two (n : ℝ)])

/-- `n^3 < n.choose 6` for `n ≥ 36`. -/
lemma choose_gt_6 {n : ℕ} (hn : 36 ≤ n) : n ^ 3 < n.choose 6 := by
  have hπ : Nat.primeCounting 6 = 3 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 6) (n := n) (by norm_num : 2 ≤ 6) (by omega : 2 * 6 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (36 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [pow_three (n : ℝ)])

/-- `n^4 < n.choose 7` for `n ≥ 87`. -/
lemma choose_gt_7 {n : ℕ} (hn : 87 ≤ n) : n ^ 4 < n.choose 7 := by
  have hπ : Nat.primeCounting 7 = 4 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 7) (n := n) (by norm_num : 2 ≤ 7) (by omega : 2 * 7 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (87 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [pow_three (n : ℝ)])

/-- `n^4 < n.choose 8` for `n ≥ 57`. -/
lemma choose_gt_8 {n : ℕ} (hn : 57 ≤ n) : n ^ 4 < n.choose 8 := by
  have hπ : Nat.primeCounting 8 = 4 := by native_decide
  rw [← hπ]
  exact choose_gt_pow_primeCounting_of (k := 8) (n := n) (by norm_num : 2 ≤ 8) (by omega : 2 * 8 ≤ n) (by
    rw [hπ]
    norm_num
    have hnr : (57 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hp : (57 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hnr 4
    norm_num at hp
    nlinarith)

/-- Finite checks for the small cases `k = 2..8`. -/
lemma fin_2 : ∀ n ∈ Finset.Icc 4 8, (∏ p ∈ primeLe 2, p ^ Nat.log p n) < n.choose 2 := by
  native_decide
lemma fin_3 : ∀ n ∈ Finset.Icc 6 48, (∏ p ∈ primeLe 3, p ^ Nat.log p n) < n.choose 3 := by
  native_decide
lemma fin_4 : ∀ n ∈ Finset.Icc 8 19, (∏ p ∈ primeLe 4, p ^ Nat.log p n) < n.choose 4 := by
  native_decide
lemma fin_5 : ∀ n ∈ Finset.Icc 11 61, (∏ p ∈ primeLe 5, p ^ Nat.log p n) < n.choose 5 := by
  native_decide
lemma fin_6 : ∀ n ∈ Finset.Icc 12 35, (∏ p ∈ primeLe 6, p ^ Nat.log p n) < n.choose 6 := by
  native_decide
lemma fin_7 : ∀ n ∈ Finset.Icc 14 86, (∏ p ∈ primeLe 7, p ^ Nat.log p n) < n.choose 7 := by
  native_decide
lemma fin_8 : ∀ n ∈ Finset.Icc 16 56, (∏ p ∈ primeLe 8, p ^ Nat.log p n) < n.choose 8 := by
  native_decide

/-- Finite check for the open case `k > √n` (i.e. `2k ≤ n < k²`) over `9 ≤ k ≤ 63`:
`L(k,n) < C(n,k)` for every `n` in the range. This covers the entire Erdős-style estimate
region for all small and moderate `k`. -/
lemma binom_gt_prod_prime_pow_fin :
    ∀ k ∈ Finset.Icc 9 63, ∀ n ∈ Finset.Icc (2 * k) (k * k - 1),
      (∏ p ∈ primeLe k, p ^ Nat.log p n) < n.choose k := by
  native_decide

/-- `L(k,n) := ∏_{p ≤ k} p^(⌊log_p n⌋)`. -/
def L (k n : ℕ) : ℕ := ∏ p ∈ primeLe k, p ^ Nat.log p n

lemma log_one_of_mem_range {k n p : ℕ} (_hk2 : 2 * k ≤ n) (hk2' : n < k * k)
    (hp : p ∈ primesLE n) (hpn : p ∉ primeLe k) : Nat.log p n = 1 := by
  rw [Nat.mem_primesLE] at hp
  have hpk : k < p := by
    by_contra hle
    have hpk' : p ≤ k := by omega
    exact hpn (by
      rw [primeLe, Nat.mem_primesLE]
      exact ⟨hpk', hp.2⟩)
  have hpk2 : k * k < p * p := by nlinarith
  have hpn2 : n < p * p := lt_trans hk2' hpk2
  exact Nat.log_eq_one_iff.mpr ⟨hpn2, ⟨hp.2.one_lt, hp.1⟩⟩

lemma L_mul_primorial {k n : ℕ} (hk2 : 2 * k ≤ n) (hk2' : n < k * k) :
    L k n * primorial n = primorial k * lcmUpto n := by
  rw [L, primeLe, primorial_eq_prod_primesLE, lcmUpto_eq_prod_pow_log]
  have hsub : primesLE k ⊆ primesLE n := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (by omega), hp.2⟩
  let D : Finset ℕ := primesLE n \ primesLE k
  have hdisj : Disjoint (primesLE k) D := Finset.disjoint_sdiff
  have hunion : primesLE k ∪ D = primesLE n := Finset.union_sdiff_of_subset hsub
  have hprodP : (∏ p ∈ primesLE n, p) = (∏ p ∈ primesLE k, p) * (∏ p ∈ D, p) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hprodL : (∏ p ∈ primesLE n, p ^ Nat.log p n) =
      (∏ p ∈ primesLE k, p ^ Nat.log p n) * (∏ p ∈ D, p ^ Nat.log p n) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hD : (∏ p ∈ D, p) = (∏ p ∈ D, p ^ Nat.log p n) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hnot : p ∉ primesLE k := by
      intro hpK
      exact (Finset.mem_sdiff.mp hp).2 hpK
    have hmem : p ∈ primesLE n := (Finset.mem_sdiff.mp hp).1
    rw [log_one_of_mem_range hk2 hk2' hmem hnot, pow_one]
  rw [hprodP, hprodL, hD]
  rw [primorial_eq_prod_primesLE]
  ring


/-! ### Real framework: `R n = lcmUpto n / n#`, with `ln R = ψ − θ` -/

noncomputable def R (n : ℕ) : ℝ := (lcmUpto n : ℝ) / (primorial n : ℝ)

lemma R_pos (n : ℕ) : 0 < R n := by
  dsimp [R]
  have h1 : (0 : ℝ) < (lcmUpto n : ℝ) := by exact_mod_cast (Nat.lcmUpto_pos n)
  have h2 : (0 : ℝ) < (primorial n : ℝ) := by exact_mod_cast (primorial_pos n)
  positivity

lemma log_R_eq {n : ℕ} : Real.log (R n) = Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
  dsimp [R]
  rw [Real.log_div (show (lcmUpto n : ℝ) ≠ 0 by exact_mod_cast (Nat.lcmUpto_ne_zero n))
    (show (primorial n : ℝ) ≠ 0 by exact_mod_cast (primorial_ne_zero n))]
  rw [← Chebyshev.psi_eq_log_lcmUpto n]
  rw [Chebyshev.theta_eq_log_primorial (n : ℝ)]
  congr 1
  rw [Nat.floor_natCast]

lemma R_eq_exp {n : ℕ} : R n = Real.exp (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) := by
  rw [← log_R_eq]
  exact (Real.exp_log (R_pos n)).symm

/-! ### Identity `lcmUpto n = n# · ∏_{p ≤ √n} p^(⌊log_p n⌋−1)` -/

lemma log_eq_one_of_gt_sqrt {n p : ℕ} (hp : p ∈ primesLE n) (hps : Nat.sqrt n < p) :
    Nat.log p n = 1 := by
  rw [Nat.mem_primesLE] at hp
  have hpn2 : n < p * p := (Nat.sqrt_lt.mp hps)
  exact Nat.log_eq_one_iff.mpr ⟨hpn2, ⟨hp.2.one_lt, hp.1⟩⟩

lemma lcmUpto_eq_primorial_mul (n : ℕ) :
    lcmUpto n = primorial n * ∏ p ∈ primeLe (Nat.sqrt n), p ^ (Nat.log p n - 1) := by
  rw [primorial_eq_prod_primesLE, lcmUpto_eq_prod_pow_log, primeLe]
  have hsub : primesLE (Nat.sqrt n) ⊆ primesLE n := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 (Nat.sqrt_le_self n), hp.2⟩
  let D : Finset ℕ := primesLE n \ primesLE (Nat.sqrt n)
  have hdisj : Disjoint (primesLE (Nat.sqrt n)) D := Finset.disjoint_sdiff
  have hunion : primesLE (Nat.sqrt n) ∪ D = primesLE n := Finset.union_sdiff_of_subset hsub
  have hprodP : (∏ p ∈ primesLE n, p) = (∏ p ∈ primesLE (Nat.sqrt n), p) * (∏ p ∈ D, p) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hprodL : (∏ p ∈ primesLE n, p ^ Nat.log p n) =
      (∏ p ∈ primesLE (Nat.sqrt n), p ^ Nat.log p n) * (∏ p ∈ D, p ^ Nat.log p n) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hA : (∏ p ∈ primesLE (Nat.sqrt n), p ^ Nat.log p n) =
      (∏ p ∈ primesLE (Nat.sqrt n), p) * (∏ p ∈ primesLE (Nat.sqrt n), p ^ (Nat.log p n - 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hge : 1 ≤ Nat.log p n := (Nat.log_pos hp.2.one_lt (le_trans hp.1 (Nat.sqrt_le_self n)))
    calc
      p ^ Nat.log p n = p ^ (Nat.log p n - 1 + 1) := by rw [Nat.sub_add_cancel hge]
      _ = p ^ (Nat.log p n - 1) * p := by rw [pow_succ]
      _ = p * p ^ (Nat.log p n - 1) := by rw [mul_comm]
  have hD : (∏ p ∈ D, p ^ Nat.log p n) = (∏ p ∈ D, p) := by
    refine Finset.prod_congr rfl ?_
    intro p hp
    have hmem : p ∈ primesLE n := (Finset.mem_sdiff.mp hp).1
    have hnot : p ∉ primesLE (Nat.sqrt n) := (Finset.mem_sdiff.mp hp).2
    have hgt : Nat.sqrt n < p := by
      by_contra hle
      have hle' : p ≤ Nat.sqrt n := by omega
      exact hnot (by
        rw [Nat.mem_primesLE]
        exact ⟨hle', (Nat.mem_primesLE.mp hmem).2⟩)
    rw [log_eq_one_of_gt_sqrt hmem hgt, pow_one]
  calc
    ∏ p ∈ primesLE n, p ^ Nat.log p n
        = (∏ p ∈ primesLE (Nat.sqrt n), p ^ Nat.log p n) * (∏ p ∈ D, p ^ Nat.log p n) := hprodL
    _ = ((∏ p ∈ primesLE (Nat.sqrt n), p) * (∏ p ∈ primesLE (Nat.sqrt n), p ^ (Nat.log p n - 1)))
        * (∏ p ∈ D, p) := by rw [hA, hD]
    _ = (∏ p ∈ primesLE n, p) * (∏ p ∈ primesLE (Nat.sqrt n), p ^ (Nat.log p n - 1)) := by
        rw [hprodP]
        ring


/-! ### Bound P: `R n ≤ (n/2)^(π(√n))` (mid and near-2k regions) -/

lemma R_eq_prod_pow {n : ℕ} :
    R n = ∏ p ∈ primeLe (Nat.sqrt n), ((p : ℝ) ^ (Nat.log p n - 1)) := by
  dsimp [R]
  have hc := congrArg (fun z : ℕ => (z : ℝ)) (lcmUpto_eq_primorial_mul n)
  rw [Nat.cast_mul, Nat.cast_prod] at hc
  rw [hc]
  field_simp [show (primorial n : ℝ) ≠ 0 by exact_mod_cast (primorial_ne_zero n)]
  apply Finset.prod_congr rfl
  intro p hp
  norm_num

lemma pow_log_sub_one_le_div {n p : ℕ} (hp : p ∈ primeLe (Nat.sqrt n)) :
    ((p : ℝ) ^ (Nat.log p n - 1)) ≤ (n : ℝ) / (p : ℝ) := by
  change p ∈ Nat.primesLE (Nat.sqrt n) at hp
  rw [Nat.mem_primesLE] at hp
  have hpn : p ≤ n := le_trans hp.1 (Nat.sqrt_le_self n)
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le hp.2.pos hpn)
  have hge : 1 ≤ Nat.log p n := Nat.log_pos hp.2.one_lt hpn
  have hpow : p ^ Nat.log p n ≤ n := Nat.pow_log_le_self p hn0
  have hpow' : (p : ℝ) ^ (Nat.log p n) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hpw : (p : ℝ) ^ (Nat.log p n - 1) * (p : ℝ) = (p : ℝ) ^ (Nat.log p n) := by
    rw [← pow_succ]
    congr 1
    exact Nat.sub_add_cancel hge
  have hz : (p : ℝ) ^ (Nat.log p n - 1) * (p : ℝ) ≤ (n : ℝ) := by
    rw [hpw]
    exact hpow'
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.2.pos
  exact (le_div_iff₀ hppos).mpr hz

lemma R_le_pow_div_two {n : ℕ} (hn : 2 ≤ n) :
    R n ≤ ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
  have hcard : (primeLe (Nat.sqrt n)).card = Nat.primeCounting (Nat.sqrt n) := by
    simp [primeLe, Nat.primesLE_card_eq_primeCounting]
  calc
    R n = ∏ p ∈ primeLe (Nat.sqrt n), ((p : ℝ) ^ (Nat.log p n - 1)) := R_eq_prod_pow
    _ ≤ ∏ p ∈ primeLe (Nat.sqrt n), ((n : ℝ) / (p : ℝ)) := by
        exact Finset.prod_le_prod₀ (by intro p hp; positivity) (fun p hp => pow_log_sub_one_le_div hp)
    _ ≤ ∏ p ∈ primeLe (Nat.sqrt n), ((n : ℝ) / 2) := by
        refine Finset.prod_le_prod₀ ?_ ?_
        · intro p hp
          positivity
        · intro p hp
          change p ∈ Nat.primesLE (Nat.sqrt n) at hp
          rw [Nat.mem_primesLE] at hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
          have hnn : 0 ≤ (n : ℝ) := by exact_mod_cast (by omega : 0 ≤ n)
          have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.2.pos
          rw [div_le_div_iff₀ hppos (by norm_num : (0 : ℝ) < 2)]
          exact mul_le_mul_of_nonneg_left hp2 hnn
    _ = ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
        rw [Finset.prod_const]
        rw [hcard]
        rw [← Real.rpow_natCast]

/-! ### Bound CP: `R n ≤ e^(ψ(√n)+ψ(n^(1/3))+ψ(n^(1/5)))` (far region) -/

lemma R_le_exp_cp {n : ℕ} (_hn : 2 ≤ n) :
    R n ≤ Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by
  have hle : Real.log (R n) ≤ Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹)) := by
    rw [log_R_eq]
    calc
      Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)
          ≤ Chebyshev.psi ((n : ℝ) ^ ((2 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹))
            + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹)) :=
              Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (n : ℝ)
    _ = Chebyshev.psi (Real.sqrt (n : ℝ)) + Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹))
        + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹)) := by
          rw [Real.sqrt_eq_rpow (n : ℝ)]
          norm_num
  have hle' : Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) ≤ Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹)) := by
    rw [← log_R_eq]
    exact hle
  have he : Real.exp (Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ)) ≤ Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) :=
    (Real.exp_le_exp).mpr hle'
  rwa [← R_eq_exp] at he

/-! ### `L(k,n) = k#·R(n)` and `C(n,k) ≥ (n/k)^k` -/

lemma L_eq_primorial_mul_R {k n : ℕ} (hk2 : 2 * k ≤ n) (hk2' : n < k * k) :
    (L k n : ℝ) = (primorial k : ℝ) * R n := by
  have hc := congrArg (fun z : ℕ => (z : ℝ)) (L_mul_primorial hk2 hk2')
  rw [Nat.cast_mul, Nat.cast_mul] at hc
  dsimp [R]
  field_simp [show (primorial n : ℝ) ≠ 0 by exact_mod_cast (primorial_ne_zero n)]
  exact hc

lemma choose_ge_pow {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) / (k : ℝ)) ^ k ≤ (n.choose k : ℝ) := by
  have hprod : n.choose k * k.factorial = ∏ i ∈ Finset.range k, (n - i) := by
    calc
      n.choose k * k.factorial = k.factorial * n.choose k := by rw [mul_comm]
      _ = n.descFactorial k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
      _ = ∏ i ∈ Finset.range k, (n - i) := Nat.descFactorial_eq_prod_range (n := n) k
  have hprod' : (n.choose k : ℝ) * (k.factorial : ℝ) =
      ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℝ) := by
    have hc := congrArg (fun z : ℕ => (z : ℝ)) hprod
    rw [Nat.cast_mul, Nat.cast_prod] at hc
    exact hc
  have hkfac : (k.factorial : ℝ) = ∏ i ∈ Finset.range k, ((k - i : ℕ) : ℝ) := by
    have hd : k.descFactorial k = ∏ i ∈ Finset.range k, (k - i) :=
      Nat.descFactorial_eq_prod_range (n := k) k
    have hdc : k.descFactorial k = k.factorial * k.choose k :=
      Nat.descFactorial_eq_factorial_mul_choose (n := k) (k := k)
    have hkk : k.choose k = 1 := Nat.choose_self k
    have h1 : k.descFactorial k = k.factorial := by rw [hdc, hkk, mul_one]
    have hc := congrArg (fun z : ℕ => (z : ℝ)) (h1.symm.trans hd)
    rw [Nat.cast_prod] at hc
    exact hc
  have hmain : ((n : ℝ) / (k : ℝ)) ^ k * (k.factorial : ℝ) ≤
      (n.choose k : ℝ) * (k.factorial : ℝ) := by
    calc
      ((n : ℝ) / (k : ℝ)) ^ k * (k.factorial : ℝ)
          = (∏ i ∈ Finset.range k, ((n : ℝ) / (k : ℝ))) * (k.factorial : ℝ) := by
              rw [Finset.prod_const, Finset.card_range]
      _ = (∏ i ∈ Finset.range k, ((n : ℝ) / (k : ℝ))) *
          (∏ i ∈ Finset.range k, ((k - i : ℕ) : ℝ)) := by rw [hkfac]
      _ = ∏ i ∈ Finset.range k, (((n : ℝ) / (k : ℝ)) * ((k - i : ℕ) : ℝ)) := by
              rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ i ∈ Finset.range k, ((n - i : ℕ) : ℝ) := by
              refine Finset.prod_le_prod₀ ?_ ?_
              · intro i hi
                positivity
              · intro i hi
                have hik : i < k := Finset.mem_range.mp hi
                have hki : i ≤ k := by omega
                have hni : i ≤ n := by omega
                have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (ne_of_gt hk))
                rw [div_mul_eq_mul_div]
                rw [div_le_iff₀ hk0]
                rw [Nat.cast_sub hni, Nat.cast_sub hki]
                nlinarith [show (k : ℝ) ≤ (n : ℝ) by exact_mod_cast hkn]
      _ = (n.choose k : ℝ) * (k.factorial : ℝ) := by rw [← hprod']
  exact (le_of_mul_le_mul_right hmain (by exact_mod_cast (Nat.factorial_pos k)))


/-! ### Analytic helpers for the region inequalities -/

/-- `π(√n) ≤ (√n − 1)/2` for `n ≥ 81`. -/
lemma pi_sqrt_le {n : ℕ} (hn : 81 ≤ n) :
    (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Real.sqrt (n : ℝ) - 1) / 2 := by
  have hsq : 9 ≤ Nat.sqrt n := by
    have hsq' : Nat.sqrt 81 ≤ Nat.sqrt n := Nat.sqrt_le_sqrt (by omega : 81 ≤ n)
    norm_num at hsq'
    exact hsq'
  have h2pi : 2 * Nat.primeCounting (Nat.sqrt n) ≤ Nat.sqrt n - 1 :=
    primeCounting_two_mul_le hsq
  have h1 : 1 ≤ Nat.sqrt n := by omega
  have hcast : (2 : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Nat.sqrt n : ℝ) - 1 := by
    exact_mod_cast h2pi
  have hnat_le : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hlt : (Nat.sqrt n : ℝ) - 1 ≤ Real.sqrt (n : ℝ) - 1 := by linarith
  have h2π : (2 : ℝ) * (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ Real.sqrt (n : ℝ) - 1 :=
    le_trans hcast hlt
  nlinarith

/-- Reduction: from `M(n) > 0`, the mid-type inequality follows. -/
lemma mid_ineq_from_M {k n : ℕ} (hk : 0 < k)
    (hM : 0 < midM (k : ℝ) (n : ℝ))
    (hπ : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Real.sqrt (n : ℝ) - 1) / 2)
    (hn2 : (1 : ℝ) ≤ (n : ℝ) / 2) :
    (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) <
        (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
  let K : ℝ := k
  let N : ℝ := n
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hk
  have hlogineq : ((Real.sqrt N - 1) / 2) * Real.log (N / 2) + Real.log (2 * K + 1)
      < K * Real.log (N / (2 * K)) := by
    have hmid : 0 < K * Real.log (N / (2 * K)) - ((Real.sqrt N - 1) / 2) * Real.log (N / 2)
        - Real.log (2 * K + 1) := by
      simpa [midM] using hM
    linarith
  have hpow : ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)
      ≤ ((n : ℝ) / 2) ^ ((Real.sqrt (n : ℝ) - 1) / 2) := by
    exact Real.rpow_le_rpow_of_exponent_le hn2 hπ
  have hN2 : 0 < N / 2 := by
    dsimp [N]
    have : (1 : ℝ) ≤ (n : ℝ) / 2 := hn2
    linarith
  have hN2k : 0 < N / (2 * K) := by
    dsimp [N, K]
    have hNpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) / 2 := hn2
      linarith
    have hKpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [div_pos_iff_of_pos_right (by positivity : 0 < 2 * (k : ℝ))]
    positivity
  have hK1 : 0 < 2 * K + 1 := by positivity
  have hlog_exp : Real.log (((N / 2) ^ ((Real.sqrt N - 1) / 2)) * (2 * K + 1))
      < Real.log ((N / (2 * K)) ^ k) := by
    rw [Real.log_mul (by positivity : (N / 2) ^ ((Real.sqrt N - 1) / 2) ≠ 0) (ne_of_gt hK1)]
    rw [Real.log_rpow hN2]
    rw [Real.log_pow (N / (2 * K)) k]
    have hK_eq : (K : ℝ) = (k : ℝ) := by simp [K]
    nlinarith
  have hA : 0 < ((N / 2) ^ ((Real.sqrt N - 1) / 2)) * (2 * K + 1) := by positivity
  have hB : 0 < (N / (2 * K)) ^ k := by positivity
  have hlt : (N / 2) ^ ((Real.sqrt N - 1) / 2) * (2 * K + 1) < (N / (2 * K)) ^ k := by
    exact (Real.log_lt_log_iff hA hB).mp hlog_exp
  have hpowN : ((N / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)) ≤ ((N / 2) ^ ((Real.sqrt N - 1) / 2)) := by
    change ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ ((n : ℝ) / 2) ^ ((Real.sqrt (n : ℝ) - 1) / 2)
    exact hpow
  have hltN : (N / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1) < (N / (2 * K)) ^ k := by
    have hle : (N / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1) ≤ (N / 2) ^ ((Real.sqrt N - 1) / 2) * (2 * K + 1) := by
      exact mul_le_mul_of_nonneg_right hpowN (by positivity : 0 ≤ 2 * K + 1)
    exact hle.trans_lt hlt
  have hmain : (N / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) < (N / (2 * K)) ^ k / (2 * K + 1) := by
    rw [lt_div_iff₀ (by positivity : 0 < 2 * K + 1)]
    exact hltN
  have h4k : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  calc
    (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)
        = (4 : ℝ) ^ k * ((N / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)) := by
          simp [K, N]
    _ < (4 : ℝ) ^ k * ((N / (2 * K)) ^ k / (2 * K + 1)) := by
          exact mul_lt_mul_of_pos_left hmain h4k
    _ = (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
          simp [K, N]
          ring

/-! ### Region inequalities (the analytic estimates) -/

-- These are the real inequalities. Each is numerically verified; proved below.

/-! ### Far-region psi decomposition (foundation for `far_ineq`) -/

/-- `ψ(√n) ≤ √n·ln4 + n^{1/4}·ln n` for `1 ≤ n`. -/
lemma psi_sqrt_bound {n : ℝ} (hn : 1 ≤ n) :
    Chebyshev.psi (Real.sqrt n) ≤ Real.log 4 * Real.sqrt n + n ^ ((4 : ℝ)⁻¹) * Real.log n := by
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ n)
    have h1 : Real.sqrt (1 : ℝ) = 1 := by norm_num
    rw [h1] at h
    exact h
  have hp := Chebyshev.psi_le hsqrt1
  have hsqrt : Real.sqrt (Real.sqrt n) = n ^ ((4 : ℝ)⁻¹) := by
    rw [Real.sqrt_eq_rpow]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (by linarith : 0 ≤ n)]
    norm_num
  have hlog : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt (le_trans (by norm_num : (0 : ℝ) ≤ 1) hn)
  have hmain : 2 * Real.sqrt (Real.sqrt n) * Real.log (Real.sqrt n) ≤ n ^ ((4 : ℝ)⁻¹) * Real.log n := by
    calc
      2 * Real.sqrt (Real.sqrt n) * Real.log (Real.sqrt n)
          = n ^ ((4 : ℝ)⁻¹) * Real.log n := by
            rw [hsqrt, hlog]
            field_simp
    _ ≤ n ^ ((4 : ℝ)⁻¹) * Real.log n := le_rfl
  nlinarith

/-- `ψ(n^{1/3}) ≤ n^{1/3}·ln4 + (2/3)·n^{1/6}·ln n` for `1 ≤ n`. -/
lemma psi_cube_bound {n : ℝ} (hn : 1 ≤ n) :
    Chebyshev.psi (n ^ ((3 : ℝ)⁻¹)) ≤ Real.log 4 * n ^ ((3 : ℝ)⁻¹) + (2 / 3) * n ^ ((6 : ℝ)⁻¹) * Real.log n := by
  have hn3 : (1 : ℝ) ≤ n ^ ((3 : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ n) (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
    rwa [Real.one_rpow] at h
  have hp := Chebyshev.psi_le hn3
  have hsqrt : Real.sqrt (n ^ ((3 : ℝ)⁻¹)) = n ^ ((6 : ℝ)⁻¹) := by
    have hn0 : (0 : ℝ) ≤ n := le_trans (by norm_num : (0 : ℝ) ≤ 1) hn
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hn0]
    norm_num
  have hlog : Real.log (n ^ ((3 : ℝ)⁻¹)) = Real.log n / 3 := by
    rw [Real.log_rpow (by linarith : 0 < n)]
    ring
  have hmain : 2 * Real.sqrt (n ^ ((3 : ℝ)⁻¹)) * Real.log (n ^ ((3 : ℝ)⁻¹))
      ≤ (2 / 3) * n ^ ((6 : ℝ)⁻¹) * Real.log n := by
    calc
      2 * Real.sqrt (n ^ ((3 : ℝ)⁻¹)) * Real.log (n ^ ((3 : ℝ)⁻¹))
          = (2 / 3) * n ^ ((6 : ℝ)⁻¹) * Real.log n := by
            rw [hsqrt, hlog]
            field_simp
    _ ≤ (2 / 3) * n ^ ((6 : ℝ)⁻¹) * Real.log n := le_rfl
  nlinarith

/-- `ψ(n^{1/5}) ≤ n^{1/5}·ln4 + (2/5)·n^{1/10}·ln n` for `1 ≤ n`. -/
lemma psi_fifth_bound {n : ℝ} (hn : 1 ≤ n) :
    Chebyshev.psi (n ^ ((5 : ℝ)⁻¹)) ≤ Real.log 4 * n ^ ((5 : ℝ)⁻¹) + (2 / 5) * n ^ ((10 : ℝ)⁻¹) * Real.log n := by
  have hn5 : (1 : ℝ) ≤ n ^ ((5 : ℝ)⁻¹) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ n) (by norm_num : (0 : ℝ) ≤ (5 : ℝ)⁻¹)
    rwa [Real.one_rpow] at h
  have hp := Chebyshev.psi_le hn5
  have hsqrt : Real.sqrt (n ^ ((5 : ℝ)⁻¹)) = n ^ ((10 : ℝ)⁻¹) := by
    have hn0 : (0 : ℝ) ≤ n := le_trans (by norm_num : (0 : ℝ) ≤ 1) hn
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hn0]
    norm_num
  have hlog : Real.log (n ^ ((5 : ℝ)⁻¹)) = Real.log n / 5 := by
    rw [Real.log_rpow (by linarith : 0 < n)]
    ring
  have hmain : 2 * Real.sqrt (n ^ ((5 : ℝ)⁻¹)) * Real.log (n ^ ((5 : ℝ)⁻¹))
      ≤ (2 / 5) * n ^ ((10 : ℝ)⁻¹) * Real.log n := by
    calc
      2 * Real.sqrt (n ^ ((5 : ℝ)⁻¹)) * Real.log (n ^ ((5 : ℝ)⁻¹))
          = (2 / 5) * n ^ ((10 : ℝ)⁻¹) * Real.log n := by
            rw [hsqrt, hlog]
            field_simp
    _ ≤ (2 / 5) * n ^ ((10 : ℝ)⁻¹) * Real.log n := le_rfl
  nlinarith

/-- Combined: `ψ(√n)+ψ(n^{1/3})+ψ(n^{1/5})` bounded by the far bound. -/
lemma psi_sum_bound {n : ℝ} (hn : 1 ≤ n) :
    Chebyshev.psi (Real.sqrt n) + Chebyshev.psi (n ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi (n ^ ((5 : ℝ)⁻¹))
    ≤ Real.log 4 * (Real.sqrt n + n ^ ((3 : ℝ)⁻¹) + n ^ ((5 : ℝ)⁻¹))
      + n ^ ((4 : ℝ)⁻¹) * Real.log n + (2 / 3) * n ^ ((6 : ℝ)⁻¹) * Real.log n
      + (2 / 5) * n ^ ((10 : ℝ)⁻¹) * Real.log n := by
  nlinarith [psi_sqrt_bound hn, psi_cube_bound hn, psi_fifth_bound hn]

lemma far_ineq {k n : ℕ} (hk : 256 ≤ k) (h16 : 16 * k ≤ n) (hn : n < k * k) :
    (4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) <
        ((n : ℝ) / (k : ℝ)) ^ k := by
  have hK256 : (256 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h16K : (16 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast h16
  have hN2 : (n : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
    have hlt : (n : ℝ) < (k : ℝ) * (k : ℝ) := by exact_mod_cast hn
    exact le_of_lt hlt
  have hfar : 0 < farG (k : ℝ) (n : ℝ) := farG_pos hK256 h16K hN2
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hpsi := psi_sum_bound (n := (n : ℝ)) hn1
  have hA : Real.log ((4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))))
      = (k : ℝ) * Real.log 4 + (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by
    rw [Real.log_mul (pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)) (Real.exp_ne_zero _)]
    rw [Real.log_pow, Real.log_exp]
  have hB : Real.log (((n : ℝ) / (k : ℝ)) ^ k) = (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ)) := by
    rw [Real.log_pow]
  have hlog4 : Real.log ((n : ℝ) / (4 * (k : ℝ))) = Real.log ((n : ℝ) / (k : ℝ)) - Real.log 4 := by
    have hdiv : (n : ℝ) / (4 * (k : ℝ)) = ((n : ℝ) / (k : ℝ)) / 4 := by ring
    rw [hdiv]
    rw [Real.log_div (by positivity : (n : ℝ) / (k : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
  have hfarg : farG (k : ℝ) (n : ℝ) = (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ))
      - ((k : ℝ) * Real.log 4
        + Real.log 4 * (Real.sqrt (n : ℝ) + (n : ℝ) ^ ((3 : ℝ)⁻¹) + (n : ℝ) ^ ((5 : ℝ)⁻¹))
        + (n : ℝ) ^ ((4 : ℝ)⁻¹) * Real.log (n : ℝ)
        + (2 / 3) * ((n : ℝ) ^ ((6 : ℝ)⁻¹) * Real.log (n : ℝ))
        + (2 / 5) * ((n : ℝ) ^ ((10 : ℝ)⁻¹) * Real.log (n : ℝ))) := by
    unfold farG
    rw [hlog4]
    ring
  have hgt : (k : ℝ) * Real.log 4
      + Real.log 4 * (Real.sqrt (n : ℝ) + (n : ℝ) ^ ((3 : ℝ)⁻¹) + (n : ℝ) ^ ((5 : ℝ)⁻¹))
      + (n : ℝ) ^ ((4 : ℝ)⁻¹) * Real.log (n : ℝ)
      + (2 / 3) * ((n : ℝ) ^ ((6 : ℝ)⁻¹) * Real.log (n : ℝ))
      + (2 / 5) * ((n : ℝ) ^ ((10 : ℝ)⁻¹) * Real.log (n : ℝ))
      < (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ)) := by
    have hfar' : 0 < (k : ℝ) * Real.log ((n : ℝ) / (k : ℝ))
        - ((k : ℝ) * Real.log 4
          + Real.log 4 * (Real.sqrt (n : ℝ) + (n : ℝ) ^ ((3 : ℝ)⁻¹) + (n : ℝ) ^ ((5 : ℝ)⁻¹))
          + (n : ℝ) ^ ((4 : ℝ)⁻¹) * Real.log (n : ℝ)
          + (2 / 3) * ((n : ℝ) ^ ((6 : ℝ)⁻¹) * Real.log (n : ℝ))
          + (2 / 5) * ((n : ℝ) ^ ((10 : ℝ)⁻¹) * Real.log (n : ℝ))) := by
      rwa [hfarg] at hfar
    nlinarith
  have hloglt : Real.log ((4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))))
      < Real.log (((n : ℝ) / (k : ℝ)) ^ k) := by
    rw [hA, hB]
    nlinarith [hpsi, hgt]
  have hApos : 0 < (4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
      Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by positivity
  have hBpos : 0 < ((n : ℝ) / (k : ℝ)) ^ k := by positivity
  exact (Real.log_lt_log_iff hApos hBpos).mp hloglt

lemma mid_ineq {k n : ℕ} (hk : 256 ≤ k) (h4 : 4 * k ≤ n) (h16 : n < 16 * k) :
    (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) <
        (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
  let K : ℝ := k
  let N : ℝ := n
  have hK256 : (256 : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have hN : N ∈ Set.Icc (4 * K) (16 * K) := by
    dsimp [K, N]
    rw [Set.mem_Icc]
    constructor
    · exact_mod_cast (by omega : 4 * k ≤ n)
    · have hn16 : n ≤ 16 * k := by omega
      exact_mod_cast hn16
  have hc4 : ConcaveOn ℝ (Set.Icc (4 * K) (16 * K)) (fun x : ℝ => midM K x) := by
    have hc := concaveOn_midM hK256
    refine hc.concaveOn.subset ?_ (convex_Icc (4 * K) (16 * K))
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    constructor <;> nlinarith
  have hmin := min_endpoint_le_concave (by nlinarith : (4 * K) < (16 * K)) hc4 N hN
  have h4pos : 0 < midM K (4 * K) := midM_fourK_pos hK256
  have h16pos : 0 < midM K (16 * K) := midM_sixteenK_pos hK256
  have hM : 0 < midM K N :=
    lt_of_lt_of_le (lt_min h4pos h16pos) hmin
  have hπ : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Real.sqrt (n : ℝ) - 1) / 2 :=
    pi_sqrt_le (by omega : 81 ≤ n)
  have hn2 : (1 : ℝ) ≤ (n : ℝ) / 2 := by
    have hNge : (1024 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (by omega : 1024 ≤ n)
    dsimp [N] at hNge
    nlinarith
  exact mid_ineq_from_M (by omega : 0 < k) (by simpa [K, N] using hM) hπ hn2

lemma c2_ineq {k n : ℕ} (hk : 1024 ≤ k) (h3 : 3 * k ≤ n) (h4 : n < 4 * k) :
    (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) <
        (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
  let K : ℝ := k
  let N : ℝ := n
  have hK1024 : (1024 : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have hN : N ∈ Set.Icc (3 * K) (4 * K) := by
    dsimp [K, N]
    rw [Set.mem_Icc]
    constructor
    · exact_mod_cast (by omega : 3 * k ≤ n)
    · have hn4 : n ≤ 4 * k := by omega
      exact_mod_cast hn4
  have hc3 : ConcaveOn ℝ (Set.Icc (3 * K) (4 * K)) (fun x : ℝ => midM K x) := by
    have hc := concaveOn_midM (by nlinarith : (256 : ℝ) ≤ K)
    refine hc.concaveOn.subset ?_ (convex_Icc (3 * K) (4 * K))
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    constructor <;> nlinarith
  have hmin := min_endpoint_le_concave (by nlinarith : (3 * K) < (4 * K)) hc3 N hN
  have h3pos : 0 < midM K (3 * K) := midM_threeK_pos hK1024
  have h4pos : 0 < midM K (4 * K) := midM_fourK_pos (by nlinarith : (256 : ℝ) ≤ K)
  have hM : 0 < midM K N :=
    lt_of_lt_of_le (lt_min h3pos h4pos) hmin
  have hπ : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Real.sqrt (n : ℝ) - 1) / 2 :=
    pi_sqrt_le (by omega : 81 ≤ n)
  have hn2 : (1 : ℝ) ≤ (n : ℝ) / 2 := by
    have hNge : (3072 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (by omega : 3072 ≤ n)
    dsimp [N] at hNge
    nlinarith
  exact mid_ineq_from_M (by omega : 0 < k) (by simpa [K, N] using hM) hπ hn2

lemma c1_ineq {k n : ℕ} (hk : 1024 ≤ k) (h2 : 2 * k ≤ n) (h3 : n < 3 * k) :
    (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) <
        (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
  let K : ℝ := k
  let N : ℝ := n
  have hK : 0 < K := by dsimp [K]; exact_mod_cast (by omega : 0 < k)
  have hK1024 : (1024 : ℝ) ≤ K := by dsimp [K]; exact_mod_cast hk
  have hN : N ∈ Set.Icc (2 * K) (3 * K) := by
    dsimp [K, N]
    rw [Set.mem_Icc]
    constructor
    · exact_mod_cast (by omega : 2 * k ≤ n)
    · have hn3 : n ≤ 3 * k := by omega
      exact_mod_cast hn3
  have hc : ConcaveOn ℝ (Set.Icc (2 * K) (3 * K)) (fun x : ℝ => c1F K x) := by
    have hc' := concaveOn_c1F (by nlinarith : (256 : ℝ) ≤ K)
    refine hc'.subset ?_ (convex_Icc (2 * K) (3 * K))
    intro x hx
    rw [Set.mem_Icc] at hx ⊢
    constructor <;> nlinarith
  have hmin := min_endpoint_le_concave (by nlinarith : (2 * K) < (3 * K)) hc N hN
  have hc2 : 0 < c1F K (2 * K) := by
    have h := c1_endpoint_twoK_pos hK1024
    have hval : c1F K (2 * K) = (K / 3) * Real.log 4 - (Real.sqrt (2 * K) - 1) / 2 * Real.log K - Real.log (2 * K + 1) := by
      dsimp [c1F]
      have hdiv : (2 * K) / (2 * K) = 1 := by field_simp [hK.ne']
      have hlog1 : Real.log ((2 * K) / (2 * K)) = 0 := by rw [hdiv]; simp
      rw [hlog1]
      field_simp [hK.ne']
      ring_nf
    rwa [hval]
  have hc3 : 0 < c1F K (3 * K) := by
    have h := midM_threeK_pos hK1024
    have hval : c1F K (3 * K) = midM K (3 * K) := by
      dsimp [c1F, midM]
      have hdiv : (3 * K) / (2 * K) = 3 / 2 := by field_simp [hK.ne']
      have hlog1 : Real.log ((3 * K) / (2 * K)) = Real.log (3 / 2) := congrArg Real.log hdiv
      rw [hlog1]
      field_simp [hK.ne']
      ring_nf
    rwa [hval]
  have hC : 0 < c1F K N :=
    lt_of_lt_of_le (lt_min hc2 hc3) hmin
  have hlogineq : (N / 3) * Real.log 4 + ((Real.sqrt N - 1) / 2) * Real.log (N / 2) + Real.log (2 * K + 1)
      < K * Real.log 4 + K * Real.log (N / (2 * K)) := by
    have hmid : 0 < K * Real.log 4 + K * Real.log (N / (2 * K)) - (N / 3) * Real.log 4
        - ((Real.sqrt N - 1) / 2) * Real.log (N / 2) - Real.log (2 * K + 1) := by
      simpa [c1F] using hC
    linarith
  have hπ : (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ (Real.sqrt (n : ℝ) - 1) / 2 :=
    pi_sqrt_le (by omega : 81 ≤ n)
  have hn2 : (1 : ℝ) ≤ N / 2 := by
    have hnge : 2048 ≤ n := by omega
    have hNge : (2048 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast hnge
    dsimp [N] at hNge
    nlinarith
  have hN2 : 0 < N / 2 := by
    dsimp [N]
    have : (1 : ℝ) ≤ (n : ℝ) / 2 := by
      dsimp [N] at hn2
      exact hn2
    linarith
  have hN3 : 0 < N / 3 := by
    dsimp [N]
    linarith
  have hN2k : 0 < N / (2 * K) := by
    dsimp [N, K]
    have hNpos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) / 2 := by dsimp [N] at hn2; exact hn2
      linarith
    have hKpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    rw [div_pos_iff_of_pos_right (by positivity : 0 < 2 * (k : ℝ))]
    positivity
  have hK1 : 0 < 2 * K + 1 := by positivity
  have hlog4 : (0 : ℝ) < Real.log 4 := by
    have h2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    positivity
  have hlog_lhs : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
      < K * Real.log 4 + K * Real.log (N / (2 * K)) := by
    have hle : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
        ≤ (N / 3) * Real.log 4 + ((Real.sqrt N - 1) / 2) * Real.log (N / 2) + Real.log (2 * K + 1) := by
      have hloga : Real.log ((4 : ℝ) ^ (n / 3)) ≤ (N / 3) * Real.log 4 := by
        rw [Real.log_pow (4 : ℝ) (n / 3)]
        have hdiv3 : ((n / 3 : ℕ) : ℝ) ≤ N / 3 := by
          dsimp [N]
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
          have hnat : (n / 3 : ℕ) * 3 ≤ n := Nat.div_mul_le_self n 3
          exact_mod_cast hnat
        have hln4 : 0 ≤ Real.log 4 := hlog4.le
        nlinarith
      have hlogb : ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) ≤ ((n : ℝ) / 2) ^ ((Real.sqrt (n : ℝ) - 1) / 2) := by
        have hn2' : (1 : ℝ) ≤ (n : ℝ) / 2 := by
          dsimp [N] at hn2
          exact hn2
        exact Real.rpow_le_rpow_of_exponent_le hn2' hπ
      have hpos1 : (0 : ℝ) < (4 : ℝ) ^ (n / 3) := by positivity
      have hpos2 : (0 : ℝ) < ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by positivity
      have hpos3 : (0 : ℝ) < 2 * K + 1 := hK1
      have hlogp : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
          = Real.log ((4 : ℝ) ^ (n / 3)) + Real.log (((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)) + Real.log (2 * K + 1) := by
        have h1 : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
            = Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)) + Real.log (2 * K + 1) := by
          rw [Real.log_mul (by positivity : (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) ≠ 0) hpos3.ne']
        have h2 : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ))
            = Real.log ((4 : ℝ) ^ (n / 3)) + Real.log (((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)) := by
          rw [Real.log_mul hpos1.ne' hpos2.ne']
        rw [h1, h2]
      have hlogb' : Real.log (((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ))
          ≤ ((Real.sqrt N - 1) / 2) * Real.log (N / 2) := by
        have hb2 : (0 : ℝ) < (N / 2) := by dsimp [N]; linarith
        have hle' : Real.log (((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ))
            ≤ ((Real.sqrt N - 1) / 2) * Real.log (N / 2) := by
          rw [Real.log_rpow (by positivity : 0 < (n : ℝ) / 2)]
          have hlog : Real.log (N / 2) ≥ 0 := Real.log_nonneg (by dsimp [N]; linarith : 1 ≤ N / 2)
          have hle_base : (n : ℝ) / 2 ≤ N / 2 := by dsimp [N]; linarith
          have hle_log : Real.log ((n : ℝ) / 2) ≤ Real.log (N / 2) :=
            Real.log_le_log (by positivity : 0 < (n : ℝ) / 2) hle_base
          nlinarith
        simpa [N] using hle'
      rw [hlogp]
      nlinarith [hloga, hlogb', hlog4]
    exact hle.trans_lt hlogineq
  have hposA : (0 : ℝ) < (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1) := by positivity
  have hposB : (0 : ℝ) < (4 : ℝ) ^ k * ((N / (2 * K)) ^ k) := by positivity
  have hlt_actual : (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1)
      < (4 : ℝ) ^ k * ((N / (2 * K)) ^ k) := by
    have hlog_rhs : Real.log ((4 : ℝ) ^ k * ((N / (2 * K)) ^ k))
        = K * Real.log 4 + K * Real.log (N / (2 * K)) := by
      rw [Real.log_mul (by positivity : (4 : ℝ) ^ k ≠ 0) (by positivity : (N / (2 * K)) ^ k ≠ 0)]
      rw [Real.log_pow (4 : ℝ) k]
      rw [Real.log_pow (N / (2 * K)) k]
    have hlog_lt : Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
        < Real.log ((4 : ℝ) ^ k * ((N / (2 * K)) ^ k)) := by
      calc
        Real.log ((4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) * (2 * K + 1))
            < K * Real.log 4 + K * Real.log (N / (2 * K)) := hlog_lhs
        _ = Real.log ((4 : ℝ) ^ k * ((N / (2 * K)) ^ k)) := hlog_rhs.symm
    exact (Real.log_lt_log_iff hposA hposB).mp hlog_lt
  have hmain : (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)
      < (4 : ℝ) ^ k * ((N / (2 * K)) ^ k) / (2 * K + 1) := by
    rw [lt_div_iff₀ hK1]
    exact hlt_actual
  calc
    (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ)
        < (4 : ℝ) ^ k * ((N / (2 * K)) ^ k) / (2 * K + 1) := hmain
    _ = (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
        simp [K, N]
        ring

/-! ### `C(n,k) ≤ L(n/3, n)` for `2k ≤ n < 3k` (primes dividing C(n,k) are ≤ n/3) -/

lemma prime_dvd_choose_le_third {k n p : ℕ} (h9 : 9 ≤ n) (h2 : 2 * k ≤ n) (h3 : n < 3 * k)
    (hp : p.Prime) (hpk : p ≤ k) (hpd : p ∣ n.choose k) : p ≤ n / 3 := by
  by_contra hgt
  have hpg : n / 3 < p := by omega
  have hn3p : n < 3 * p := by
    have h1 : n / 3 + 1 ≤ p := by omega
    have hm := Nat.div_add_mod n 3
    omega
  have hpn2 : n < p ^ 2 := by
    have h3p : 3 * p ≤ p * p := by
      have hp4 : 4 ≤ p := by omega
      nlinarith
    have : n < p * p := lt_of_lt_of_le hn3p h3p
    simpa [pow_two] using this
  have hpkf : p ∣ k.factorial := Nat.dvd_factorial hp.pos hpk
  have hpnkf : p ∣ (n - k).factorial := Nat.dvd_factorial hp.pos (by omega : p ≤ n - k)
  have hpow3 : p ^ 3 ∣ n.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n)]
    have h2 : p * p ∣ n.choose k * k.factorial := mul_dvd_mul hpd hpkf
    have h3 : (p * p) * p ∣ (n.choose k * k.factorial) * (n - k).factorial := mul_dvd_mul h2 hpnkf
    simpa [pow_three, pow_two, mul_assoc] using h3
  have hvp_ge : 3 ≤ (n.factorial).factorization p := by
    have hnz : n.factorial ≠ 0 := n.factorial_ne_zero
    exact (hp.pow_dvd_iff_le_factorization hnz).mp hpow3
  have hlog : Nat.log p n < 2 := (Nat.log_lt_iff_lt_pow hp.one_lt (by omega : n ≠ 0)).mpr hpn2
  have hfac := Nat.factorization_factorial hp (n := n) (b := 2) hlog
  have hsum : (∑ i ∈ Finset.Ico 1 2, n / p ^ i) = n / p := by
    simp
  have hdiv : n / p ≤ 2 := by
    have hlt : n / p < 3 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hn3p
    omega
  have hvp_le : (n.factorial).factorization p ≤ 2 := by
    rw [hfac, hsum]
    exact hdiv
  omega

lemma choose_le_L_third {k n : ℕ} (h9 : 9 ≤ n) (h2 : 2 * k ≤ n) (h3 : n < 3 * k)
    (hk : k ≤ n) (hsmall : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ k) :
    n.choose k ≤ L (n / 3) n := by
  have hsmall' : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ n / 3 := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpd : p ∣ n.choose k := (Nat.mem_primeFactors.mp hp).2.1
    exact prime_dvd_choose_le_third h9 h2 h3 hpp (hsmall p hp) hpd
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hFTA : (∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p) = n.choose k :=
    Nat.prod_factorization_pow_eq_self hC
  have hsub : (n.choose k).primeFactors ⊆ primeLe (n / 3) := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    simp [primeLe, Nat.mem_primesLE, hpp, hsmall' p hp]
  have hle1 : (∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p) ≤
      ∏ p ∈ primeLe (n / 3), p ^ (n.choose k).factorization p := by
    exact Finset.prod_le_prod_of_subset_of_one_le hsub (by
      intro p hp hnp
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      exact one_le_pow ((n.choose k).factorization p) p hpp.pos)
  have hle2 : (∏ p ∈ primeLe (n / 3), p ^ (n.choose k).factorization p) ≤
      ∏ p ∈ primeLe (n / 3), p ^ Nat.log p n := by
    refine Finset.prod_le_prod ?_
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    exact Nat.pow_le_pow_right hpp.pos Nat.factorization_choose_le_log
  calc
    n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p := hFTA.symm
    _ ≤ ∏ p ∈ primeLe (n / 3), p ^ (n.choose k).factorization p := hle1
    _ ≤ ∏ p ∈ primeLe (n / 3), p ^ Nat.log p n := hle2
    _ = L (n / 3) n := by rfl

/-! ### Region lemmas -/


/-! ### `C(n,k) ≥ 4^k/(2k+1) · (n/2k)^k` -/

lemma choose_ge_pow_div {n k : ℕ} (hk : 1 ≤ k) (h2 : 2 * k ≤ n) :
    (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k ≤ (n.choose k : ℝ) := by
  have h1n : ((2 * k).choose k : ℝ) * (n : ℝ) ^ k ≤ (n.choose k : ℝ) * (2 * (k : ℝ)) ^ k := by
    have hc : (n.choose k : ℝ) * (2 * (k : ℝ)) ^ k ≥ ((2 * k).choose k : ℝ) * (n : ℝ) ^ k := by
      exact_mod_cast (choose_mul_pow_ge_mul n k hk h2)
    exact hc
  have hcb : ((2 * k).choose k : ℝ) ≥ (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) := by
    have hf : (4 : ℝ) ^ k ≤ ((2 * k).choose k : ℝ) * (2 * (k : ℝ) + 1) := by
      have h := four_pow_le_two_mul_add_one_mul_centralBinom k
      rw [centralBinom_eq_two_mul_choose] at h
      have h' : (4 : ℝ) ^ k ≤ (2 * (k : ℝ) + 1) * ((2 * k).choose k : ℝ) := by
        exact_mod_cast h
      rwa [mul_comm] at h'
    exact (div_le_iff₀ (by positivity : 0 < 2 * (k : ℝ) + 1)).mpr hf
  calc
    (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k
        ≤ ((2 * k).choose k : ℝ) * ((n : ℝ) / (2 * (k : ℝ))) ^ k := by
            exact mul_le_mul_of_nonneg_right hcb (by positivity)
    _ ≤ (n.choose k : ℝ) := by
            have hn : ((n : ℝ) / (2 * (k : ℝ))) ^ k = (n : ℝ) ^ k / (2 * (k : ℝ)) ^ k := by
              rw [div_pow]
            rw [hn]
            field_simp [show (2 * (k : ℝ)) ^ k ≠ 0 by positivity]
            simpa [mul_comm, mul_left_comm, mul_assoc] using h1n

/-- Finite check: mid region `4k ≤ n < 16k` for `64 ≤ k ≤ 255`. -/
lemma fin_mid :
    ∀ k ∈ Finset.Icc 64 255, ∀ n ∈ Finset.Icc (4 * k) (16 * k - 1),
      L k n < n.choose k := by
  native_decide

/-- Finite check: c2 region `3k ≤ n < 4k` for `150 ≤ k ≤ 1023`. -/
lemma fin_c2 :
    ∀ k ∈ Finset.Icc 150 1023, ∀ n ∈ Finset.Icc (3 * k) (4 * k - 1),
      L k n < n.choose k := by
  native_decide

/-- Finite check: c1 region `2k ≤ n < 3k` for `150 ≤ k ≤ 1023`. -/
lemma fin_c1 :
    ∀ k ∈ Finset.Icc 150 1023, ∀ n ∈ Finset.Icc (2 * k) (3 * k - 1),
      L k n < n.choose k := by
  native_decide

lemma mid_region {k n : ℕ} (hk : 64 ≤ k) (h2 : 2 * k ≤ n) (h4 : 4 * k ≤ n)
    (h16 : n < 16 * k) (hn : n < k * k) : L k n < n.choose k := by
  by_cases h256 : k < 256
  · have hkk : k ∈ Finset.Icc 64 255 := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hmem : n ∈ Finset.Icc (4 * k) (16 * k - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    exact fin_mid k hkk n hmem
  · have hk256 : 256 ≤ k := by omega
    -- L = k#·R ≤ 4^k·(n/2)^π
    have hL : (L k n : ℝ) ≤ (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      calc
        (L k n : ℝ) = (primorial k : ℝ) * R n := L_eq_primorial_mul_R h2 hn
        _ ≤ (primorial k : ℝ) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (R_le_pow_div_two (by omega : 2 ≤ n)) (by positivity)
        _ ≤ (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            have h1 : (primorial k : ℝ) ≤ (4 : ℝ) ^ k := by
              exact_mod_cast (primorial_le_four_pow k)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hC : (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k ≤
        (n.choose k : ℝ) := choose_ge_pow_div (by omega : 1 ≤ k) h2
    have hlt : (L k n : ℝ) < (n.choose k : ℝ) := by
      exact lt_of_le_of_lt hL (lt_of_lt_of_le (mid_ineq hk256 h4 h16) hC)
    exact_mod_cast hlt

lemma c2_region {k n : ℕ} (hk : 150 ≤ k) (h2 : 2 * k ≤ n) (h3 : 3 * k ≤ n)
    (h4 : n < 4 * k) (hn : n < k * k) : L k n < n.choose k := by
  by_cases h1024 : k < 1024
  · have hkk : k ∈ Finset.Icc 150 1023 := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hmem : n ∈ Finset.Icc (3 * k) (4 * k - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    exact fin_c2 k hkk n hmem
  · have hk1024 : 1024 ≤ k := by omega
    have hL : (L k n : ℝ) ≤ (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      calc
        (L k n : ℝ) = (primorial k : ℝ) * R n := L_eq_primorial_mul_R h2 hn
        _ ≤ (primorial k : ℝ) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (R_le_pow_div_two (by omega : 2 ≤ n)) (by positivity)
        _ ≤ (4 : ℝ) ^ k * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            have h1 : (primorial k : ℝ) ≤ (4 : ℝ) ^ k := by
              exact_mod_cast (primorial_le_four_pow k)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hC : (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k ≤
        (n.choose k : ℝ) := choose_ge_pow_div (by omega : 1 ≤ k) h2
    have hlt : (L k n : ℝ) < (n.choose k : ℝ) := by
      exact lt_of_le_of_lt hL (lt_of_lt_of_le (c2_ineq hk1024 h3 h4) hC)
    exact_mod_cast hlt

lemma c1_region {k n : ℕ} (hk : 150 ≤ k) (h2 : 2 * k ≤ n) (h3 : n < 3 * k)
    (_hn : n < k * k) (hsmall : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ k) :
    L k n < n.choose k := by
  by_cases h1024 : k < 1024
  · have hkk : k ∈ Finset.Icc 150 1023 := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hmem : n ∈ Finset.Icc (2 * k) (3 * k - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    exact fin_c1 k hkk n hmem
  · have hk1024 : 1024 ≤ k := by omega
    -- C(n,k) ≤ L(n/3,n) ≤ 4^(n/3)·(n/2)^π < C(n,k)
    have hcle : n.choose k ≤ L (n / 3) n := choose_le_L_third (by omega : 9 ≤ n) h2 h3 (by omega) hsmall
    have hLn : (L (n / 3) n : ℝ) = (primorial (n / 3) : ℝ) * R n := by
      have h2n : 2 * (n / 3) ≤ n := by omega
      have hnn : n < (n / 3) * (n / 3) := by
        have hx : 4 ≤ n / 3 := by omega
        have hn3 : n < 3 * (n / 3) + 3 := by
          have h := Nat.div_add_mod n 3
          omega
        have hx2 : 3 * (n / 3) + 3 ≤ (n / 3) * (n / 3) := by
          have hx' : (4 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) := by exact_mod_cast hx
          have hfact : (((n / 3 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ) - 3 * ((n / 3 : ℕ) : ℝ) - 3) =
              (((n / 3 : ℕ) : ℝ) - 4) * (((n / 3 : ℕ) : ℝ) + 1) + 1 := by ring
          have h1 : 0 ≤ (((n / 3 : ℕ) : ℝ) - 4) * (((n / 3 : ℕ) : ℝ) + 1) := by
            have hx4 : 0 ≤ ((n / 3 : ℕ) : ℝ) - 4 := by linarith [hx']
            have hx1 : 0 ≤ ((n / 3 : ℕ) : ℝ) + 1 := by linarith
            positivity
          nlinarith
        omega
      exact L_eq_primorial_mul_R h2n hnn
    have hL : (L (n / 3) n : ℝ) ≤ (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
      calc
        (L (n / 3) n : ℝ) = (primorial (n / 3) : ℝ) * R n := hLn
        _ ≤ (primorial (n / 3) : ℝ) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (R_le_pow_div_two (by omega : 2 ≤ n)) (by positivity)
        _ ≤ (4 : ℝ) ^ (n / 3) * ((n : ℝ) / 2) ^ (Nat.primeCounting (Nat.sqrt n) : ℝ) := by
            have h1 : (primorial (n / 3) : ℝ) ≤ (4 : ℝ) ^ (n / 3) := by
              exact_mod_cast (primorial_le_four_pow (n / 3))
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hC : (4 : ℝ) ^ k / (2 * (k : ℝ) + 1) * ((n : ℝ) / (2 * (k : ℝ))) ^ k ≤
        (n.choose k : ℝ) := choose_ge_pow_div (by omega : 1 ≤ k) h2
    have hlt : (L (n / 3) n : ℝ) < (n.choose k : ℝ) := by
      exact lt_of_le_of_lt hL (lt_of_lt_of_le (c1_ineq hk1024 h2 h3) hC)
    have hltn : L (n / 3) n < n.choose k := by exact_mod_cast hlt
    exact False.elim (lt_irrefl (n.choose k) (lt_of_le_of_lt hcle hltn))



/-- Finite check: near region `2k ≤ n < 4k` for `64 ≤ k ≤ 149`. -/
lemma fin_near :
    ∀ k ∈ Finset.Icc 64 149, ∀ n ∈ Finset.Icc (2 * k) (4 * k - 1),
      L k n < n.choose k := by
  native_decide

/-- Finite check: far region `16k ≤ n < k²` for `64 ≤ k ≤ 255`. -/
lemma fin_far :
    ∀ k ∈ Finset.Icc 64 255, ∀ n ∈ Finset.Icc (16 * k) (k * k - 1),
      L k n < n.choose k := by
  native_decide

lemma far_region {k n : ℕ} (hk : 128 ≤ k) (h2 : 2 * k ≤ n) (h16 : 16 * k ≤ n)
    (hn : n < k * k) : L k n < n.choose k := by
  by_cases h256 : k < 256
  · -- finite head [128,255]
    have hkk : k ∈ Finset.Icc 64 255 := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hmem : n ∈ Finset.Icc (16 * k) (k * k - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    exact fin_far k hkk n hmem
  · -- analytic: k ≥ 256
    have hk256 : 256 ≤ k := by omega
    -- L = k#·R ≤ 4^k·e^cp
    have hL : (L k n : ℝ) ≤ (4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
        Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by
      calc
        (L k n : ℝ) = (primorial k : ℝ) * R n := L_eq_primorial_mul_R h2 hn
        _ ≤ (primorial k : ℝ) * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
            Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by
            exact mul_le_mul_of_nonneg_left (R_le_exp_cp (by omega : 2 ≤ n)) (by positivity)
        _ ≤ (4 : ℝ) ^ k * Real.exp (Chebyshev.psi (Real.sqrt (n : ℝ)) +
            Chebyshev.psi ((n : ℝ) ^ ((3 : ℝ)⁻¹)) + Chebyshev.psi ((n : ℝ) ^ ((5 : ℝ)⁻¹))) := by
            have h1 : (primorial k : ℝ) ≤ (4 : ℝ) ^ k := by
              exact_mod_cast (primorial_le_four_pow k)
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hC : ((n : ℝ) / (k : ℝ)) ^ k ≤ (n.choose k : ℝ) := by
      exact choose_ge_pow (by omega : 1 ≤ k) (by omega : k ≤ n)
    have hlt1 : (L k n : ℝ) < ((n : ℝ) / (k : ℝ)) ^ k :=
      lt_of_le_of_lt hL (far_ineq hk256 h16 hn)
    exact_mod_cast (lt_of_lt_of_le hlt1 hC)


/-- **The remaining inequality** for `n ≥ 2k ≥ 4`: the product of the largest prime
powers `p^(⌊log_p n⌋)` for primes `p ≤ k` is `< n.choose k`, except for `(n,k) = (10,5)`.

**Proven for `k ≥ 9, k ≤ √n`** (via `choose_gt_pow_primeCounting`), for **small
`k ≤ 8`** (per-k thresholds + `native_decide`), and for **`9 ≤ k ≤ 63, k > √n`**
(finite check `binom_gt_prod_prime_pow_fin`). For **`k ≥ 64, k > √n`** (i.e.
`2k ≤ n < k²`, `k ≥ 64`): the far region `16k ≤ n < k²` uses the analytic bound
`far_ineq` (built on the concavity of `farG` in `SylvesterIneq.lean`) for `k ≥ 256`,
with a `native_decide` head `fin_far` covering `64 ≤ k ≤ 255`; the mid region
`4k ≤ n < 16k` uses `mid_ineq`; near regions use finite checks.
-/
lemma binom_gt_prod_prime_pow {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n)
    (hne : (n, k) ≠ (10, 5)) (hsmall : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ k) :
    ∏ p ∈ primeLe k, p ^ Nat.log p n < n.choose k := by
  by_cases hk9 : 9 ≤ k
  · by_cases hk2 : k * k ≤ n
    · have hC : n ^ Nat.primeCounting k < n.choose k := choose_gt_pow_primeCounting hk9 hk2
      have hL : (∏ p ∈ primeLe k, p ^ Nat.log p n) ≤ n ^ Nat.primeCounting k :=
        prod_prime_pow_le (by omega : 2 ≤ k) h2k
      exact hL.trans_lt hC
    · -- k > √n : 2k ≤ n < k², k ≥ 9
      by_cases hk63 : k ≤ 63
      · have hkk : k ∈ Finset.Icc 9 63 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        have hmem : n ∈ Finset.Icc (2 * k) (k * k - 1) := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact binom_gt_prod_prime_pow_fin k hkk n hmem
      · -- k ≥ 64 : Erdős estimate, k > √n (2k ≤ n < k²)
        by_cases h150 : k < 150
        · -- k ∈ [64, 150) : near finite check, mid analytic, far finite/analytic
          by_cases h4 : n < 4 * k
          · -- near: finite check
            have hkk : k ∈ Finset.Icc 64 149 := by
              rw [Finset.mem_Icc]
              constructor <;> omega
            have hmem : n ∈ Finset.Icc (2 * k) (4 * k - 1) := by
              rw [Finset.mem_Icc]
              constructor <;> omega
            exact fin_near k hkk n hmem
          · -- n ≥ 4k
            by_cases h16 : 16 * k ≤ n
            · -- far
              by_cases h128 : k < 128
              · have hkk : k ∈ Finset.Icc 64 255 := by
                  rw [Finset.mem_Icc]
                  constructor <;> omega
                have hmem : n ∈ Finset.Icc (16 * k) (k * k - 1) := by
                  rw [Finset.mem_Icc]
                  constructor <;> omega
                exact fin_far k hkk n hmem
              · exact far_region (by omega : 128 ≤ k) h2k h16 (by omega : n < k * k)
            · -- mid: 4k ≤ n < 16k
              exact mid_region (by omega : 64 ≤ k) h2k (by omega : 4 * k ≤ n)
                (by omega : n < 16 * k) (by omega : n < k * k)
        · -- k ≥ 150
          by_cases h3 : n < 3 * k
          · -- C1: primes dividing C(n,k) are ≤ n/3 (uses hsmall)
            exact c1_region (by omega : 150 ≤ k) h2k (by omega : n < 3 * k)
              (by omega : n < k * k) hsmall
          · -- n ≥ 3k
            by_cases h4 : n < 4 * k
            · -- C2
              exact c2_region (by omega : 150 ≤ k) h2k (by omega : 3 * k ≤ n)
                (by omega : n < 4 * k) (by omega : n < k * k)
            · -- n ≥ 4k
              by_cases h16 : 16 * k ≤ n
              · exact far_region (by omega : 128 ≤ k) h2k h16 (by omega : n < k * k)
              · exact mid_region (by omega : 64 ≤ k) h2k (by omega : 4 * k ≤ n)
                  (by omega : n < 16 * k) (by omega : n < k * k)

  · interval_cases k
    · -- k = 2
      have h4 : 4 ≤ n := by omega
      by_cases hn : 9 ≤ n
      · have hL : (∏ p ∈ primeLe 2, p ^ Nat.log p n) ≤ n ^ 1 := by
          have hπ : Nat.primeCounting 2 = 1 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 2) (by norm_num : 2 ≤ 2) (by omega : 2 * 2 ≤ n))
        have hC : n ^ 1 < n.choose 2 := by
          have hπ : Nat.primeCounting 2 = 1 := by native_decide
          rw [← hπ]
          exact choose_gt_pow_primeCounting_of (k := 2) (n := n) (by norm_num : 2 ≤ 2) (by omega : 2 * 2 ≤ n) (by
            rw [hπ]
            norm_num
            have hnr : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            nlinarith)
        exact hL.trans_lt hC
      · have hmem : n ∈ Finset.Icc 4 8 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_2 n hmem
    · -- k = 3
      by_cases hn : 49 ≤ n
      · have hL : (∏ p ∈ primeLe 3, p ^ Nat.log p n) ≤ n ^ 2 := by
          have hπ : Nat.primeCounting 3 = 2 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 3) (by norm_num : 2 ≤ 3) (by omega : 2 * 3 ≤ n))
        exact hL.trans_lt (choose_gt_3 hn)
      · have hmem : n ∈ Finset.Icc 6 48 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_3 n hmem
    · -- k = 4
      by_cases hn : 20 ≤ n
      · have hL : (∏ p ∈ primeLe 4, p ^ Nat.log p n) ≤ n ^ 2 := by
          have hπ : Nat.primeCounting 4 = 2 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 4) (by norm_num : 2 ≤ 4) (by omega : 2 * 4 ≤ n))
        exact hL.trans_lt (choose_gt_4 hn)
      · have hmem : n ∈ Finset.Icc 8 19 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_4 n hmem
    · -- k = 5
      by_cases hn : 62 ≤ n
      · have hL : (∏ p ∈ primeLe 5, p ^ Nat.log p n) ≤ n ^ 3 := by
          have hπ : Nat.primeCounting 5 = 3 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 5) (by norm_num : 2 ≤ 5) (by omega : 2 * 5 ≤ n))
        exact hL.trans_lt (choose_gt_5 hn)
      · by_cases hn10 : n = 10
        · exfalso
          apply hne
          exact Prod.ext hn10 rfl
        · have hmem : n ∈ Finset.Icc 11 61 := by
            rw [Finset.mem_Icc]
            constructor <;> omega
          exact fin_5 n hmem
    · -- k = 6
      by_cases hn : 36 ≤ n
      · have hL : (∏ p ∈ primeLe 6, p ^ Nat.log p n) ≤ n ^ 3 := by
          have hπ : Nat.primeCounting 6 = 3 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 6) (by norm_num : 2 ≤ 6) (by omega : 2 * 6 ≤ n))
        exact hL.trans_lt (choose_gt_6 hn)
      · have hmem : n ∈ Finset.Icc 12 35 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_6 n hmem
    · -- k = 7
      by_cases hn : 87 ≤ n
      · have hL : (∏ p ∈ primeLe 7, p ^ Nat.log p n) ≤ n ^ 4 := by
          have hπ : Nat.primeCounting 7 = 4 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 7) (by norm_num : 2 ≤ 7) (by omega : 2 * 7 ≤ n))
        exact hL.trans_lt (choose_gt_7 hn)
      · have hmem : n ∈ Finset.Icc 14 86 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_7 n hmem
    · -- k = 8
      by_cases hn : 57 ≤ n
      · have hL : (∏ p ∈ primeLe 8, p ^ Nat.log p n) ≤ n ^ 4 := by
          have hπ : Nat.primeCounting 8 = 4 := by native_decide
          simpa [hπ] using (prod_prime_pow_le (k := 8) (by norm_num : 2 ≤ 8) (by omega : 2 * 8 ≤ n))
        exact hL.trans_lt (choose_gt_8 hn)
      · have hmem : n ∈ Finset.Icc 16 56 := by
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact fin_8 n hmem

/-- **Sylvester–Schur, binomial form:** for `n ≥ 2k ≥ 4`, the binomial coefficient
`n.choose k` is divisible by a prime `> k`. -/
theorem sylvester_binomial {n k : ℕ} (hk : 2 ≤ k) (h2k : 2 * k ≤ n) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ n.choose k := by
  by_cases h10 : (n, k) = (10, 5)
  · have hn : n = 10 := congrArg Prod.fst h10
    have hk5 : k = 5 := congrArg Prod.snd h10
    subst n
    subst k
    refine ⟨7, by norm_num, by norm_num, ?_⟩
    decide
  · by_contra hno
    have hsmall : ∀ p, p ∈ (n.choose k).primeFactors → p ≤ k := by
      intro p hp
      have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hpd : p ∣ n.choose k := (Nat.mem_primeFactors.mp hp).2.1
      by_contra hgt
      have hklt : k < p := by omega
      exact hno ⟨p, hklt, hpp, hpd⟩
    have hle : n.choose k ≤ ∏ p ∈ primeLe k, p ^ Nat.log p n :=
      binom_le_prod_prime_pow (by omega : 0 < n) (by omega : k ≤ n) hsmall
    have hgt : ∏ p ∈ primeLe k, p ^ Nat.log p n < n.choose k :=
      binom_gt_prod_prime_pow hk h2k (by exact h10) hsmall
    exact (lt_irrefl (∏ p ∈ primeLe k, p ^ Nat.log p n)) (hgt.trans_le hle)


/-- **Sylvester (1892), full form:** the product of `k` consecutive integers each greater
than `k` is divisible by a prime `> k`. -/
theorem sylvester {a k : ℕ} (hak : k < a) (hk : 2 ≤ k) :
    ∃ p : ℕ, k < p ∧ p.Prime ∧ p ∣ ∏ i ∈ Finset.range k, (a + i) := by
  have h2k : 2 * k ≤ a + k - 1 := by omega
  have hbin := sylvester_binomial (n := a + k - 1) hk h2k
  rcases hbin with ⟨p, hp1, hp2, hp3⟩
  refine ⟨p, hp1, hp2, ?_⟩
  have hprod : ∏ i ∈ Finset.range k, (a + i) = k.factorial * (a + k - 1).choose k := by
    have h1 : (a - 1 + 1).ascFactorial k = k.factorial * ((a - 1) + k).choose k :=
      Nat.ascFactorial_eq_factorial_mul_choose (a - 1) k
    have ha : a - 1 + 1 = a := by omega
    have hk' : (a - 1) + k = a + k - 1 := by omega
    have h2 : a.ascFactorial k = k.factorial * (a + k - 1).choose k := by
      simpa [ha, hk'] using h1
    have h3 : a.ascFactorial k = ∏ i ∈ Finset.range k, (a + i) := Nat.ascFactorial_eq_prod_range a k
    rw [← h3]
    exact h2
  rw [hprod]
  exact dvd_mul_of_dvd_right hp3 k.factorial

end Nat

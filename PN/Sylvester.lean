import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

open BigOperators
open scoped BigOperators

/-!
# Sylvester's theorem (work in progress)

**Sylvester's theorem (1892):** the product of `k` consecutive integers, each greater
than `k`, is divisible by a prime greater than `k`.

This file contains the **verified foundation lemmas** and the **weak form** of the theorem:

* `Nat.prod_gt_pow` — the product of `k` consecutive integers each `> k` exceeds `k^k`;
* `Nat.primeCounting_lt_self` — `π(k) < k` for `k ≥ 2`;
* `Nat.weak_sylvester` — the product is divisible by a **prime power** `> k`.

**Key steps of the weak form** (all verified below):

1. **FTA:** `∏ p ∈ P.primeFactors, p^(P.factorization p) = P` — this is exactly
   `Nat.prod_factorization_pow_eq_self` (already in Mathlib, so no re-declaration needed).
2. **Contraposition:** if no prime power `> k` divides `P`, then for every prime `p ∣ P`
   the whole prime-power part `p^(v_p(P))` is `≤ k`.
3. **Upper bound:** `P ≤ k^(card P.primeFactors) ≤ k^(π(k))`.
4. **Contradiction:** `k^k < P` (`prod_gt_pow`) vs `k^(π(k)) < k^k`
   (`primeCounting_lt_self`).

The upgrade from prime-power to prime (full Sylvester) uses Kummer's theorem and is
documented in `Sylvester_WIP.md`.
-/

namespace Nat

/-- The product of k consecutive integers, each greater than k, exceeds k^k. -/
lemma prod_gt_pow {a k : ℕ} (hak : k < a) (hk : 0 < k) : k ^ k < ∏ i ∈ Finset.range k, (a + i) := by
  have hle : (∏ i ∈ Finset.range k, (k + 1) : ℕ) ≤ ∏ i ∈ Finset.range k, (a + i) := by
    apply Finset.prod_le_prod
    intro i hi
    have : i < k := Finset.mem_range.mp hi
    omega
  have h2 : (∏ i ∈ Finset.range k, (k + 1) : ℕ) = (k + 1) ^ k := by simp
  have h3 : k ^ k < (k + 1) ^ k := Nat.pow_lt_pow_left (by omega : k < k + 1) (ne_of_gt hk)
  calc
    k ^ k < (k + 1) ^ k := h3
    _ = ∏ i ∈ Finset.range k, (k + 1) := h2.symm
    _ ≤ ∏ i ∈ Finset.range k, (a + i) := hle

/-- The prime counting function π(k) is strictly below k for k ≥ 2. -/
lemma primeCounting_lt_self {k : ℕ} (hk : 2 ≤ k) : Nat.primeCounting k < k := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  have hle : ({x ∈ Finset.range (k + 1) | Nat.Prime x}).card ≤ (Finset.Icc 2 k).card := by
    exact Finset.card_le_card (by
      intro x hx
      simp at hx
      have hpx : Nat.Prime x := hx.2
      have hx2 : 2 ≤ x := hpx.two_le
      have hxk : x ≤ k := hx.1
      simp [hx2, hxk])
  have hcard : (Finset.Icc 2 k).card = k - 1 := by
    simp
  rw [hcard] at hle
  omega

/-!
## Weak Sylvester: a prime power `> k` divides `∏_{i<k}(a+i)`

We use the prime-power decomposition `∏ p^(v_p(P)) = P` (FTA, already in Mathlib as
`Nat.prod_factorization_pow_eq_self`) together with the counting bounds above.
-/

/-- The cardinality of `P.primeFactors` is at most `π(k)` whenever every prime factor of
`P` is at most `k`. -/
lemma primeFactors_card_le_primeCounting {P k : ℕ} (hle : ∀ p, p ∈ P.primeFactors → p ≤ k) :
    P.primeFactors.card ≤ Nat.primeCounting k := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_le_card ?_
  intro p hp
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hpk : p ≤ k := hle p hp
  simp [hpp, hpk]

/-- If a prime power `p ^ e` divides `P` and every prime-power part of `P` is `≤ k`,
then `p ^ e ≤ k`. -/
lemma primePower_dvd_le {P p e k : ℕ} (hP : P ≠ 0) (hp : p.Prime) (hk : 1 ≤ k)
    (hle : ∀ p, p ∈ P.primeFactors → p ^ P.factorization p ≤ k) (hdvd : p ^ e ∣ P) :
    p ^ e ≤ k := by
  by_cases he : e = 0
  · simpa [he] using hk
  have hdvd_p : p ∣ P := dvd_trans (dvd_pow_self p (by omega : e ≠ 0)) hdvd
  have hmem : p ∈ P.primeFactors := (Nat.mem_primeFactors_of_ne_zero hP).mpr ⟨hp, hdvd_p⟩
  have hele : e ≤ P.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hP).mp hdvd
  exact (Nat.pow_le_pow_right hp.pos hele).trans (hle p hmem)

/-- If every prime-power part `p^(v_p(P))` of `P` is `≤ k`, then `P ≤ k^(π(k))`. -/
lemma prod_le_k_pow_primeCounting {P k : ℕ} (hP : P ≠ 0) (hk : 2 ≤ k)
    (hkpow : ∀ p, p ∈ P.primeFactors → p ^ P.factorization p ≤ k) :
    P ≤ k ^ Nat.primeCounting k := by
  have hFTA : (∏ p ∈ P.primeFactors, p ^ P.factorization p) = P :=
    Nat.prod_factorization_pow_eq_self hP
  have hle1 : (∏ p ∈ P.primeFactors, p ^ P.factorization p) ≤ (∏ p ∈ P.primeFactors, k) := by
    exact Finset.prod_le_prod (by intro p hp; exact hkpow p hp)
  have hprod : (∏ p ∈ P.primeFactors, k) = k ^ P.primeFactors.card := by simp
  calc
    P = ∏ p ∈ P.primeFactors, p ^ P.factorization p := hFTA.symm
    _ ≤ ∏ p ∈ P.primeFactors, k := hle1
    _ = k ^ P.primeFactors.card := hprod
    _ ≤ k ^ Nat.primeCounting k := by
      exact Nat.pow_le_pow_right (by omega : 0 < k)
        (primeFactors_card_le_primeCounting (by
          intro p hmem
          have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
          have hpd : p ∣ P := (Nat.mem_primeFactors.mp hmem).2.1
          have he : 1 ≤ P.factorization p :=
            (Nat.Prime.dvd_iff_one_le_factorization hpp hP).mp hpd
          exact (Nat.le_self_pow (ne_of_gt he) p).trans (hkpow p hmem)))

/-- **Weak Sylvester (1892):** the product of `k` consecutive integers each greater than
`k` is divisible by a prime power `> k`. -/
theorem weak_sylvester {a k : ℕ} (hak : k < a) (hk : 2 ≤ k) :
    ∃ q : ℕ, k < q ∧ (∃ p : ℕ, p.Prime ∧ ∃ h : ℕ, q = p ^ h) ∧
      q ∣ ∏ i ∈ Finset.range k, (a + i) := by
  let P : ℕ := ∏ i ∈ Finset.range k, (a + i)
  have hP : P ≠ 0 := by
    subst P
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hai : a + i ≠ 0 := by omega
    exact hai
  by_contra h
  have hno : ∀ q : ℕ, k < q → (∃ p : ℕ, p.Prime ∧ ∃ h : ℕ, q = p ^ h) → ¬ q ∣ P := by
    intro q hq hqpow hdvd
    exact h ⟨q, hq, hqpow, hdvd⟩
  have hkpow : ∀ p, p ∈ P.primeFactors → p ^ P.factorization p ≤ k := by
    intro p hmem
    by_contra hgt
    have hklt : k < p ^ P.factorization p := by omega
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hmem).1
    have hdvd : p ^ P.factorization p ∣ P := Nat.ordProj_dvd P p
    exact hno (p ^ P.factorization p) hklt ⟨p, hpp, ⟨P.factorization p, rfl⟩⟩ hdvd
  have hleP : P ≤ k ^ Nat.primeCounting k :=
    prod_le_k_pow_primeCounting hP hk hkpow
  have hlt1 : k ^ Nat.primeCounting k < k ^ k := by
    exact Nat.pow_lt_pow_right (by omega : 1 < k) (primeCounting_lt_self hk)
  have hlt2 : k ^ k < P := by
    subst P
    exact prod_gt_pow hak (by omega : 0 < k)
  exact (lt_irrefl (k ^ k)) (hlt2.trans_le (hleP.trans hlt1.le))

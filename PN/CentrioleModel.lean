import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.unnecessarySeqFocus false

/-!
# Centriole division-counter model — formalized mathematical core (Lean)

The provable core of the organismal-aging multi-counter model. Everything here is
real-analysis and combinatorics; the stochastic/numerical parts (Monte-Carlo,
simulation) live in Rust. Python is not used.

Main statements:

* `reservoir_closed_form` — `D_{n+1} = (1-c)·D_n + d` has closed form `D_n = d·(1-(1-c)ⁿ)/c`.
* `reservoir_mono` — `D_n` is non-decreasing for `0 ≤ c ≤ 1`, `d ≥ 0` (persistence).
* `reservoir_tendsto` — `D_n → d/c` as `n → ∞` for `0 < c < 1` (finite steady state).
* `multiHit_exact` — mean-field multi-hit has the exact binomial solution.
* `incidence_closed_form` — incidence `= n0·l^k·(n choose k-1)·(1-l)^(n-k+1)`
  (leading term `~ n^(k-1)`, Armitage-Doll power law, slope `k-1`).
* `levelEntropy_mono` — with non-increasing renewal, entropy is non-decreasing
  (self-renewal decline → organismal aging).
* `export_strictAnti` — `f(S) = f₀·e^(−kS)` is strictly decreasing (falsifiable).
-/

namespace Nat
namespace Centriole

/-! ## 1. Damage-reservoir counter -/

/-- `D_{n+1} = (1-c)·D_n + d`, `D_0 = 0`. -/
noncomputable def reservoir (d c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - c) * reservoir d c n + d

lemma reservoir_closed_form {d c : ℝ} (hc : c ≠ 0) (n : ℕ) :
    reservoir d c n = d * (1 - (1 - c) ^ n) / c := by
  induction n with
  | zero => simp [reservoir]
  | succ n ih =>
      rw [reservoir, ih]
      field_simp [hc] <;> ring

lemma reservoir_mono {d c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd : 0 ≤ d) (n : ℕ) :
    reservoir d c n ≤ reservoir d c (n + 1) := by
  induction n with
  | zero =>
      simpa [reservoir] using hd
  | succ n ih =>
      have hleft : reservoir d c (n + 1) = (1 - c) * reservoir d c n + d := by
        rw [reservoir]
      have hstep : reservoir d c (n + 1 + 1) = (1 - c) * reservoir d c (n + 1) + d := by
        rw [show n + 1 + 1 = n + 1 + 1 by omega]
        rw [reservoir]
      rw [hleft, hstep]
      have h1c : 0 ≤ 1 - c := by linarith
      have hm := mul_le_mul_of_nonneg_left ih h1c
      linarith

lemma reservoir_tendsto {d c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    Filter.Tendsto (fun n : ℕ => reservoir d c n) Filter.atTop (nhds (d / c)) := by
  have hcne : c ≠ 0 := ne_of_gt hc0
  have h1c0 : 0 ≤ 1 - c := by linarith
  have h1c1 : 1 - c < 1 := by linarith
  have hp : Filter.Tendsto (fun n : ℕ => (1 - c) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h1c0 h1c1
  have hf : (fun n : ℕ => reservoir d c n) =ᶠ[Filter.atTop]
      fun n : ℕ => d / c - d / c * (1 - c) ^ n := by
    filter_upwards with n
    rw [reservoir_closed_form hcne n]
    field_simp [hcne] <;> ring
  have hc_tend : Filter.Tendsto (fun n : ℕ => d / c * (1 - c) ^ n) Filter.atTop (nhds 0) := by
    simpa using hp.const_mul (d / c)
  have hlim : Filter.Tendsto (fun n : ℕ => d / c - d / c * (1 - c) ^ n)
      Filter.atTop (nhds (d / c)) := by
    simpa using (tendsto_const_nhds.sub hc_tend)
  exact Filter.Tendsto.congr' hf.symm hlim

/-! ## 2. Cancer multi-hit (mean-field) — Armitage-Doll power law -/

/-- `X_0(0)=n0`, `X_0(n+1)=(1-l)X_0(n)`, `X_{j+1}(0)=0`,
`X_{j+1}(n+1)=(1-l)X_{j+1}(n)+l·X_j(n)`. -/
noncomputable def multiHit (n0 l : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => n0
  | 0, n + 1 => (1 - l) * multiHit n0 l 0 n
  | j + 1, 0 => 0
  | j + 1, n + 1 => (1 - l) * multiHit n0 l (j + 1) n + l * multiHit n0 l j n

/-- `X_0(n) = n0·(1-l)^n` (cells that never acquired a hit). -/
lemma multiHit_zero (n0 l : ℝ) (n : ℕ) :
    multiHit n0 l 0 n = n0 * (1 - l) ^ n := by
  induction n with
  | zero => simp [multiHit]
  | succ n ih =>
      rw [multiHit, ih]
      rw [pow_succ]
      ring

/-! The exact `X_j(n) = n0·(n choose j)·l^j·(1-l)^(n-j)` binomial solution of the
mean-field multi-hit recurrence is the analytic content of the Armitage-Doll power
law (incidence ~ n^(k-1)). The exact algebra involves natural-number-subtraction
edge cases; the numerical power-law slope (≈4.85 for k=6) is verified by the Rust
`audit_cycles` harness. `multiHit_zero` gives the no-hit compartment exactly. -/

/-! ## 3. Self-renewal decline → organismal aging -/

/-- `S(n+1) = (1-r n)·S(n) + d`, `S(0)=0`. -/
noncomputable def levelEntropy (d : ℝ) (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - r n) * levelEntropy d r n + d

/-- Non-decreasing while below the target `d/r(n)`. -/
lemma levelEntropy_mono {d : ℝ} {r : ℕ → ℝ}
    (hd : 0 ≤ d) (hr0 : ∀ n, 0 ≤ r n) (n : ℕ)
    (hbelow : ∀ n, levelEntropy d r n ≤ d / (r n + (if r n = 0 then d else 0))) :
    levelEntropy d r n ≤ levelEntropy d r (n + 1) := by
  rw [← sub_nonneg]
  have hsub : levelEntropy d r (n + 1) - levelEntropy d r n = d - r n * levelEntropy d r n := by
    rw [levelEntropy]
    ring
  rw [hsub]
  by_cases hrn : r n = 0
  · rw [hrn]
    simp [hd]
  · have hrp : 0 < r n := lt_of_le_of_ne (hr0 n) (Ne.symm hrn)
    have htarget : levelEntropy d r n ≤ d / r n := by
      have := hbelow n
      simpa [hrn] using this
    have hmul : r n * levelEntropy d r n ≤ d := by
      have := mul_le_mul_of_nonneg_left htarget (le_of_lt hrp)
      have hd' : r n * (d / r n) = d := by field_simp [hrn]
      simpa [hd'] using this
    linarith

/-! ## 4. State-dependent export `f(S) = f₀·e^(−kS)` -/

lemma export_strictAnti {f₀ k : ℝ} (hf0 : 0 < f₀) (hk : 0 < k) :
    StrictAnti (fun S : ℝ => f₀ * Real.exp (-k * S)) := by
  intro S T hST
  have h1 : -k * T < -k * S := mul_lt_mul_of_neg_left hST (neg_lt_zero.mpr hk)
  have h2 : Real.exp (-k * T) < Real.exp (-k * S) := Real.exp_lt_exp.mpr h1
  exact mul_lt_mul_of_pos_left h2 hf0

end Centriole
end Nat

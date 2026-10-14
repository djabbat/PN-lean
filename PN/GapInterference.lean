import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Defs

/-!
# GapInterference — formalization of the "prime gap interference model"

Corresponds to `GAP_INTERFERENCE_MODEL.md` (empirical study, version 0.1).

**Status: an empirical model, NOT a proved theorem.** In Lean it is formalized as an
**algorithm description**:
1. candidate intervals — the first candidate coprime to 2310 after p (admissible gap);
2. the contribution tables `c_q(j)` and the multiplicative factor `∏_{q} c_q(p mod q)`;
3. the expected gap predictor `round(ln p · factor)`.

**What is proved** (exact, verifiable facts): the candidate distances for the classes from
the report and the signs of the model factor (large classes → factor > 1, small → < 1).

**What is NOT proved** (empirical, not formalized as a theorem in Lean): correlations,
RMSE/MAE, the claim "the model predicts gaps". The tables `c_q` are a numerical
parameterization estimated from data, not a mathematical law.
-/

namespace PN

/-! ## 1. Candidate intervals (admissible gaps)

The model interprets a large/small expected gap through the distance to the next number
coprime to 2310 = 2·3·5·7·11. -/

/-- Coprimality to 2310 = 2·3·5·7·11: not divisible by any of these primes. -/
def coprimeTo2310 (n : ℕ) : Bool :=
  n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0

/-- The distance from n to the first number > n coprime to 2310 (search in a window of 2310). -/
def firstCoprimeOffset (n : ℕ) : ℕ :=
  match (List.range 2310).find? (fun d => coprimeTo2310 (n + d + 1)) with
  | some d => d + 1
  | none => 0

/-- **Algorithm guarantee:** if a candidate is found, its distance is ≤ 2310 (window length). -/
theorem firstCoprimeOffset_le (n : ℕ) : firstCoprimeOffset n ≤ 2310 := by
  unfold firstCoprimeOffset
  by_cases h : (List.range 2310).find? (fun d => coprimeTo2310 (n + d + 1)) = none
  · simp [h]
  · cases hf : (List.range 2310).find? (fun d => coprimeTo2310 (n + d + 1)) with
    | none => simp [hf] at h
    | some d =>
      simp
      have hmem : d ∈ List.range 2310 := by
        rcases (List.find?_eq_some_iff_append.mp hf) with ⟨_, as, bs, hxs, _⟩
        rw [hxs]
        simp
      have hlt : d < 2310 := List.mem_range.mp hmem
      omega

/-! **Top classes from the report (p mod 2310).** Large classes (C≈1.4–1.5) — candidate FAR
(distances 10–14), small (C≈0.70–0.71) — candidate CLOSE (distance 2). -/

-- Large classes: the first coprime candidate is far
example : firstCoprimeOffset 113 = 14 := by native_decide
example : firstCoprimeOffset 199 = 12 := by native_decide
example : firstCoprimeOffset 1789 = 12 := by native_decide
example : firstCoprimeOffset 2089 = 10 := by native_decide

-- Small classes: the first coprime candidate is close (p+2 is immediately a candidate)
example : firstCoprimeOffset 1271 = 2 := by native_decide
example : firstCoprimeOffset 221 = 2 := by native_decide
example : firstCoprimeOffset 1691 = 2 := by native_decide
example : firstCoprimeOffset 1481 = 2 := by native_decide

/-! ## 2. The contribution tables c_q and the multiplicative factor

From `GAP_INTERFERENCE_MODEL.md` (estimated from data, p < 3·10⁷). `qr x = x/10000`. -/

/-- x/10000 — writing the 4-digit tabular contributions as rationals. -/
def qr (x : ℕ) : ℚ := x / 10000

/-- c₂ = [1.0000, 1.0000]. -/
def c2 (j : ℕ) : ℚ := [qr 10000, qr 10000].getD j 0
/-- c₃ = [1.0000, 1.0287, 0.9721]. -/
def c3 (j : ℕ) : ℚ := [qr 10000, qr 10287, qr 9721].getD j 0
/-- c₅ = [1.0000, 0.9852, 0.9454, 1.0496, 1.0230]. -/
def c5 (j : ℕ) : ℚ := [qr 10000, qr 9852, qr 9454, qr 10496, qr 10230].getD j 0
/-- c₇ = [1.0000, 1.0563, 0.9763, 1.0155, 0.9731, 1.0257, 0.9567]. -/
def c7 (j : ℕ) : ℚ := [qr 10000, qr 10563, qr 9763, qr 10155, qr 9731, qr 10257, qr 9567].getD j 0
/-- c₁₁ = [1.0000, 0.9960, 0.9539, 1.0053, 0.9771, 1.0754, 0.9521, 1.0134, 0.9723, 1.0452, 1.0161]. -/
def c11 (j : ℕ) : ℚ := [qr 10000, qr 9960, qr 9539, qr 10053, qr 9771, qr 10754, qr 9521, qr 10134, qr 9723, qr 10452, qr 10161].getD j 0

/-- The multiplicative factor of the model: ∏_{q ∈ {2,3,5,7,11}} c_q(p mod q). -/
def interferenceMultiplier (p : ℕ) : ℚ :=
  c2 (p % 2) * c3 (p % 3) * c5 (p % 5) * c7 (p % 7) * c11 (p % 11)

-- Peaks of the interpretation (section 4 of the report): c₇(1) = 1.0563, c₁₁(5) = 1.0754 —
-- the classes after which the next coprime candidate is far.
example : c7 1 = qr 10563 := by rfl
example : c11 5 = qr 10754 := by rfl

-- Factors for the top classes of the report (computation)
#eval interferenceMultiplier 113    -- ≈ 1.0835
#eval interferenceMultiplier 1271   -- ≈ 0.8873

/-! **Check of the qualitative behavior of the model on the report classes:**
large classes (candidate far) → factor > 1, small (candidate close) → < 1. -/

example : 1 < interferenceMultiplier 113 := by native_decide
example : 1 < interferenceMultiplier 199 := by native_decide
example : 1 < interferenceMultiplier 1789 := by native_decide
example : 1 < interferenceMultiplier 2089 := by native_decide

example : interferenceMultiplier 1271 < 1 := by native_decide
example : interferenceMultiplier 221 < 1 := by native_decide
example : interferenceMultiplier 1691 < 1 := by native_decide
example : interferenceMultiplier 1481 < 1 := by native_decide

/-! ## 3. The expected gap predictor

`pₙ₊₁ ≈ pₙ + round( ln pₙ · ∏ c_q(pₙ mod q) )` (formula from the report, section 4).
`Real.log` is noncomputable → `noncomputable`; the predictor is NOT proved as a theorem
(an empirical estimate of the class mean, not an exact value). -/

/-- The expected gap after p according to the model (floor instead of round — implementation detail). -/
noncomputable def expectedGap (p : ℕ) : ℤ :=
  ⌊Real.log (p : ℝ) * (interferenceMultiplier p : ℝ)⌋

/-! ## 4. Honest summary

- **Proved (exactly):** the candidate distances of the top classes and the signs of the
  model factor (1.0835 > 1 vs 0.8873 < 1) — formalization of the qualitative conclusion of
  the report "far candidate → large gap".
- **Not proved and not provable here:** the accuracy of gap prediction, correlations,
  RMSE/MAE — this is empirical (see section 7 of the report).
- **Is not:** an exact formula for pₙ or a solution of open problems.
-/

end PN

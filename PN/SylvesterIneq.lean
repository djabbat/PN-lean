import Mathlib.Tactic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Chebyshev
set_option maxHeartbeats 800000

open scoped BigOperators
open scoped Topology
open Set

/-!
# Analytic infrastructure for the Sylvester–Schur real inequalities

Reusable real-analysis facts: log-vs-sqrt bounds, constant bounds, the
"minimum at endpoints for concave functions" helper, and the second-derivative
formulas for the region functions. All statements are English.
-/

namespace Nat

/-- `log 2 ≤ 1`. -/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- `2 ≤ 3 log 2` (i.e. `2/3 ≤ log 2`). -/
lemma two_thirds_le_log_two : (2 : ℝ) ≤ 3 * Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at h
  nlinarith

/-- `log 8 = 3 log 2 ≥ 2`. -/
lemma two_le_log_eight : (2 : ℝ) ≤ Real.log 8 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  simpa using two_thirds_le_log_two

/-- `log 8 ≤ 3`. -/
lemma log_eight_le_three : Real.log 8 ≤ 3 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  calc
    3 * Real.log 2 ≤ 3 * 1 := by gcongr; exact log_two_le_one
    _ = 3 := by norm_num

/-- `1 ≤ √2`. -/
lemma one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  simpa using h

/-- `√2 ≤ 17/12`. -/
lemma sqrt_two_le_seventeen_twelve : Real.sqrt 2 ≤ (17 : ℝ) / 12 := by
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 17 / 12)]
  norm_num

/-- `log 2 ≤ 5/6`. -/
lemma log_two_le_five_sixths : Real.log 2 ≤ 5 / 6 := by
  have h1 : Real.log 2 ≤ 2 * (Real.sqrt 2 - 1) := by
    have hlog : Real.log (Real.sqrt 2) ≤ Real.sqrt 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity : 0 < Real.sqrt 2)
    have hsq : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have h2 : 2 * (Real.sqrt 2 - 1) ≤ 5 / 6 := by
    nlinarith [sqrt_two_le_seventeen_twelve]
  linarith

/-- `log (1 + x) ≤ x` for `x > 0`. -/
lemma log_one_add_le {x : ℝ} (hx : 0 < x) : Real.log (1 + x) ≤ x := by
  have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  linarith

/-- `log (2x + 1) ≤ log (2x) + 1/(2x)` for `0 < x`. -/
lemma log_two_mul_add_one_le {x : ℝ} (hx : 0 < x) :
    Real.log (2 * x + 1) ≤ Real.log (2 * x) + 1 / (2 * x) := by
  have hpos : (0 : ℝ) < 2 * x := by positivity
  have h1 : (0 : ℝ) < 1 + 1 / (2 * x) := by positivity
  have hmul : 2 * x + 1 = 2 * x * (1 + 1 / (2 * x)) := by
    field_simp [hx.ne']
  calc
    Real.log (2 * x + 1) = Real.log (2 * x * (1 + 1 / (2 * x))) := by rw [hmul]
    _ = Real.log (2 * x) + Real.log (1 + 1 / (2 * x)) := by
      rw [Real.log_mul hpos.ne' (ne_of_gt h1)]
    _ ≤ Real.log (2 * x) + 1 / (2 * x) := by
      gcongr
      exact log_one_add_le (by positivity : (0 : ℝ) < 1 / (2 * x))

/-- `(2/3)·√x - log x` is strictly increasing on `[256, ∞)`. -/
lemma strictMonoOn_two_thirds_sqrt_sub_log :
    StrictMonoOn (fun x : ℝ => (2 / 3 : ℝ) * Real.sqrt x - Real.log x) (Set.Ici (256 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici (256 : ℝ)) ?_ ?_
  · have hcont : ContinuousOn (fun x : ℝ => (2 / 3 : ℝ) * Real.sqrt x - Real.log x)
        (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      exact (((Real.contDiffAt_sqrt (n := 0) hx0).continuousAt.const_mul (2 / 3 : ℝ)).sub
        (Real.continuousAt_log hx0)).continuousWithinAt
    refine hcont.mono ?_
    intro x hx
    rw [mem_Ici] at hx
    exact (by norm_num : (0 : ℝ) < 256).trans_le hx
  · intro x hx
    have hx256 : 256 < x := by simpa [Set.mem_Ici, interior_Ici] using hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hs : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x := by
      exact Real.hasDerivAt_sqrt (ne_of_gt hx0)
    have hg : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * Real.sqrt y - Real.log y)
        ((2 / 3 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹) x := by
      exact (hs.const_mul (2 / 3 : ℝ)).sub (Real.hasDerivAt_log (ne_of_gt hx0))
    rw [hg.deriv]
    have hx9lt : (9 : ℝ) < x := by linarith
    have hsq : 3 < Real.sqrt x := by
      rw [show (3 : ℝ) = Real.sqrt 9 by norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 9) hx9lt
    have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hcalc : (2 / 3 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹ = (Real.sqrt x - 3) / (3 * x) := by
      field_simp [hx0.ne']
      nlinarith [hsqx]
    rw [hcalc]
    have hnum : (0 : ℝ) < Real.sqrt x - 3 := sub_pos.mpr hsq
    have hden : (0 : ℝ) < 3 * x := by positivity
    exact (div_pos_iff_of_pos_right hden).mpr hnum

/-- `log x ≤ (2/3)·√x` for `x ≥ 256`. -/
lemma log_le_two_thirds_sqrt {x : ℝ} (hx : 256 ≤ x) : Real.log x ≤ (2 / 3 : ℝ) * Real.sqrt x := by
  by_cases hxeq : x = 256
  · subst x
    have hbase : (0 : ℝ) ≤ (2 / 3 : ℝ) * Real.sqrt 256 - Real.log 256 := by
      have h16 : (16 : ℝ) ≤ Real.sqrt 256 := by norm_num
      have hlog : Real.log 256 ≤ 8 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
        calc
          8 * Real.log 2 ≤ 8 * 1 := by gcongr; exact log_two_le_one
          _ = 8 := by norm_num
      have h1 : (8 : ℝ) ≤ (2 / 3 : ℝ) * Real.sqrt 256 := by
        have hfrac : (8 : ℝ) ≤ (2 / 3 : ℝ) * 16 := by norm_num
        exact hfrac.trans (mul_le_mul_of_nonneg_left h16 (by norm_num : (0 : ℝ) ≤ 2 / 3))
      exact sub_nonneg.mpr (hlog.trans h1)
    simpa using hbase
  · have hxlt : (256 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hxeq)
    have hg := strictMonoOn_two_thirds_sqrt_sub_log
    have h256 : (256 : ℝ) ∈ Set.Ici 256 := by simp
    have hxI : x ∈ Set.Ici 256 := by simp [hx]
    have hmono : (2 / 3 : ℝ) * Real.sqrt 256 - Real.log 256
        ≤ (2 / 3 : ℝ) * Real.sqrt x - Real.log x := (hg h256 hxI hxlt).le
    have hbase : (0 : ℝ) ≤ (2 / 3 : ℝ) * Real.sqrt 256 - Real.log 256 := by
      have h16 : (16 : ℝ) ≤ Real.sqrt 256 := by norm_num
      have hlog : Real.log 256 ≤ 8 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
        calc
          8 * Real.log 2 ≤ 8 * 1 := by gcongr; exact log_two_le_one
          _ = 8 := by norm_num
      have h1 : (8 : ℝ) ≤ (2 / 3 : ℝ) * Real.sqrt 256 := by
        have hfrac : (8 : ℝ) ≤ (2 / 3 : ℝ) * 16 := by norm_num
        exact hfrac.trans (mul_le_mul_of_nonneg_left h16 (by norm_num : (0 : ℝ) ≤ 2 / 3))
      exact sub_nonneg.mpr (hlog.trans h1)
    linarith

/-- `(9/20)·√x - log x` is strictly increasing on `[512, ∞)`. -/
lemma strictMonoOn_nine_twentieth_sqrt_sub_log :
    StrictMonoOn (fun x : ℝ => (9 / 20 : ℝ) * Real.sqrt x - Real.log x) (Set.Ici (512 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici (512 : ℝ)) ?_ ?_
  · have hcont : ContinuousOn (fun x : ℝ => (9 / 20 : ℝ) * Real.sqrt x - Real.log x)
        (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      exact (((Real.contDiffAt_sqrt (n := 0) hx0).continuousAt.const_mul (9 / 20 : ℝ)).sub
        (Real.continuousAt_log hx0)).continuousWithinAt
    refine hcont.mono ?_
    intro x hx
    rw [mem_Ici] at hx
    exact (by norm_num : (0 : ℝ) < 512).trans_le hx
  · intro x hx
    have hx512 : 512 < x := by simpa [Set.mem_Ici, interior_Ici] using hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hs : HasDerivAt (fun y : ℝ => Real.sqrt y) (1 / (2 * Real.sqrt x)) x := by
      exact Real.hasDerivAt_sqrt (ne_of_gt hx0)
    have hg : HasDerivAt (fun y : ℝ => (9 / 20 : ℝ) * Real.sqrt y - Real.log y)
        ((9 / 20 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹) x := by
      exact (hs.const_mul (9 / 20 : ℝ)).sub (Real.hasDerivAt_log (ne_of_gt hx0))
    rw [hg.deriv]
    have hsq : (40 / 9 : ℝ) < Real.sqrt x := by
      have hlt : (40 / 9 : ℝ) ^ 2 < x := by
        nlinarith
      have hsq' : Real.sqrt ((40 / 9 : ℝ) ^ 2) < Real.sqrt x := by
        exact Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ (40 / 9 : ℝ) ^ 2) hlt
      have hs2 : Real.sqrt ((40 / 9 : ℝ) ^ 2) = 40 / 9 := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 40 / 9)]
      simpa [hs2] using hsq'
    have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have hcalc : (9 / 20 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹
        = ((9 / 40 : ℝ) * Real.sqrt x - 1) / x := by
      field_simp [hx0.ne']
      nlinarith [hsqx]
    rw [hcalc]
    have hnum : (0 : ℝ) < (9 / 40 : ℝ) * Real.sqrt x - 1 := by nlinarith
    have hden : (0 : ℝ) < x := hx0
    exact (div_pos_iff_of_pos_right hden).mpr hnum

/-- `log x ≤ (9/20)·√x` for `x ≥ 512`. -/
lemma log_le_nine_twentieth_sqrt {x : ℝ} (hx : 512 ≤ x) : Real.log x ≤ (9 / 20 : ℝ) * Real.sqrt x := by
  by_cases hxeq : x = 512
  · subst x
    have hbase : (0 : ℝ) ≤ (9 / 20 : ℝ) * Real.sqrt 512 - Real.log 512 := by
      have h20 : (20 : ℝ) ≤ Real.sqrt 512 := by
        have hs := Real.sqrt_le_sqrt (by norm_num : (400 : ℝ) ≤ 512)
        norm_num at hs
        exact hs
      have hlog : Real.log 512 ≤ 9 := by
        rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
        calc
          9 * Real.log 2 ≤ 9 * 1 := by gcongr; exact log_two_le_one
          _ = 9 := by norm_num
      have h1 : (9 : ℝ) ≤ (9 / 20 : ℝ) * Real.sqrt 512 := by
        have hfrac : (9 : ℝ) ≤ (9 / 20 : ℝ) * 20 := by norm_num
        exact hfrac.trans (mul_le_mul_of_nonneg_left h20 (by norm_num : (0 : ℝ) ≤ 9 / 20))
      exact sub_nonneg.mpr (hlog.trans h1)
    simpa using hbase
  · have hxlt : (512 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hxeq)
    have hg := strictMonoOn_nine_twentieth_sqrt_sub_log
    have h512 : (512 : ℝ) ∈ Set.Ici 512 := by simp
    have hxI : x ∈ Set.Ici 512 := by simp [hx]
    have hmono : (9 / 20 : ℝ) * Real.sqrt 512 - Real.log 512
        ≤ (9 / 20 : ℝ) * Real.sqrt x - Real.log x := (hg h512 hxI hxlt).le
    have hbase : (0 : ℝ) ≤ (9 / 20 : ℝ) * Real.sqrt 512 - Real.log 512 := by
      have h20 : (20 : ℝ) ≤ Real.sqrt 512 := by
        have hs := Real.sqrt_le_sqrt (by norm_num : (400 : ℝ) ≤ 512)
        norm_num at hs
        exact hs
      have hlog : Real.log 512 ≤ 9 := by
        rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
        calc
          9 * Real.log 2 ≤ 9 * 1 := by gcongr; exact log_two_le_one
          _ = 9 := by norm_num
      have h1 : (9 : ℝ) ≤ (9 / 20 : ℝ) * Real.sqrt 512 := by
        have hfrac : (9 : ℝ) ≤ (9 / 20 : ℝ) * 20 := by norm_num
        exact hfrac.trans (mul_le_mul_of_nonneg_left h20 (by norm_num : (0 : ℝ) ≤ 9 / 20))
      exact sub_nonneg.mpr (hlog.trans h1)
    linarith

/-! ### Constant bounds used in the endpoints -/

/-- `(2:ℝ)/3 ≤ log 2` and `log 2 ≤ 1`. -/
lemma log_two_le_one' : Real.log 2 ≤ 1 := log_two_le_one

/-- `√2 ≤ 17/12` (re-export). -/
lemma sqrt_two_le : Real.sqrt 2 ≤ (17 : ℝ) / 12 := sqrt_two_le_seventeen_twelve

/-- `1 ≤ √2` (re-export). -/
lemma sqrt_two_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := one_le_sqrt_two

/-! ### Concavity: minimum at endpoints -/

/-- For a concave function on `[a,b]`, the minimum is attained at an endpoint. -/
lemma min_endpoint_le_concave {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f) :
    ∀ x ∈ Set.Icc a b, min (f a) (f b) ≤ f x := by
  intro x hx
  rcases hx with ⟨hax, hxb⟩
  let t : ℝ := (x - a) / (b - a)
  have hba : 0 < b - a := by linarith
  have hxeq : x = (1 - t) * a + t * b := by
    dsimp [t]
    field_simp [ne_of_gt hba]
    ring
  have ht0 : 0 ≤ t := by
    dsimp [t]
    rw [le_div_iff₀ hba]
    nlinarith
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_iff₀ hba]
    nlinarith
  have hmem_a : a ∈ Set.Icc a b := by exact ⟨le_rfl, le_of_lt hab⟩
  have hmem_b : b ∈ Set.Icc a b := by exact ⟨le_of_lt hab, le_rfl⟩
  have hconc : (1 - t) * f a + t * f b ≤ f ((1 - t) * a + t * b) :=
    hf.2 hmem_a hmem_b (by linarith : 0 ≤ 1 - t) ht0 (by linarith : (1 - t) + t = 1)
  have hx' : f ((1 - t) * a + t * b) = f x := by rw [hxeq]
  have hconc' : (1 - t) * f a + t * f b ≤ f x := by
    simpa [hx'] using hconc
  have hmin : min (f a) (f b) ≤ (1 - t) * f a + t * f b := by
    rcases le_total (f a) (f b) with h | h
    · have ht1' : 0 ≤ 1 - t := by linarith
      calc
        min (f a) (f b) = f a := by rw [min_eq_left h]
        _ = (1 - t) * f a + t * f a := by ring
        _ ≤ (1 - t) * f a + t * f b := by gcongr
    · have ht1' : 0 ≤ 1 - t := by linarith
      calc
        min (f a) (f b) = f b := by rw [min_eq_right h]
        _ = (1 - t) * f b + t * f b := by ring
        _ ≤ (1 - t) * f a + t * f b := by gcongr
  exact le_trans hmin hconc'

/-- A concave function positive at both endpoints is positive throughout. -/
lemma concave_positive_of_positive_endpoints {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Icc a b) f) (ha : 0 < f a) (hb : 0 < f b) :
    ∀ x ∈ Set.Icc a b, 0 < f x := by
  intro x hx
  have hmin : min (f a) (f b) ≤ f x := min_endpoint_le_concave hab hf x hx
  exact lt_of_lt_of_le (lt_min ha hb) hmin


/-! ### The mid-region function `M` and its derivatives -/

/-- `M(u) = K·log(u/(2K)) - ((√u - 1)/2)·log(u/2) - log(2K+1)`. -/
noncomputable def midM (K u : ℝ) : ℝ :=
  K * Real.log (u / (2 * K)) - ((Real.sqrt u - 1) / 2) * Real.log (u / 2) - Real.log (2 * K + 1)

/-- First derivative of `midM`. -/
lemma deriv_midM_first {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    deriv (fun x : ℝ => midM K x) u
    = K / u - (1 / (4 * Real.sqrt u)) * Real.log (u / 2) - (Real.sqrt u - 1) / (2 * u) := by
  have hA : HasDerivAt (fun x : ℝ => K * Real.log (x / (2 * K))) (K / u) u := by
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * K)) (1 / (2 * K)) u :=
      (hasDerivAt_id u).div_const (2 * K)
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (2 * K))) u⁻¹ u := by
      have hl : HasDerivAt (fun x : ℝ => Real.log (x / (2 * K)))
          (1 / (2 * K) / (u / (2 * K))) u := h1.log (by positivity)
      have hv : K⁻¹ * 2⁻¹ / (u / (2 * K)) = u⁻¹ := by
        field_simp [hK.ne', hu.ne']
      simpa [hv] using hl
    exact h2.const_mul K
  have hB : HasDerivAt (fun x : ℝ => ((Real.sqrt x - 1) / 2) * Real.log (x / 2))
      ((1 / (4 * Real.sqrt u)) * Real.log (u / 2) + ((Real.sqrt u - 1) / 2) / u) u := by
    have hs : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt u)) u :=
      Real.hasDerivAt_sqrt (ne_of_gt hu)
    have hsub : HasDerivAt ((fun x : ℝ => Real.sqrt x) - fun x : ℝ => 1) (1 / (2 * Real.sqrt u)) u := by
      simpa using (hs.sub (hasDerivAt_const u 1))
    have hb1 : HasDerivAt (fun x : ℝ => (Real.sqrt x - 1) / 2) (1 / (4 * Real.sqrt u)) u := by
      have hdiv : HasDerivAt (fun x : ℝ => (Real.sqrt x - 1) / 2) (1 / (2 * Real.sqrt u) / 2) u := by
        exact hsub.div_const 2
      have hv : 1 / (2 * Real.sqrt u) / 2 = 1 / (4 * Real.sqrt u) := by
        field_simp [hu.ne']
        ring
      rw [hv] at hdiv
      exact hdiv
    have hb2 : HasDerivAt (fun x : ℝ => Real.log (x / 2)) u⁻¹ u := by
      have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) u :=
        (hasDerivAt_id u).div_const 2
      have hl : HasDerivAt (fun x : ℝ => Real.log (x / 2)) (1 / 2 / (u / 2)) u :=
        h1.log (by positivity)
      have hv : 2⁻¹ / (u / 2) = u⁻¹ := by
        field_simp [hu.ne']
      simpa [hv] using hl
    exact hb1.mul hb2
  have hC : HasDerivAt (fun x : ℝ => Real.log (2 * K + 1)) 0 u := by
    have hc : HasDerivAt (fun x : ℝ => 2 * K + 1) 0 u := by
      simpa using (hasDerivAt_const u (2 * K + 1))
    have hl : HasDerivAt (fun x : ℝ => Real.log (2 * K + 1)) (0 / (2 * K + 1)) u :=
      hc.log (by positivity)
    have hv : 0 / (2 * K + 1) = 0 := by norm_num
    simpa [hv] using hl
  have hM : HasDerivAt (fun x : ℝ => midM K x)
      (K / u - ((1 / (4 * Real.sqrt u)) * Real.log (u / 2) + ((Real.sqrt u - 1) / 2) / u) - 0) u := by
    dsimp [midM]
    exact (hA.sub hB).sub hC
  have hv : (K / u - ((1 / (4 * Real.sqrt u)) * Real.log (u / 2) + ((Real.sqrt u - 1) / 2) / u) - 0)
      = K / u - (1 / (4 * Real.sqrt u)) * Real.log (u / 2) - (Real.sqrt u - 1) / (2 * u) := by
    field_simp [hu.ne']
    ring
  rw [hv] at hM
  exact hM.deriv
/-- The function `D(u) = deriv (midM K ·) u` for `u > 0`. -/
noncomputable def midD (K x : ℝ) : ℝ :=
  K / x - (1 / (4 * Real.sqrt x)) * Real.log (x / 2) - (Real.sqrt x - 1) / (2 * x)

/-- `deriv (midM K ·)` equals `midD K ·` pointwise on `Ioi 0`. -/
lemma deriv_midM_eq_midD {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    deriv (fun x : ℝ => midM K x) u = midD K u := by
  rw [deriv_midM_first hK hu]
  rfl


/-- Second derivative of `midM`:
`M'' = -(K + 1/2)/u² + (1/8)·log(u/2)/(u·√u)`. -/
lemma deriv2_midM {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    deriv^[2] (fun x : ℝ => midM K x) u
    = -(K + 1 / 2) / u ^ 2 + (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) := by
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
  have hlocal : (fun x : ℝ => deriv (fun y : ℝ => midM K y) x) =ᶠ[𝓝 u]
      (fun x : ℝ => midD K x) := by
    filter_upwards [hIoi] with x hx
    exact deriv_midM_eq_midD hK hx
  have hdeq : deriv (fun x : ℝ => deriv (fun y : ℝ => midM K y) x) u
      = deriv (fun x : ℝ => midD K x) u := hlocal.deriv_eq
  have hsqx : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt (ne_of_gt hu)
  have hD1 : HasDerivAt (fun x : ℝ => K / x) (-K / u ^ 2) u := by
    have hk : HasDerivAt (fun x : ℝ => K) (0 : ℝ) u := hasDerivAt_const u K
    have hid : HasDerivAt (fun x : ℝ => x) (1 : ℝ) u := hasDerivAt_id u
    have hdiv : HasDerivAt (fun x : ℝ => K / x) ((0 * u - K * 1) / u ^ 2) u :=
      hk.div hid (ne_of_gt hu)
    have hv : (0 * u - K * 1) / u ^ 2 = -K / u ^ 2 := by
      field_simp [hu.ne']
      ring
    rw [hv] at hdiv
    exact hdiv
  have hA : HasDerivAt (fun x : ℝ => 1 / (4 * Real.sqrt x)) (-(1 : ℝ) / (8 * u * Real.sqrt u)) u := by
    have h4 : HasDerivAt (fun x : ℝ => 4 * Real.sqrt x) (4 * (1 / (2 * Real.sqrt u))) u :=
      hs.const_mul 4
    have hconst : HasDerivAt (fun x : ℝ => 1) (0 : ℝ) u := hasDerivAt_const u (1 : ℝ)
    have hq : HasDerivAt (fun x : ℝ => 1 / (4 * Real.sqrt x))
        ((0 * (4 * Real.sqrt u) - 1 * (4 * (1 / (2 * Real.sqrt u)))) / (4 * Real.sqrt u) ^ 2) u :=
      hconst.div h4 (by positivity : 4 * Real.sqrt u ≠ 0)
    have hv : (0 * (4 * Real.sqrt u) - 1 * (4 * (1 / (2 * Real.sqrt u)))) / (4 * Real.sqrt u) ^ 2
        = -(1 : ℝ) / (8 * u * Real.sqrt u) := by
      field_simp [hu.ne', hsqx]
      nlinarith [hsqx]
    rw [hv] at hq
    exact hq
  have hB : HasDerivAt (fun x : ℝ => Real.log (x / 2)) u⁻¹ u := by
    have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) u :=
      (hasDerivAt_id u).div_const 2
    have hl : HasDerivAt (fun x : ℝ => Real.log (x / 2)) (1 / 2 / (u / 2)) u :=
      h1.log (by positivity)
    have hv : 2⁻¹ / (u / 2) = u⁻¹ := by
      field_simp [hu.ne']
    simpa [hv] using hl
  have hD2 : HasDerivAt (fun x : ℝ => (1 / (4 * Real.sqrt x)) * Real.log (x / 2))
      (-(1 : ℝ) / (8 * u * Real.sqrt u) * Real.log (u / 2) + 1 / (4 * Real.sqrt u) * u⁻¹) u :=
    hA.mul hB
  have hnum : HasDerivAt ((fun x : ℝ => Real.sqrt x) - fun x : ℝ => 1) (1 / (2 * Real.sqrt u)) u := by
    simpa using (hs.sub (hasDerivAt_const u (1 : ℝ)))
  have hden : HasDerivAt (fun x : ℝ => 2 * x) (2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul 2
  have hD3 : HasDerivAt (fun x : ℝ => (Real.sqrt x - 1) / (2 * x))
      ((2 - Real.sqrt u) / (4 * u ^ 2)) u := by
    have hq : HasDerivAt (fun x : ℝ => (Real.sqrt x - 1) / (2 * x))
        ((1 / (2 * Real.sqrt u) * (2 * u) - (Real.sqrt u - 1) * 2) / (2 * u) ^ 2) u :=
      hnum.div hden (by positivity : 2 * u ≠ 0)
    have hv : (1 / (2 * Real.sqrt u) * (2 * u) - (Real.sqrt u - 1) * 2) / (2 * u) ^ 2
        = (2 - Real.sqrt u) / (4 * u ^ 2) := by
      field_simp [hu.ne', hsqx]
      nlinarith [hsqx]
    rw [hv] at hq
    exact hq
  have hcomb : HasDerivAt (fun x : ℝ => midD K x)
      ((-K / u ^ 2)
        - (-(1 : ℝ) / (8 * u * Real.sqrt u) * Real.log (u / 2) + 1 / (4 * Real.sqrt u) * u⁻¹)
        - (2 - Real.sqrt u) / (4 * u ^ 2)) u := by
    dsimp [midD]
    exact (hD1.sub hD2).sub hD3
  have hv : (-K / u ^ 2)
        - (-(1 : ℝ) / (8 * u * Real.sqrt u) * Real.log (u / 2) + 1 / (4 * Real.sqrt u) * u⁻¹)
        - (2 - Real.sqrt u) / (4 * u ^ 2)
      = -(K + 1 / 2) / u ^ 2 + (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) := by
    field_simp [hu.ne', hsqx]
    nlinarith [hsqx]
  rw [hv] at hcomb
  have hD : HasDerivAt (fun x : ℝ => midD K x)
      (-(K + 1 / 2) / u ^ 2 + (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u)) u := hcomb
  have hmain : deriv (fun x : ℝ => deriv (fun y : ℝ => midM K y) x) u
      = -(K + 1 / 2) / u ^ 2 + (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) := by
    rw [hdeq]
    exact hD.deriv
  simpa [Function.iterate_succ_apply'] using hmain

/-- `M'' < 0` on `[2K, 16K]` for `K ≥ 256`: the mid-function is strictly concave there. -/
lemma deriv2_midM_neg {K u : ℝ} (hK256 : 256 ≤ K) (hu2 : 2 * K ≤ u) (hu16 : u ≤ 16 * K) :
    deriv^[2] (fun x : ℝ => midM K x) u < 0 := by
  have hK : 0 < K := by linarith
  have hu : 0 < u := by linarith
  have hsqx : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hlog : Real.log (u / 2) < (8 * K + 4) / Real.sqrt u := by
    have hu2le : u / 2 ≤ 8 * K := by linarith
    have hlog1 : Real.log (u / 2) ≤ Real.log (8 * K) :=
      Real.log_le_log (by positivity : 0 < u / 2) hu2le
    have hlk : Real.log K ≤ (2 / 3 : ℝ) * Real.sqrt K := log_le_two_thirds_sqrt hK256
    have hlog2 : Real.log (8 * K) ≤ (2 / 3 : ℝ) * Real.sqrt K + 3 := by
      calc
        Real.log (8 * K) = Real.log 8 + Real.log K := by
          rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hK)]
        _ ≤ 3 + (2 / 3 : ℝ) * Real.sqrt K := by linarith [hlk, log_eight_le_three]
        _ = (2 / 3 : ℝ) * Real.sqrt K + 3 := by ring
    have hs : Real.sqrt u ≤ 4 * Real.sqrt K := by
      have hs' : Real.sqrt u ≤ Real.sqrt (16 * K) := Real.sqrt_le_sqrt hu16
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) K] at hs'
      have h16s : Real.sqrt 16 = 4 := by norm_num
      rw [h16s] at hs'
      exact hs'
    have hrhs : (2 / 3 : ℝ) * Real.sqrt K + 3 < (8 * K + 4) / Real.sqrt u := by
      have h1 : (8 * K + 4) / (4 * Real.sqrt K) ≤ (8 * K + 4) / Real.sqrt u := by
        rw [div_le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt K) (by positivity : 0 < Real.sqrt u)]
        have hpos : 0 ≤ 8 * K + 4 := by linarith
        exact mul_le_mul_of_nonneg_left hs hpos
      have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
      have h2 : (8 * K + 4) / (4 * Real.sqrt K) = 2 * Real.sqrt K + 1 / Real.sqrt K := by
        field_simp [hK.ne']
        nlinarith [hsqK]
      have h3 : (2 / 3 : ℝ) * Real.sqrt K + 3 < 2 * Real.sqrt K + 1 / Real.sqrt K := by
        have hsK : 16 ≤ Real.sqrt K := by
          have hs' : Real.sqrt 256 ≤ Real.sqrt K := Real.sqrt_le_sqrt hK256
          norm_num at hs'
          exact hs'
        have hleft : 3 - 1 / Real.sqrt K < (4 / 3) * Real.sqrt K := by
          have h3lt : 3 < (4 / 3) * Real.sqrt K := by nlinarith [hsK]
          have h1ge : 3 - 1 / Real.sqrt K ≤ 3 := by
            have : (0 : ℝ) ≤ 1 / Real.sqrt K := by positivity
            linarith
          linarith
        linarith
      linarith
    exact lt_of_le_of_lt hlog1 (lt_of_le_of_lt hlog2 hrhs)
  have hA : (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) < (K + 1 / 2) / u ^ 2 := by
    have hlt : Real.log (u / 2) / (u * Real.sqrt u) < (8 * K + 4) / Real.sqrt u / (u * Real.sqrt u) := by
      exact div_lt_div_of_pos_right hlog (by positivity : 0 < u * Real.sqrt u)
    have hmul : (1 / 8) * (Real.log (u / 2) / (u * Real.sqrt u)) < (1 / 8) * ((8 * K + 4) / Real.sqrt u / (u * Real.sqrt u)) := by
      exact mul_lt_mul_of_pos_left hlt (by norm_num : (0 : ℝ) < 1 / 8)
    have hrhs : (1 / 8) * ((8 * K + 4) / Real.sqrt u / (u * Real.sqrt u)) = (K + 1 / 2) / u ^ 2 := by
      field_simp [hu.ne']
      nlinarith [hsqx]
    rw [hrhs] at hmul
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hfin : -(K + 1 / 2) / u ^ 2 + (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) < 0 := by
    have hsub : (1 / 8) * Real.log (u / 2) / (u * Real.sqrt u) - (K + 1 / 2) / u ^ 2 < 0 := by
      exact sub_lt_zero.mpr hA
    ring_nf at hsub ⊢
    exact hsub
  rw [deriv2_midM hK hu]
  exact hfin

/-- `midM` is strictly concave on `[2K, 16K]` for `K ≥ 256`. -/
lemma concaveOn_midM {K : ℝ} (hK256 : 256 ≤ K) :
    StrictConcaveOn ℝ (Set.Icc (2 * K) (16 * K)) (fun x : ℝ => midM K x) := by
  refine strictConcaveOn_of_deriv2_neg' (convex_Icc (2 * K) (16 * K)) ?_ ?_
  · -- continuity on Ioi 0, then restrict
    have hcont : ContinuousOn (fun x : ℝ => midM K x) (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      -- midM = K·log(x/(2K)) - ((√x-1)/2)·log(x/2) - log(2K+1)
      have h1 : ContinuousAt (fun x : ℝ => K * Real.log (x / (2 * K))) x := by
        refine ContinuousAt.const_mul ?_ K
        have hl : ContinuousAt (fun x : ℝ => Real.log (x / (2 * K))) x := by
          refine ContinuousAt.log ?_ ?_
          · exact (continuousAt_id.div_const (2 * K))
          · have : x / (2 * K) ≠ 0 := by positivity
            exact this
        exact hl
      have h2 : ContinuousAt (fun x : ℝ => ((Real.sqrt x - 1) / 2) * Real.log (x / 2)) x := by
        have hs : ContinuousAt (fun x : ℝ => Real.sqrt x) x :=
          (Real.contDiffAt_sqrt (n := 0) hx0).continuousAt
        have hl : ContinuousAt (fun x : ℝ => Real.log (x / 2)) x := by
          refine ContinuousAt.log ?_ ?_
          · exact (continuousAt_id.div_const 2)
          · have : x / 2 ≠ 0 := by positivity
            exact this
        have hsub : ContinuousAt (fun x : ℝ => (Real.sqrt x - 1) / 2) x :=
          (hs.sub continuousAt_const).div_const 2
        exact hsub.mul hl
      have h3 : ContinuousAt (fun x : ℝ => Real.log (2 * K + 1)) x := by
        refine ContinuousAt.log ?_ ?_
        · exact continuousAt_const
        · positivity
      exact ((h1.sub h2).sub h3).continuousWithinAt
    refine hcont.mono ?_
    intro x hx
    rw [mem_Icc] at hx
    exact (by linarith : (0 : ℝ) < 2 * K).trans_le hx.1
  · intro x hx
    have hx2 : 2 * K ≤ x := (mem_Icc.mp hx).1
    have hx16 : x ≤ 16 * K := (mem_Icc.mp hx).2
    exact deriv2_midM_neg hK256 hx2 hx16

/-- Endpoint `u = 4K`: `midM K (4K) > 0` for `K ≥ 256`. -/
lemma midM_fourK_pos {K : ℝ} (hK256 : 256 ≤ K) : 0 < midM K (4 * K) := by
  have hK : 0 < K := by linarith
  have h2K : 512 ≤ 2 * K := by linarith
  have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have h16 : 16 ≤ Real.sqrt K := by
    have hs' : Real.sqrt 256 ≤ Real.sqrt K := Real.sqrt_le_sqrt hK256
    norm_num at hs'
    exact hs'
  have hlog2k : Real.log (2 * K) ≤ (9 / 20 : ℝ) * Real.sqrt (2 * K) :=
    log_le_nine_twentieth_sqrt h2K
  have hlog2k1 : Real.log (2 * K + 1) ≤ Real.log (2 * K) + 1 / (2 * K) :=
    log_two_mul_add_one_le hK
  have hsqrt2k : Real.sqrt (2 * K) = Real.sqrt 2 * Real.sqrt K := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) K]
  have hs2 : Real.sqrt 2 ≤ (17 / 12 : ℝ) := sqrt_two_le_seventeen_twelve
  have hc : (9 / 20 : ℝ) * Real.sqrt (2 * K) ≤ (51 / 80 : ℝ) * Real.sqrt K := by
    rw [hsqrt2k]
    calc
      (9 / 20 : ℝ) * (Real.sqrt 2 * Real.sqrt K)
          ≤ (9 / 20 : ℝ) * ((17 / 12 : ℝ) * Real.sqrt K) := by
            gcongr
      _ = (51 / 80 : ℝ) * Real.sqrt K := by ring
  have hlog2k' : Real.log (2 * K) ≤ (51 / 80 : ℝ) * Real.sqrt K := le_trans hlog2k hc
  have hsqrtK_half : 0 ≤ Real.sqrt K - 1 / 2 := by linarith
  have hRHS : (Real.sqrt K - 1 / 2) * Real.log (2 * K) + Real.log (2 * K + 1)
      ≤ (51 / 80 : ℝ) * K + (51 / 160 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
    have h1 : (Real.sqrt K - 1 / 2) * Real.log (2 * K)
        ≤ (51 / 80 : ℝ) * K - (51 / 160 : ℝ) * Real.sqrt K := by
      calc
        (Real.sqrt K - 1 / 2) * Real.log (2 * K)
            ≤ (Real.sqrt K - 1 / 2) * ((51 / 80 : ℝ) * Real.sqrt K) :=
              mul_le_mul_of_nonneg_left hlog2k' hsqrtK_half
        _ = (51 / 80 : ℝ) * Real.sqrt K ^ 2 - (51 / 160 : ℝ) * Real.sqrt K := by ring
        _ = (51 / 80 : ℝ) * K - (51 / 160 : ℝ) * Real.sqrt K := by rw [hsqK]
    have h2 : Real.log (2 * K + 1) ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
      calc
        Real.log (2 * K + 1) ≤ Real.log (2 * K) + 1 / (2 * K) := hlog2k1
        _ ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by linarith
    linarith
  have hmain : (51 / 80 : ℝ) * K + (51 / 160 : ℝ) * Real.sqrt K + 1 / (2 * K)
      < K * Real.log 2 := by
    have htwo3 : (2 / 3 : ℝ) * K ≤ K * Real.log 2 := by
      have hl := two_thirds_le_log_two
      -- hl : 2 ≤ 3 log 2; multiply by K/3
      have hk3 : 0 ≤ K / 3 := by positivity
      calc
        (2 / 3 : ℝ) * K = (K / 3) * 2 := by ring
        _ ≤ (K / 3) * (3 * Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ K / 3)
        _ = K * Real.log 2 := by ring
    have hrecip : 1 / (2 * K) ≤ 1 / 512 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) (by norm_num : (0 : ℝ) < 512)]
      nlinarith
    have hstep : (51 / 80 : ℝ) * K + (51 / 160 : ℝ) * Real.sqrt K + 1 / (2 * K)
        < (2 / 3 : ℝ) * K := by
      -- (2/3 - 51/80)K = 7K/240 > (51/160)√K + 1/512
      have h7 : (7 / 240 : ℝ) * K > (51 / 160 : ℝ) * Real.sqrt K + 1 / 512 := by
        nlinarith [h16, hsqK]
      nlinarith
    exact hstep.trans_le htwo3
  have hgt : (Real.sqrt K - 1 / 2) * Real.log (2 * K) + Real.log (2 * K + 1)
      < K * Real.log 2 := hRHS.trans_lt hmain
  have hval : midM K (4 * K) = K * Real.log 2 - (Real.sqrt K - 1 / 2) * Real.log (2 * K)
      - Real.log (2 * K + 1) := by
    dsimp [midM]
    have hsqrt4 : Real.sqrt (4 * K) = 2 * Real.sqrt K := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) K]
      have hsq4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hsq4]
    have hdiv : (4 * K) / (2 * K) = 2 := by
      field_simp [hK.ne']
      ring
    have hlog_div : Real.log ((4 * K) / (2 * K)) = Real.log 2 :=
      congrArg Real.log hdiv
    have hdiv2 : (4 * K) / 2 = 2 * K := by
      field_simp
      ring
    have hlog_u2 : Real.log ((4 * K) / 2) = Real.log (2 * K) :=
      congrArg Real.log hdiv2
    rw [hsqrt4, hlog_div, hlog_u2]
    ring
  rw [hval]
  linarith


/-- `log(2K) ≤ (51/80)·√K` for `K ≥ 256`. -/
lemma log_two_mul_le {K : ℝ} (hK256 : 256 ≤ K) : Real.log (2 * K) ≤ (51 / 80 : ℝ) * Real.sqrt K := by
  have h2K : 512 ≤ 2 * K := by linarith
  have hlog2k : Real.log (2 * K) ≤ (9 / 20 : ℝ) * Real.sqrt (2 * K) := log_le_nine_twentieth_sqrt h2K
  have hsqrt2k : Real.sqrt (2 * K) = Real.sqrt 2 * Real.sqrt K := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) K]
  have hs2 : Real.sqrt 2 ≤ (17 / 12 : ℝ) := sqrt_two_le_seventeen_twelve
  calc
    Real.log (2 * K) ≤ (9 / 20 : ℝ) * Real.sqrt (2 * K) := hlog2k
    _ ≤ (9 / 20 : ℝ) * ((17 / 12 : ℝ) * Real.sqrt K) := by
      rw [hsqrt2k]
      gcongr
    _ = (51 / 80 : ℝ) * Real.sqrt K := by ring

/-- Endpoint `u = 16K`: `midM K (16K) > 0` for `K ≥ 256`. -/
lemma midM_sixteenK_pos {K : ℝ} (hK256 : 256 ≤ K) : 0 < midM K (16 * K) := by
  have hK : 0 < K := by linarith
  have h2K : 512 ≤ 2 * K := by linarith
  have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have h16 : 16 ≤ Real.sqrt K := by
    have hs' : Real.sqrt 256 ≤ Real.sqrt K := Real.sqrt_le_sqrt hK256
    norm_num at hs'
    exact hs'
  have hlog8k : Real.log (8 * K) ≤ (2 / 3 : ℝ) * Real.sqrt K + 3 := by
    calc
      Real.log (8 * K) = Real.log 8 + Real.log K := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hK)]
      _ ≤ (2 / 3 : ℝ) * Real.sqrt K + 3 := by
        linarith [log_eight_le_three, log_le_two_thirds_sqrt hK256]
  have hlog2k1 : Real.log (2 * K + 1) ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
    calc
      Real.log (2 * K + 1) ≤ Real.log (2 * K) + 1 / (2 * K) := log_two_mul_add_one_le hK
      _ ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by linarith [log_two_mul_le hK256]
  have hRHS : (2 * Real.sqrt K - 1 / 2) * Real.log (8 * K) + Real.log (2 * K + 1)
      ≤ (4 / 3 : ℝ) * K + (6 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
    have hlog8kge0 : 0 ≤ Real.log (8 * K) := Real.log_nonneg (by linarith : 1 ≤ 8 * K)
    have h1 : (2 * Real.sqrt K - 1 / 2) * Real.log (8 * K)
        ≤ (2 * Real.sqrt K) * ((2 / 3 : ℝ) * Real.sqrt K + 3) := by
      have hle1 : (2 * Real.sqrt K - 1 / 2) * Real.log (8 * K) ≤ (2 * Real.sqrt K) * Real.log (8 * K) := by
        exact mul_le_mul_of_nonneg_right (by linarith : 2 * Real.sqrt K - 1 / 2 ≤ 2 * Real.sqrt K) hlog8kge0
      have hle2 : (2 * Real.sqrt K) * Real.log (8 * K) ≤ (2 * Real.sqrt K) * ((2 / 3 : ℝ) * Real.sqrt K + 3) := by
        exact mul_le_mul_of_nonneg_left hlog8k (by positivity : 0 ≤ 2 * Real.sqrt K)
      exact hle1.trans hle2
    have hb : (2 * Real.sqrt K) * ((2 / 3 : ℝ) * Real.sqrt K + 3)
        = 6 * Real.sqrt K + (4 / 3 : ℝ) * K := by
      nlinarith [hsqK]
    linarith
  have hmain : (4 / 3 : ℝ) * K + (6 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
      < K * Real.log 8 := by
    have hln8 : (2 : ℝ) * K ≤ K * Real.log 8 := by
      calc
        (2 : ℝ) * K = K * 2 := by ring
        _ ≤ K * Real.log 8 := by
          exact mul_le_mul_of_nonneg_left two_le_log_eight (by positivity : 0 ≤ K)
    have hrecip : 1 / (2 * K) ≤ 1 / 512 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) (by norm_num : (0 : ℝ) < 512)]
      nlinarith
    have hstep : (4 / 3 : ℝ) * K + (6 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
        < (2 : ℝ) * K := by
      have h8 : (2 / 3 : ℝ) * K > (6 + 51 / 80 : ℝ) * Real.sqrt K + 1 / 512 := by
        nlinarith [h16, hsqK]
      nlinarith
    exact hstep.trans_le hln8
  have hgt : (2 * Real.sqrt K - 1 / 2) * Real.log (8 * K) + Real.log (2 * K + 1)
      < K * Real.log 8 := hRHS.trans_lt hmain
  have hval : midM K (16 * K) = K * Real.log 8 - (2 * Real.sqrt K - 1 / 2) * Real.log (8 * K)
      - Real.log (2 * K + 1) := by
    dsimp [midM]
    have hsqrt16 : Real.sqrt (16 * K) = 4 * Real.sqrt K := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) K]
      have hsq16 : Real.sqrt 16 = 4 := by
        rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      rw [hsq16]
    have hdiv : (16 * K) / (2 * K) = 8 := by
      field_simp [hK.ne']
      ring
    have hlog_div : Real.log ((16 * K) / (2 * K)) = Real.log 8 := congrArg Real.log hdiv
    have hdiv2 : (16 * K) / 2 = 8 * K := by
      field_simp
      ring
    have hlog_u2 : Real.log ((16 * K) / 2) = Real.log (8 * K) := congrArg Real.log hdiv2
    rw [hsqrt16, hlog_div, hlog_u2]
    ring
  rw [hval]
  linarith

/-- `2/5 ≤ log(3/2)`. -/
lemma two_fifths_le_log_three_half : (2 : ℝ) / 5 ≤ Real.log (3 / 2) := by
  have h := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
  norm_num at h
  exact h

/-- `log(3/2) ≤ 1/2`. -/
lemma log_three_half_le_half : Real.log (3 / 2) ≤ 1 / 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  linarith

/-- `log(2K) ≤ (51/80)·√K` for `K ≥ 256`. -/
lemma log_two_mul_le' {K : ℝ} (hK256 : 256 ≤ K) : Real.log (2 * K) ≤ (51 / 80 : ℝ) * Real.sqrt K :=
  log_two_mul_le hK256

/-- `log(2K+1) ≤ (51/80)·√K + 1/(2K)` for `K ≥ 256`. -/
lemma log_two_mul_add_one_le' {K : ℝ} (hK256 : 256 ≤ K) :
    Real.log (2 * K + 1) ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
  have hK : 0 < K := by linarith
  calc
    Real.log (2 * K + 1) ≤ Real.log (2 * K) + 1 / (2 * K) := log_two_mul_add_one_le hK
    _ ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by linarith [log_two_mul_le hK256]

/-- `(2/7)·√x - log x` is strictly increasing on `[1024, ∞)`. -/
lemma strictMonoOn_two_sevenths_sqrt_sub_log :
    StrictMonoOn (fun x : ℝ => (2 / 7 : ℝ) * Real.sqrt x - Real.log x) (Set.Ici (1024 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici (1024 : ℝ)) ?_ ?_
  · have hcont : ContinuousOn (fun x : ℝ => (2 / 7 : ℝ) * Real.sqrt x - Real.log x)
        (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      exact (((Real.contDiffAt_sqrt (n := 0) hx0).continuousAt.const_mul (2 / 7 : ℝ)).sub
        (Real.continuousAt_log hx0)).continuousWithinAt
    refine hcont.mono ?_
    intro x hx
    rw [mem_Ici] at hx
    exact (by norm_num : (0 : ℝ) < 1024).trans_le hx
  · intro x hx
    have hx1024 : 1024 < x := by simpa [Set.mem_Ici, interior_Ici] using hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hs : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt x)) x :=
      Real.hasDerivAt_sqrt (ne_of_gt hx0)
    have hg : HasDerivAt (fun y : ℝ => (2 / 7 : ℝ) * Real.sqrt y - Real.log y)
        ((2 / 7 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹) x :=
      (hs.const_mul (2 / 7 : ℝ)).sub (Real.hasDerivAt_log (ne_of_gt hx0))
    rw [hg.deriv]
    have hsq : 7 < Real.sqrt x := by
      have hx49 : (49 : ℝ) < x := by linarith
      have hsq' : Real.sqrt 49 < Real.sqrt x :=
        Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 49) hx49
      have hs49 : Real.sqrt 49 = 7 := by
        rw [show (49 : ℝ) = 7 ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7)]
      rw [hs49] at hsq'
      exact hsq'
    have hcalc : (2 / 7 : ℝ) * (1 / (2 * Real.sqrt x)) - x⁻¹ = (Real.sqrt x - 7) / (7 * x) := by
      have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
      field_simp [hx0.ne']
      nlinarith [hsqx]
    rw [hcalc]
    have hnum : (0 : ℝ) < Real.sqrt x - 7 := sub_pos.mpr hsq
    have hden : (0 : ℝ) < 7 * x := by positivity
    exact (div_pos_iff_of_pos_right hden).mpr hnum

/-- `log x ≤ (2/7)·√x` for `x ≥ 1024`. -/
lemma log_le_two_sevenths_sqrt {x : ℝ} (hx : 1024 ≤ x) : Real.log x ≤ (2 / 7 : ℝ) * Real.sqrt x := by
  by_cases hxeq : x = 1024
  · subst x
    have h32 : (32 : ℝ) ≤ Real.sqrt 1024 := by
      rw [show (1024 : ℝ) = 32 ^ 2 by norm_num]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
    have hlog : Real.log 1024 ≤ 25 / 3 := by
      rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
      calc
        10 * Real.log 2 ≤ 10 * (5 / 6) := by gcongr; exact log_two_le_five_sixths
        _ = 25 / 3 := by norm_num
    have h1 : Real.log 1024 ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by
      have h1b : (64 / 7 : ℝ) = (2 / 7 : ℝ) * 32 := by norm_num
      have h1c : (2 / 7 : ℝ) * 32 ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by
        exact mul_le_mul_of_nonneg_left h32 (by norm_num : (0 : ℝ) ≤ 2 / 7)
      calc
        Real.log 1024 ≤ 25 / 3 := hlog
        _ ≤ 64 / 7 := by linarith
        _ ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by linarith [h1b, h1c]
    exact h1
  · have hxlt : (1024 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hxeq)
    have hg := strictMonoOn_two_sevenths_sqrt_sub_log
    have h1024 : (1024 : ℝ) ∈ Set.Ici 1024 := by simp
    have hxI : x ∈ Set.Ici 1024 := by simp [hx]
    have hmono : (2 / 7 : ℝ) * Real.sqrt 1024 - Real.log 1024
        ≤ (2 / 7 : ℝ) * Real.sqrt x - Real.log x := (hg h1024 hxI hxlt).le
    have hbase : (0 : ℝ) ≤ (2 / 7 : ℝ) * Real.sqrt 1024 - Real.log 1024 := by
      have h32 : (32 : ℝ) ≤ Real.sqrt 1024 := by
        rw [show (1024 : ℝ) = 32 ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)]
      have hlog : Real.log 1024 ≤ 25 / 3 := by
        rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
        calc
          10 * Real.log 2 ≤ 10 * (5 / 6) := by gcongr; exact log_two_le_five_sixths
          _ = 25 / 3 := by norm_num
      have h1 : Real.log 1024 ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by
        have h1b : (64 / 7 : ℝ) = (2 / 7 : ℝ) * 32 := by norm_num
        have h1c : (2 / 7 : ℝ) * 32 ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by
          exact mul_le_mul_of_nonneg_left h32 (by norm_num : (0 : ℝ) ≤ 2 / 7)
        calc
          Real.log 1024 ≤ 25 / 3 := hlog
          _ ≤ 64 / 7 := by linarith
          _ ≤ (2 / 7 : ℝ) * Real.sqrt 1024 := by linarith [h1b, h1c]
      linarith
    linarith

/-- Endpoint `u = 3K`: `midM K (3K) > 0` for `K ≥ 1024`. -/
lemma midM_threeK_pos {K : ℝ} (hK1024 : 1024 ≤ K) : 0 < midM K (3 * K) := by
  have hK : 0 < K := by linarith
  have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have h3half_le : Real.log (3 / 2) ≤ 1 / 2 := log_three_half_le_half
  have h3half_ge : (2 / 5 : ℝ) ≤ Real.log (3 / 2) := two_fifths_le_log_three_half
  have hsq3 : Real.sqrt (3 * K) ≤ (7 / 4 : ℝ) * Real.sqrt K := by
    have hs' : Real.sqrt (3 * K) ≤ Real.sqrt ((7 / 4 : ℝ) ^ 2 * K) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (7 / 4 : ℝ) ^ 2) K] at hs'
    have hs4 : Real.sqrt ((7 / 4 : ℝ) ^ 2) = 7 / 4 := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4)]
    rw [hs4] at hs'
    simpa [mul_comm] using hs'
  have hlogK : Real.log K ≤ (2 / 7 : ℝ) * Real.sqrt K := log_le_two_sevenths_sqrt hK1024
  have hlog2k1 : Real.log (2 * K + 1) ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) :=
    log_two_mul_add_one_le' (by linarith : 256 ≤ K)
  have hRHS : (Real.sqrt (3 * K) - 1) / 2 * Real.log (3 * K / 2) + Real.log (2 * K + 1)
      ≤ (1 / 4 : ℝ) * K + (7 / 16 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
    have hlg : Real.log (3 * K / 2) ≤ 1 / 2 + (2 / 7 : ℝ) * Real.sqrt K := by
      calc
        Real.log (3 * K / 2) = Real.log (3 / 2 * K) := by congr 1; ring
        _ = Real.log (3 / 2) + Real.log K := by
          rw [Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) (ne_of_gt hK)]
        _ ≤ 1 / 2 + (2 / 7 : ℝ) * Real.sqrt K := by linarith [h3half_le, hlogK]
    have h1 : (Real.sqrt (3 * K) - 1) / 2 * Real.log (3 * K / 2)
        ≤ (7 / 8 : ℝ) * Real.sqrt K * (1 / 2 + (2 / 7 : ℝ) * Real.sqrt K) := by
      have hpart1 : (Real.sqrt (3 * K) - 1) / 2 ≤ (7 / 8 : ℝ) * Real.sqrt K := by
        have : Real.sqrt (3 * K) - 1 ≤ (7 / 4 : ℝ) * Real.sqrt K := by linarith [hsq3]
        nlinarith
      have hlgge0 : 0 ≤ Real.log (3 * K / 2) := Real.log_nonneg (by linarith : 1 ≤ 3 * K / 2)
      calc
        (Real.sqrt (3 * K) - 1) / 2 * Real.log (3 * K / 2)
            ≤ (7 / 8 : ℝ) * Real.sqrt K * Real.log (3 * K / 2) := by
              exact mul_le_mul_of_nonneg_right hpart1 hlgge0
        _ ≤ (7 / 8 : ℝ) * Real.sqrt K * (1 / 2 + (2 / 7 : ℝ) * Real.sqrt K) := by
              exact mul_le_mul_of_nonneg_left hlg (by positivity : 0 ≤ (7 / 8 : ℝ) * Real.sqrt K)
    have hb : (7 / 8 : ℝ) * Real.sqrt K * (1 / 2 + (2 / 7 : ℝ) * Real.sqrt K)
        = (1 / 4 : ℝ) * K + (7 / 16 : ℝ) * Real.sqrt K := by
      rw [show (7 / 8 : ℝ) * Real.sqrt K * (1 / 2 + (2 / 7 : ℝ) * Real.sqrt K)
          = (7 / 16 : ℝ) * Real.sqrt K + (1 / 4 : ℝ) * Real.sqrt K ^ 2 by ring]
      rw [hsqK]
      ring
    linarith
  have hmain : (1 / 4 : ℝ) * K + (7 / 16 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
      < K * Real.log (3 / 2) := by
    have hlhs : (2 / 5 : ℝ) * K ≤ K * Real.log (3 / 2) := by
      calc
        (2 / 5 : ℝ) * K = K * (2 / 5) := by ring
        _ ≤ K * Real.log (3 / 2) := by
          exact mul_le_mul_of_nonneg_left h3half_ge (by positivity : 0 ≤ K)
    have hrecip : 1 / (2 * K) ≤ 1 / 2048 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) (by norm_num : (0 : ℝ) < 2048)]
      nlinarith
    have hstep : (1 / 4 : ℝ) * K + (7 / 16 + 51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
        < (2 / 5 : ℝ) * K := by
      -- (2/5 - 1/4)K = 3K/20 > (7/16+51/80)√K + 1/2048
      have hsqK2 : Real.sqrt K ^ 2 = K := hsqK
      have hbig : (3 / 20 : ℝ) * K > (7 / 16 + 51 / 80 : ℝ) * Real.sqrt K + 1 / 2048 := by
        have hs32 : 32 ≤ Real.sqrt K := by
          have hs' : Real.sqrt 1024 ≤ Real.sqrt K := Real.sqrt_le_sqrt hK1024
          norm_num at hs'
          exact hs'
        nlinarith [hsqK2]
      nlinarith
    exact hstep.trans_le hlhs
  have hgt : (Real.sqrt (3 * K) - 1) / 2 * Real.log (3 * K / 2) + Real.log (2 * K + 1)
      < K * Real.log (3 / 2) := hRHS.trans_lt hmain
  have hval : midM K (3 * K) = K * Real.log (3 / 2)
      - (Real.sqrt (3 * K) - 1) / 2 * Real.log (3 * K / 2) - Real.log (2 * K + 1) := by
    dsimp [midM]
    have hsqrt3 : Real.sqrt (3 * K) = Real.sqrt (3 * K) := rfl
    have hdiv : (3 * K) / (2 * K) = 3 / 2 := by
      field_simp [hK.ne']
    have hlog_div : Real.log ((3 * K) / (2 * K)) = Real.log (3 / 2) := congrArg Real.log hdiv
    rw [hlog_div]
  rw [hval]
  linarith

/-- `log 4 ≥ 4/3`. -/
lemma log4_ge_four_thirds : (4 : ℝ) / 3 ≤ Real.log 4 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [two_thirds_le_log_two]

/-- The c1 endpoint `u = 2K` is positive: `(K/3)ln4 > ((√(2K)−1)/2)·lnK + ln(2K+1)`. -/
lemma c1_endpoint_twoK_pos {K : ℝ} (hK1024 : 1024 ≤ K) :
    0 < (K / 3) * Real.log 4 - (Real.sqrt (2 * K) - 1) / 2 * Real.log K - Real.log (2 * K + 1) := by
  have hK : 0 < K := by linarith
  have hsqK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK.le
  have hlogK : Real.log K ≤ (2 / 7 : ℝ) * Real.sqrt K := log_le_two_sevenths_sqrt hK1024
  have hlog2k1 : Real.log (2 * K + 1) ≤ (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) :=
    log_two_mul_add_one_le' (by linarith : 256 ≤ K)
  have hsqrt2 : Real.sqrt (2 * K) ≤ (17 / 12 : ℝ) * Real.sqrt K := by
    have hs' : Real.sqrt (2 * K) ≤ Real.sqrt ((17 / 12 : ℝ) ^ 2 * K) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (17 / 12 : ℝ) ^ 2) K] at hs'
    have hs4 : Real.sqrt ((17 / 12 : ℝ) ^ 2) = 17 / 12 := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 17 / 12)]
    rw [hs4] at hs'
    simpa [mul_comm] using hs'
  have hRHS : (Real.sqrt (2 * K) - 1) / 2 * Real.log K + Real.log (2 * K + 1)
      ≤ (17 / 84 : ℝ) * K + (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K) := by
    have hlgge0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith : 1 ≤ K)
    have h1 : (Real.sqrt (2 * K) - 1) / 2 * Real.log K
        ≤ (17 / 24 : ℝ) * Real.sqrt K * Real.log K := by
      have hpart : (Real.sqrt (2 * K) - 1) / 2 ≤ (17 / 24 : ℝ) * Real.sqrt K := by
        have : Real.sqrt (2 * K) - 1 ≤ (17 / 12 : ℝ) * Real.sqrt K := by linarith [hsqrt2]
        nlinarith
      exact mul_le_mul_of_nonneg_right hpart hlgge0
    have h2 : (17 / 24 : ℝ) * Real.sqrt K * Real.log K ≤ (17 / 84 : ℝ) * K := by
      have hlogKle : (17 / 24 : ℝ) * Real.sqrt K * Real.log K
          ≤ (17 / 24 : ℝ) * Real.sqrt K * ((2 / 7 : ℝ) * Real.sqrt K) := by
        exact mul_le_mul_of_nonneg_left hlogK (by positivity : 0 ≤ (17 / 24 : ℝ) * Real.sqrt K)
      have hval : (17 / 24 : ℝ) * Real.sqrt K * ((2 / 7 : ℝ) * Real.sqrt K) ≤ (17 / 84 : ℝ) * K := by
        nlinarith [hsqK]
      exact hlogKle.trans hval
    linarith
  have hmain : (17 / 84 : ℝ) * K + (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
      < (K / 3) * Real.log 4 := by
    have hlhs : (4 / 9 : ℝ) * K ≤ (K / 3) * Real.log 4 := by
      calc
        (4 / 9 : ℝ) * K = (K / 3) * (4 / 3) := by ring
        _ ≤ (K / 3) * Real.log 4 := by
          exact mul_le_mul_of_nonneg_left log4_ge_four_thirds (by positivity : 0 ≤ K / 3)
    have hrecip : 1 / (2 * K) ≤ 1 / 2048 := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * K) (by norm_num : (0 : ℝ) < 2048)]
      nlinarith
    have hstep : (17 / 84 : ℝ) * K + (51 / 80 : ℝ) * Real.sqrt K + 1 / (2 * K)
        < (4 / 9 : ℝ) * K := by
      have hbig : (61 / 252 : ℝ) * K > (51 / 80 : ℝ) * Real.sqrt K + 1 / 2048 := by
        have hs32 : 32 ≤ Real.sqrt K := by
          have hs' : Real.sqrt 1024 ≤ Real.sqrt K := Real.sqrt_le_sqrt hK1024
          norm_num at hs'
          exact hs'
        nlinarith [hsqK]
      nlinarith
    exact hstep.trans_le hlhs
  have hgt : (Real.sqrt (2 * K) - 1) / 2 * Real.log K + Real.log (2 * K + 1)
      < (K / 3) * Real.log 4 := hRHS.trans_lt hmain
  linarith

/-- The c1 function `C(u) = K ln4 + K ln(u/(2K)) − (u/3)ln4 − ((√u−1)/2)ln(u/2) − ln(2K+1)`. -/
noncomputable def c1F (K u : ℝ) : ℝ :=
  K * Real.log 4 + K * Real.log (u / (2 * K)) - (u / 3) * Real.log 4
    - ((Real.sqrt u - 1) / 2) * Real.log (u / 2) - Real.log (2 * K + 1)

/-- `C'' = M''`, so `C` is strictly concave on `[2K, 16K]` for `K ≥ 256`. -/
lemma concaveOn_c1F {K : ℝ} (hK256 : 256 ≤ K) :
    ConcaveOn ℝ (Set.Icc (2 * K) (16 * K)) (fun x : ℝ => c1F K x) := by
  have hc_mid : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K)) (fun x : ℝ => midM K x) :=
    (concaveOn_midM hK256).concaveOn
  have hc_aff : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K))
      (fun x : ℝ => K * Real.log 4 - (x / 3) * Real.log 4) := by
    have hlin : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K))
        (fun x : ℝ => -(Real.log 4 / 3) * x) := by
      refine ⟨convex_Icc (2 * K) (16 * K), ?_⟩
      intro x hx y hy a b ha hb hab
      change a * (-(Real.log 4 / 3) * x) + b * (-(Real.log 4 / 3) * y) ≤ -(Real.log 4 / 3) * (a * x + b * y)
      have heq : a * (-(Real.log 4 / 3) * x) + b * (-(Real.log 4 / 3) * y) = -(Real.log 4 / 3) * (a * x + b * y) := by
        ring
      rw [heq]
    have hd : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K)) (fun x : ℝ => K * Real.log 4) :=
      concaveOn_const (K * Real.log 4) (convex_Icc (2 * K) (16 * K))
    have hlin_full : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K))
        (fun x : ℝ => -(Real.log 4 / 3) * x + K * Real.log 4) := hlin.add hd
    convert hlin_full using 1
    · ext x
      ring
  have hc_sum : ConcaveOn ℝ (Set.Icc (2 * K) (16 * K))
      (fun x : ℝ => midM K x + (K * Real.log 4 - (x / 3) * Real.log 4)) := hc_mid.add hc_aff
  have hfun : (fun x : ℝ => midM K x + (K * Real.log 4 - (x / 3) * Real.log 4))
      = fun x : ℝ => c1F K x := by
    funext x
    dsimp [c1F, midM]
    ring
  rwa [hfun] at hc_sum

/-! ### Far-region function `farG` and its analysis

The far region is `16k ≤ n < k²` with `k ≥ 192` (finite head covers `64 ≤ k < 192`).
The log-inequality we need is
`k·ln4 + (√n + n^{1/3} + n^{1/5})·ln4 + n^{1/4}·ln n + (2/3)n^{1/6}·ln n + (2/5)n^{1/10}·ln n < k·ln(n/k)`.
Define `farG(K,u) = K·ln(u/(4K)) − ln4·(√u + u^{1/3} + u^{1/5}) − u^{1/4}ln u − (2/3)u^{1/6}ln u − (2/5)u^{1/10}ln u`.
Positive values of `farG` on `[16K, K²]` give the inequality.
-/

/-- `log 2 ≤ 3/4`. -/
lemma log_two_le_three_fourths : Real.log 2 ≤ (3 : ℝ) / 4 := by
  have h1 : (1 : ℝ) + 1 / 8 ≤ Real.exp (1 / 8) := by
    have h := Real.add_one_le_exp (1 / 8)
    linarith
  have h3 : (9 : ℝ) / 8 ≤ Real.exp (1 / 8) := by
    norm_num at h1 ⊢
    exact h1
  have h4' : ((9 : ℝ) / 8) ^ 6 ≤ Real.exp (1 / 8) ^ 6 := by
    exact pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9 : ℝ) / 8) h3 6
  have h4 : Real.exp ((3 : ℝ) / 4) ≥ ((9 : ℝ) / 8) ^ 6 := by
    have h6 : (3 : ℝ) / 4 = (6 : ℕ) * (1 / 8) := by norm_num
    rw [h6, Real.exp_nat_mul]
    exact h4'
  have hgt : ((9 : ℝ) / 8) ^ 6 > (2 : ℝ) := by norm_num
  have h2le : (2 : ℝ) ≤ Real.exp ((3 : ℝ) / 4) := le_trans (le_of_lt hgt) h4
  have hlog : Real.log 2 ≤ Real.log (Real.exp ((3 : ℝ) / 4)) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
  simpa using hlog

/-- `log 4 ≤ 3/2`. -/
lemma log_four_le_three_halves : Real.log 4 ≤ (3 : ℝ) / 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  nlinarith [log_two_le_three_fourths]

/-- `√x ≤ x/8` for `x ≥ 64`. -/
lemma sqrt_le_eighth_self {x : ℝ} (hx : 64 ≤ x) : Real.sqrt x ≤ x / 8 := by
  have hxpos : 0 < x := by linarith
  have h8 : 8 ≤ Real.sqrt x := by
    have h' : Real.sqrt 64 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    norm_num at h'
    exact h'
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  nlinarith

/-- `c ≤ x^(1/3)` whenever `c³ ≤ x` and `0 ≤ c`. -/
lemma rpow_inv_three_ge {x c : ℝ} (hx : c ^ 3 ≤ x) (hc : 0 ≤ c) :
    c ≤ x ^ ((3 : ℝ)⁻¹) := by
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ c ^ 3) hx (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  have hc3 : (c ^ 3) ^ ((3 : ℝ)⁻¹) = c := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num
  rwa [hc3] at hpow

/-- `x^(2/3) ≤ x/5` for `x ≥ 125`. -/
lemma rpow_two_thirds_le_div_five {x : ℝ} (hx : 125 ≤ x) : x ^ ((2 : ℝ) / 3) ≤ x / 5 := by
  have hxpos : 0 < x := by linarith
  have h5 : (5 : ℝ) ≤ x ^ ((3 : ℝ)⁻¹) := by
    have hc : (5 : ℝ) ^ 3 = 125 := by norm_num
    exact rpow_inv_three_ge (x := x) (c := 5) (by rw [hc]; exact hx) (by norm_num)
  have hx23 : x ^ ((2 : ℝ) / 3) = x / x ^ ((3 : ℝ)⁻¹) := by
    have h : (2 : ℝ) / 3 = 1 - (3 : ℝ)⁻¹ := by norm_num
    rw [h, Real.rpow_sub hxpos, Real.rpow_one]
  rw [hx23]
  rw [div_le_div_iff₀ (by positivity : 0 < x ^ ((3 : ℝ)⁻¹)) (by norm_num : (0 : ℝ) < 5)]
  nlinarith [h5]

/-- `log x ≤ (2/3)√x` for `x ≥ 128`. -/
lemma far_log_le_two_thirds_sqrt {x : ℝ} (hx : 128 ≤ x) : Real.log x ≤ (2 / 3 : ℝ) * Real.sqrt x := by
  by_cases h256 : x ≥ 256
  · exact log_le_two_thirds_sqrt h256
  · -- 128 ≤ x < 256 : ln x ≤ ln 256 = 8 ln 2 ≤ 8·(5/6) = 20/3 ≤ (2/3)·√x
    have hxlt : x < 256 := by linarith
    have hlog : Real.log x ≤ (20 : ℝ) / 3 := by
      have hle1 : Real.log x ≤ Real.log 256 := Real.log_le_log (by linarith : (0 : ℝ) < x) (le_of_lt hxlt)
      have h256 : Real.log 256 ≤ (20 : ℝ) / 3 := by
        rw [show (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) by norm_num, Real.log_pow]
        nlinarith [log_two_le_five_sixths]
      exact hle1.trans h256
    have hsqrt : (20 : ℝ) / 3 ≤ (2 / 3 : ℝ) * Real.sqrt x := by
      have hxr : Real.sqrt 128 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
      have h10 : (10 : ℝ) ≤ Real.sqrt 128 := by
        have : Real.sqrt 100 ≤ Real.sqrt 128 := Real.sqrt_le_sqrt (by norm_num : (100 : ℝ) ≤ 128)
        norm_num at this
        exact this
      nlinarith
    linarith

/-- The far-region log-gap function:
`farG(K,u) = K·log(u/(4K)) − log4·(√u + u^{1/3} + u^{1/5}) − u^{1/4}log u − (2/3)u^{1/6}log u − (2/5)u^{1/10}log u`. -/
noncomputable def farG (K u : ℝ) : ℝ :=
  K * Real.log (u / (4 * K))
    - Real.log 4 * (Real.sqrt u + u ^ ((3 : ℝ)⁻¹) + u ^ ((5 : ℝ)⁻¹))
    - u ^ ((4 : ℝ)⁻¹) * Real.log u
    - (2 / 3) * (u ^ ((6 : ℝ)⁻¹) * Real.log u)
    - (2 / 5) * (u ^ ((10 : ℝ)⁻¹) * Real.log u)

/-- First derivative of `farG` (for `u > 0`, `K > 0`). -/
noncomputable def farD (K u : ℝ) : ℝ :=
  K / u
    - Real.log 4 * (1 / (2 * Real.sqrt u) + ((3 : ℝ)⁻¹) * u ^ (((3 : ℝ)⁻¹) - 1)
        + ((5 : ℝ)⁻¹) * u ^ (((5 : ℝ)⁻¹) - 1))
    - (((4 : ℝ)⁻¹) * u ^ (((4 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1))
    - (2 / 3) * (((6 : ℝ)⁻¹) * u ^ (((6 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1))
    - (2 / 5) * (((10 : ℝ)⁻¹) * u ^ (((10 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1))

/-- `deriv (farG K ·) u = farD K u` for `u > 0`, `K > 0`. -/
lemma deriv_farG_eq_farD {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    deriv (fun x : ℝ => farG K x) u = farD K u := by
  have hA : HasDerivAt (fun x : ℝ => K * Real.log (x / (4 * K))) (K / u) u := by
    have h1 : HasDerivAt (fun x : ℝ => x / (4 * K)) (1 / (4 * K)) u :=
      (hasDerivAt_id u).div_const (4 * K)
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x / (4 * K))) u⁻¹ u := by
      have hl : HasDerivAt (fun x : ℝ => Real.log (x / (4 * K)))
          (1 / (4 * K) / (u / (4 * K))) u := h1.log (by positivity)
      have hv : K⁻¹ * 4⁻¹ / (u / (4 * K)) = u⁻¹ := by
        field_simp [hK.ne', hu.ne']
      simpa [hv] using hl
    exact h2.const_mul K
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt u)) u :=
    Real.hasDerivAt_sqrt (ne_of_gt hu)
  have hR3 : HasDerivAt (fun x : ℝ => x ^ ((3 : ℝ)⁻¹))
      (((3 : ℝ)⁻¹) * u ^ (((3 : ℝ)⁻¹) - 1)) u :=
    Real.hasDerivAt_rpow_const (x := u) (p := (3 : ℝ)⁻¹) (Or.inl (ne_of_gt hu))
  have hR5 : HasDerivAt (fun x : ℝ => x ^ ((5 : ℝ)⁻¹))
      (((5 : ℝ)⁻¹) * u ^ (((5 : ℝ)⁻¹) - 1)) u :=
    Real.hasDerivAt_rpow_const (x := u) (p := (5 : ℝ)⁻¹) (Or.inl (ne_of_gt hu))
  have hB : HasDerivAt (fun x : ℝ => Real.sqrt x + x ^ ((3 : ℝ)⁻¹) + x ^ ((5 : ℝ)⁻¹))
      (1 / (2 * Real.sqrt u) + ((3 : ℝ)⁻¹) * u ^ (((3 : ℝ)⁻¹) - 1)
        + ((5 : ℝ)⁻¹) * u ^ (((5 : ℝ)⁻¹) - 1)) u :=
    (hs.add hR3).add hR5
  have hB4 : HasDerivAt (fun x : ℝ => Real.log 4 * (Real.sqrt x + x ^ ((3 : ℝ)⁻¹) + x ^ ((5 : ℝ)⁻¹)))
      (Real.log 4 * (1 / (2 * Real.sqrt u) + ((3 : ℝ)⁻¹) * u ^ (((3 : ℝ)⁻¹) - 1)
        + ((5 : ℝ)⁻¹) * u ^ (((5 : ℝ)⁻¹) - 1))) u :=
    hB.const_mul (Real.log 4)
  have hL4 : HasDerivAt (fun x : ℝ => x ^ ((4 : ℝ)⁻¹) * Real.log x)
      (((4 : ℝ)⁻¹) * u ^ (((4 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1)) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := (4 : ℝ)⁻¹) (Or.inl (ne_of_gt hu))
    have hl : HasDerivAt (fun x : ℝ => Real.log x) u⁻¹ u := Real.hasDerivAt_log (ne_of_gt hu)
    have hd := hr.mul hl
    have hval : ((4 : ℝ)⁻¹) * u ^ (((4 : ℝ)⁻¹) - 1) * Real.log u + u ^ ((4 : ℝ)⁻¹) * u⁻¹
        = ((4 : ℝ)⁻¹) * u ^ (((4 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1) := by
      have hu4 : u ^ ((4 : ℝ)⁻¹) = u ^ (((4 : ℝ)⁻¹) - 1) * u := by
        calc
          u ^ ((4 : ℝ)⁻¹) = u ^ ((((4 : ℝ)⁻¹) - 1) + 1) := by congr 1; ring
          _ = u ^ (((4 : ℝ)⁻¹) - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_add hu]
          _ = u ^ (((4 : ℝ)⁻¹) - 1) * u := by rw [Real.rpow_one]
      rw [hu4]
      field_simp [hu.ne']
    rw [hval] at hd
    exact hd
  have hL6 : HasDerivAt (fun x : ℝ => (2 / 3) * (x ^ ((6 : ℝ)⁻¹) * Real.log x))
      ((2 / 3) * (((6 : ℝ)⁻¹) * u ^ (((6 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1))) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := (6 : ℝ)⁻¹) (Or.inl (ne_of_gt hu))
    have hl : HasDerivAt (fun x : ℝ => Real.log x) u⁻¹ u := Real.hasDerivAt_log (ne_of_gt hu)
    have hd := hr.mul hl
    have hval : ((6 : ℝ)⁻¹) * u ^ (((6 : ℝ)⁻¹) - 1) * Real.log u + u ^ ((6 : ℝ)⁻¹) * u⁻¹
        = ((6 : ℝ)⁻¹) * u ^ (((6 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1) := by
      have hu6 : u ^ ((6 : ℝ)⁻¹) = u ^ (((6 : ℝ)⁻¹) - 1) * u := by
        calc
          u ^ ((6 : ℝ)⁻¹) = u ^ ((((6 : ℝ)⁻¹) - 1) + 1) := by congr 1; ring
          _ = u ^ (((6 : ℝ)⁻¹) - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_add hu]
          _ = u ^ (((6 : ℝ)⁻¹) - 1) * u := by rw [Real.rpow_one]
      rw [hu6]
      field_simp [hu.ne']
    rw [hval] at hd
    exact hd.const_mul (2 / 3)
  have hL10 : HasDerivAt (fun x : ℝ => (2 / 5) * (x ^ ((10 : ℝ)⁻¹) * Real.log x))
      ((2 / 5) * (((10 : ℝ)⁻¹) * u ^ (((10 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1))) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := (10 : ℝ)⁻¹) (Or.inl (ne_of_gt hu))
    have hl : HasDerivAt (fun x : ℝ => Real.log x) u⁻¹ u := Real.hasDerivAt_log (ne_of_gt hu)
    have hd := hr.mul hl
    have hval : ((10 : ℝ)⁻¹) * u ^ (((10 : ℝ)⁻¹) - 1) * Real.log u + u ^ ((10 : ℝ)⁻¹) * u⁻¹
        = ((10 : ℝ)⁻¹) * u ^ (((10 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1) := by
      have hu10 : u ^ ((10 : ℝ)⁻¹) = u ^ (((10 : ℝ)⁻¹) - 1) * u := by
        calc
          u ^ ((10 : ℝ)⁻¹) = u ^ ((((10 : ℝ)⁻¹) - 1) + 1) := by congr 1; ring
          _ = u ^ (((10 : ℝ)⁻¹) - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_add hu]
          _ = u ^ (((10 : ℝ)⁻¹) - 1) * u := by rw [Real.rpow_one]
      rw [hu10]
      field_simp [hu.ne']
    rw [hval] at hd
    exact hd.const_mul (2 / 5)
  have hmain : HasDerivAt (fun x : ℝ => farG K x)
      (K / u
        - Real.log 4 * (1 / (2 * Real.sqrt u) + ((3 : ℝ)⁻¹) * u ^ (((3 : ℝ)⁻¹) - 1)
            + ((5 : ℝ)⁻¹) * u ^ (((5 : ℝ)⁻¹) - 1))
        - (((4 : ℝ)⁻¹) * u ^ (((4 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1))
        - (2 / 3) * (((6 : ℝ)⁻¹) * u ^ (((6 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1))
        - (2 / 5) * (((10 : ℝ)⁻¹) * u ^ (((10 : ℝ)⁻¹) - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1))) u := by
    dsimp [farG]
    exact ((((hA.sub hB4).sub hL4).sub hL6).sub hL10)
  simpa [farD] using hmain.deriv

/-- Second derivative of `farG` (for `u > 0`, `K > 0`). -/
noncomputable def farD2 (K u : ℝ) : ℝ :=
  - K / u ^ 2
    + Real.log 4 * (((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2)) + ((2 : ℝ) / 9) * u ^ (-((5 : ℝ) / 3))
        + ((4 : ℝ) / 25) * u ^ (-((9 : ℝ) / 5)))
    + ((3 : ℝ) / 16) * u ^ (-((7 : ℝ) / 4)) * Real.log u + (1 / 2) * u ^ (-((7 : ℝ) / 4))
    + ((5 : ℝ) / 54) * u ^ (-((11 : ℝ) / 6)) * Real.log u + ((4 : ℝ) / 9) * u ^ (-((11 : ℝ) / 6))
    + ((9 : ℝ) / 250) * u ^ (-((19 : ℝ) / 10)) * Real.log u + ((8 : ℝ) / 25) * u ^ (-((19 : ℝ) / 10))

/-- `HasDerivAt` of `x ↦ x^p · log x`. -/
lemma hasDerivAt_rpow_mul_log {u p : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => x ^ p * Real.log x)
      (p * u ^ (p - 1) * Real.log u + u ^ (p - 1)) u := by
  have hr := Real.hasDerivAt_rpow_const (x := u) (p := p) (Or.inl (ne_of_gt hu))
  have hl : HasDerivAt (fun x : ℝ => Real.log x) u⁻¹ u := Real.hasDerivAt_log (ne_of_gt hu)
  have hd := hr.mul hl
  have hval : p * u ^ (p - 1) * Real.log u + u ^ p * u⁻¹
      = p * u ^ (p - 1) * Real.log u + u ^ (p - 1) := by
    have hu' : u ^ p = u ^ (p - 1) * u := by
      calc
        u ^ p = u ^ ((p - 1) + 1) := by congr 1; ring
        _ = u ^ (p - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_add hu]
        _ = u ^ (p - 1) * u := by rw [Real.rpow_one]
    rw [hu']
    field_simp [ne_of_gt hu]
  rwa [hval] at hd

/-- `HasDerivAt` of `x ↦ 1/(2√x)`. -/
lemma hasDerivAt_inv_two_sqrt {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x)) (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2))) u := by
  have hrr : (fun x : ℝ => 1 / (2 * Real.sqrt x)) =ᶠ[𝓝 u]
      (fun x : ℝ => (1 / 2) * x ^ (-((1 : ℝ) / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
    have hx0 : (0 : ℝ) < x := by simpa using hx
    rw [Real.sqrt_eq_rpow]
    calc
      1 / (2 * x ^ ((1 : ℝ) / 2)) = (1 / 2) * (x ^ ((1 : ℝ) / 2))⁻¹ := by
        field_simp [ne_of_gt hx0]
      _ = (1 / 2) * x ^ (-((1 : ℝ) / 2)) := by
        rw [Real.rpow_neg hx0.le]
  have hd : HasDerivAt (fun x : ℝ => (1 / 2) * x ^ (-((1 : ℝ) / 2)))
      (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2))) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := -((1 : ℝ) / 2)) (Or.inl (ne_of_gt hu))
    convert hr.const_mul (1 / 2) using 1
    · have h : -((1 : ℝ) / 2) - 1 = -((3 : ℝ) / 2) := by norm_num
      rw [h]
      ring_nf
  exact (hrr.hasDerivAt_iff).mpr hd

/-- Second derivative of `farG`: `deriv^[2] (farG K ·) u = farD2 K u`. -/
lemma deriv2_farG {K u : ℝ} (hK : 0 < K) (hu : 0 < u) :
    deriv^[2] (fun x : ℝ => farG K x) u = farD2 K u := by
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
  have hlocal : (fun x : ℝ => deriv (fun y : ℝ => farG K y) x) =ᶠ[𝓝 u]
      (fun x : ℝ => farD K x) := by
    filter_upwards [hIoi] with x hx
    exact deriv_farG_eq_farD hK hx
  have hdeq : deriv (fun x : ℝ => deriv (fun y : ℝ => farG K y) x) u
      = deriv (fun x : ℝ => farD K x) u := hlocal.deriv_eq
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu.le
  have hD1 : HasDerivAt (fun x : ℝ => K / x) (-K / u ^ 2) u := by
    have hk : HasDerivAt (fun x : ℝ => K) (0 : ℝ) u := hasDerivAt_const u K
    have hid : HasDerivAt (fun x : ℝ => x) (1 : ℝ) u := hasDerivAt_id u
    have hdiv : HasDerivAt (fun x : ℝ => K / x) ((0 * u - K * 1) / u ^ 2) u :=
      hk.div hid (ne_of_gt hu)
    have hv : (0 * u - K * 1) / u ^ 2 = -K / u ^ 2 := by
      field_simp [hu.ne']
      ring
    rw [hv] at hdiv
    exact hdiv
  have hS : HasDerivAt (fun x : ℝ => 1 / (2 * Real.sqrt x)) (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2))) u :=
    hasDerivAt_inv_two_sqrt hu
  have hR3 : HasDerivAt (fun x : ℝ => ((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1))
      (-((2 : ℝ) / 9) * u ^ (-((5 : ℝ) / 3))) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := ((3 : ℝ)⁻¹) - 1) (Or.inl (ne_of_gt hu))
    convert hr.const_mul ((3 : ℝ)⁻¹) using 1
    · have he : ((3 : ℝ)⁻¹) - 1 - 1 = -((5 : ℝ) / 3) := by norm_num
      rw [he]
      norm_num
      ring
  have hR5 : HasDerivAt (fun x : ℝ => ((5 : ℝ)⁻¹) * x ^ (((5 : ℝ)⁻¹) - 1))
      (-((4 : ℝ) / 25) * u ^ (-((9 : ℝ) / 5))) u := by
    have hr := Real.hasDerivAt_rpow_const (x := u) (p := ((5 : ℝ)⁻¹) - 1) (Or.inl (ne_of_gt hu))
    convert hr.const_mul ((5 : ℝ)⁻¹) using 1
    · have he : ((5 : ℝ)⁻¹) - 1 - 1 = -((9 : ℝ) / 5) := by norm_num
      rw [he]
      norm_num
      ring
  have hC1 : HasDerivAt (fun x : ℝ => (1 / (2 * Real.sqrt x)) + ((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1)
        + ((5 : ℝ)⁻¹) * x ^ (((5 : ℝ)⁻¹) - 1))
      (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2)) + (-((2 : ℝ) / 9)) * u ^ (-((5 : ℝ) / 3))
        + (-((4 : ℝ) / 25)) * u ^ (-((9 : ℝ) / 5))) u :=
    (hS.add hR3).add hR5
  have hC2 : HasDerivAt (fun x : ℝ => Real.log 4 * (1 / (2 * Real.sqrt x) + ((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1)
        + ((5 : ℝ)⁻¹) * x ^ (((5 : ℝ)⁻¹) - 1)))
      (Real.log 4 * (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2)) + (-((2 : ℝ) / 9)) * u ^ (-((5 : ℝ) / 3))
        + (-((4 : ℝ) / 25)) * u ^ (-((9 : ℝ) / 5)))) u :=
    hC1.const_mul (Real.log 4)
  have hL4' : HasDerivAt (fun x : ℝ => ((4 : ℝ)⁻¹) * x ^ (((4 : ℝ)⁻¹) - 1) * Real.log x + x ^ (((4 : ℝ)⁻¹) - 1))
      (-((3 : ℝ) / 16) * u ^ (-((7 : ℝ) / 4)) * Real.log u - (1 / 2) * u ^ (-((7 : ℝ) / 4))) u := by
    have h1 := hasDerivAt_rpow_mul_log (u := u) (p := ((4 : ℝ)⁻¹) - 1) hu
    have h1c : HasDerivAt (fun x : ℝ => ((4 : ℝ)⁻¹) * (x ^ (((4 : ℝ)⁻¹) - 1) * Real.log x))
        (((4 : ℝ)⁻¹) * ((((4 : ℝ)⁻¹) - 1) * u ^ (((4 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1 - 1))) u :=
      h1.const_mul ((4 : ℝ)⁻¹)
    have h2 : HasDerivAt (fun x : ℝ => x ^ (((4 : ℝ)⁻¹) - 1))
        ((((4 : ℝ)⁻¹) - 1) * u ^ (((4 : ℝ)⁻¹) - 1 - 1)) u :=
      Real.hasDerivAt_rpow_const (x := u) (p := ((4 : ℝ)⁻¹) - 1) (Or.inl (ne_of_gt hu))
    have hsum : HasDerivAt (fun x : ℝ => ((4 : ℝ)⁻¹) * (x ^ (((4 : ℝ)⁻¹) - 1) * Real.log x) + x ^ (((4 : ℝ)⁻¹) - 1))
        (((4 : ℝ)⁻¹) * ((((4 : ℝ)⁻¹) - 1) * u ^ (((4 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((4 : ℝ)⁻¹) - 1 - 1))
          + (((4 : ℝ)⁻¹) - 1) * u ^ (((4 : ℝ)⁻¹) - 1 - 1)) u :=
      h1c.add h2
    convert hsum using 1
    · funext x
      ring
    · have he : ((4 : ℝ)⁻¹) - 1 - 1 = -((7 : ℝ) / 4) := by norm_num
      rw [he]
      norm_num
      ring
  have hL6' : HasDerivAt (fun x : ℝ => (2 / 3) * (((6 : ℝ)⁻¹) * x ^ (((6 : ℝ)⁻¹) - 1) * Real.log x + x ^ (((6 : ℝ)⁻¹) - 1)))
      (-((5 : ℝ) / 54) * u ^ (-((11 : ℝ) / 6)) * Real.log u - ((4 : ℝ) / 9) * u ^ (-((11 : ℝ) / 6))) u := by
    have h1 := hasDerivAt_rpow_mul_log (u := u) (p := ((6 : ℝ)⁻¹) - 1) hu
    have h1c : HasDerivAt (fun x : ℝ => ((6 : ℝ)⁻¹) * (x ^ (((6 : ℝ)⁻¹) - 1) * Real.log x))
        (((6 : ℝ)⁻¹) * ((((6 : ℝ)⁻¹) - 1) * u ^ (((6 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1 - 1))) u :=
      h1.const_mul ((6 : ℝ)⁻¹)
    have h2 : HasDerivAt (fun x : ℝ => x ^ (((6 : ℝ)⁻¹) - 1))
        ((((6 : ℝ)⁻¹) - 1) * u ^ (((6 : ℝ)⁻¹) - 1 - 1)) u :=
      Real.hasDerivAt_rpow_const (x := u) (p := ((6 : ℝ)⁻¹) - 1) (Or.inl (ne_of_gt hu))
    have hsum : HasDerivAt (fun x : ℝ => ((6 : ℝ)⁻¹) * (x ^ (((6 : ℝ)⁻¹) - 1) * Real.log x) + x ^ (((6 : ℝ)⁻¹) - 1))
        (((6 : ℝ)⁻¹) * ((((6 : ℝ)⁻¹) - 1) * u ^ (((6 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((6 : ℝ)⁻¹) - 1 - 1))
          + (((6 : ℝ)⁻¹) - 1) * u ^ (((6 : ℝ)⁻¹) - 1 - 1)) u :=
      h1c.add h2
    convert (hsum.const_mul (2 / 3)) using 1
    · funext x
      ring
    · have he : ((6 : ℝ)⁻¹) - 1 - 1 = -((11 : ℝ) / 6) := by norm_num
      rw [he]
      norm_num
      ring
  have hL10' : HasDerivAt (fun x : ℝ => (2 / 5) * (((10 : ℝ)⁻¹) * x ^ (((10 : ℝ)⁻¹) - 1) * Real.log x + x ^ (((10 : ℝ)⁻¹) - 1)))
      (-((9 : ℝ) / 250) * u ^ (-((19 : ℝ) / 10)) * Real.log u - ((8 : ℝ) / 25) * u ^ (-((19 : ℝ) / 10))) u := by
    have h1 := hasDerivAt_rpow_mul_log (u := u) (p := ((10 : ℝ)⁻¹) - 1) hu
    have h1c : HasDerivAt (fun x : ℝ => ((10 : ℝ)⁻¹) * (x ^ (((10 : ℝ)⁻¹) - 1) * Real.log x))
        (((10 : ℝ)⁻¹) * ((((10 : ℝ)⁻¹) - 1) * u ^ (((10 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1 - 1))) u :=
      h1.const_mul ((10 : ℝ)⁻¹)
    have h2 : HasDerivAt (fun x : ℝ => x ^ (((10 : ℝ)⁻¹) - 1))
        ((((10 : ℝ)⁻¹) - 1) * u ^ (((10 : ℝ)⁻¹) - 1 - 1)) u :=
      Real.hasDerivAt_rpow_const (x := u) (p := ((10 : ℝ)⁻¹) - 1) (Or.inl (ne_of_gt hu))
    have hsum : HasDerivAt (fun x : ℝ => ((10 : ℝ)⁻¹) * (x ^ (((10 : ℝ)⁻¹) - 1) * Real.log x) + x ^ (((10 : ℝ)⁻¹) - 1))
        (((10 : ℝ)⁻¹) * ((((10 : ℝ)⁻¹) - 1) * u ^ (((10 : ℝ)⁻¹) - 1 - 1) * Real.log u + u ^ (((10 : ℝ)⁻¹) - 1 - 1))
          + (((10 : ℝ)⁻¹) - 1) * u ^ (((10 : ℝ)⁻¹) - 1 - 1)) u :=
      h1c.add h2
    convert (hsum.const_mul (2 / 5)) using 1
    · funext x
      ring
    · have he : ((10 : ℝ)⁻¹) - 1 - 1 = -((19 : ℝ) / 10) := by norm_num
      rw [he]
      norm_num
      ring
  have hsub : HasDerivAt (fun x : ℝ => farD K x)
      (-K / u ^ 2 - Real.log 4 * (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2)) + -((2 : ℝ) / 9) * u ^ (-((5 : ℝ) / 3))
        + -((4 : ℝ) / 25) * u ^ (-((9 : ℝ) / 5)))
        - (-((3 : ℝ) / 16) * u ^ (-((7 : ℝ) / 4)) * Real.log u - (1 / 2) * u ^ (-((7 : ℝ) / 4)))
        - (-((5 : ℝ) / 54) * u ^ (-((11 : ℝ) / 6)) * Real.log u - ((4 : ℝ) / 9) * u ^ (-((11 : ℝ) / 6)))
        - (-((9 : ℝ) / 250) * u ^ (-((19 : ℝ) / 10)) * Real.log u - ((8 : ℝ) / 25) * u ^ (-((19 : ℝ) / 10)))) u := by
    convert ((((hD1.sub hC2).sub hL4').sub hL6').sub hL10') using 1
    · funext x
      dsimp [farD]
  have hval : (-K / u ^ 2 - Real.log 4 * (-((1 : ℝ) / 4) * u ^ (-((3 : ℝ) / 2)) + -((2 : ℝ) / 9) * u ^ (-((5 : ℝ) / 3))
        + -((4 : ℝ) / 25) * u ^ (-((9 : ℝ) / 5)))
        - (-((3 : ℝ) / 16) * u ^ (-((7 : ℝ) / 4)) * Real.log u - (1 / 2) * u ^ (-((7 : ℝ) / 4)))
        - (-((5 : ℝ) / 54) * u ^ (-((11 : ℝ) / 6)) * Real.log u - ((4 : ℝ) / 9) * u ^ (-((11 : ℝ) / 6)))
        - (-((9 : ℝ) / 250) * u ^ (-((19 : ℝ) / 10)) * Real.log u - ((8 : ℝ) / 25) * u ^ (-((19 : ℝ) / 10)))) = farD2 K u := by
    dsimp [farD2]
    field_simp [ne_of_gt hu]
    ring_nf
  rw [hval] at hsub
  have hfinal : deriv (fun x : ℝ => deriv (fun y : ℝ => farG K y) x) u = farD2 K u := by
    rw [hdeq]
    exact hsub.deriv
  simpa [Function.iterate_succ_apply'] using hfinal

/-! ### Power bounds for the far second-derivative negativity -/

/-- `x^a ≤ x/b` whenever `b ≤ x^(1-a)`, `0 < x`, `0 < b`. -/
lemma rpow_le_self_div {x : ℝ} (hx : 0 < x) (a b : ℝ) (hb : 0 < b) (h : b ≤ x ^ (1 - a)) :
    x ^ a ≤ x / b := by
  have hxsub : x ^ a = x / x ^ (1 - a) := by
    calc
      x ^ a = x ^ (1 - (1 - a)) := by
        apply congrArg
        ring
      _ = x ^ (1 : ℝ) / x ^ (1 - a) := by rw [Real.rpow_sub hx]
      _ = x / x ^ (1 - a) := by rw [Real.rpow_one]
  rw [hxsub]
  rw [div_le_div_iff₀ (by positivity : 0 < x ^ (1 - a)) hb]
  exact mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ x)

/-- `x^(2/5) ≤ x/16` for `x ≥ 128`. -/
lemma rpow_two_fifths_le_div_sixteen {x : ℝ} (hx : 128 ≤ x) : x ^ ((2 : ℝ) / 5) ≤ x / 16 := by
  refine rpow_le_self_div (by linarith : 0 < x) ((2 : ℝ) / 5) 16 (by norm_num) ?_
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hx (by norm_num : (0 : ℝ) ≤ 1 - (2 : ℝ) / 5)
  have h128 : (128 : ℝ) ^ (1 - (2 : ℝ) / 5) = 2 ^ ((21 : ℝ) / 5) := by
    have he : 1 - (2 : ℝ) / 5 = (3 : ℝ) / 5 := by norm_num
    rw [he]
    rw [show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h16 : (16 : ℝ) ≤ 2 ^ ((21 : ℝ) / 5) := by
    have hsum : (21 : ℝ) / 5 = 4 + (1 : ℝ) / 5 := by norm_num
    rw [hsum, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by
      norm_num [Real.rpow_natCast]
    rw [h4]
    have h15 : (1 : ℝ) ≤ 2 ^ ((1 : ℝ) / 5) := by
      have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
      rwa [Real.one_rpow] at hp
    nlinarith
  have hxr : 2 ^ ((21 : ℝ) / 5) ≤ x ^ (1 - (2 : ℝ) / 5) := by rwa [h128] at hpow
  exact le_trans h16 hxr

/-- `x^(1/3) ≤ (1/2)√x` for `x ≥ 64`. -/
lemma rpow_third_le_half_sqrt {x : ℝ} (hx : 64 ≤ x) : x ^ ((1 : ℝ) / 3) ≤ (1 / 2) * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hxneg : x ^ (-((1 : ℝ) / 6)) ≤ 1 / 2 := by
    have hx6 : (2 : ℝ) ≤ x ^ ((1 : ℝ) / 6) := by
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 64) hx (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 6)
      have h64 : (64 : ℝ) ^ ((1 : ℝ) / 6) = 2 := by
        rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rwa [h64] at hpow
    have hinv : (x ^ ((1 : ℝ) / 6))⁻¹ ≤ (1 / 2 : ℝ) := by
      have hle : (x ^ ((1 : ℝ) / 6))⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by positivity : 0 < x ^ ((1 : ℝ) / 6)) (by norm_num : (0 : ℝ) < 2)).mpr hx6
      simpa using hle
    have hxneg' : x ^ (-((1 : ℝ) / 6)) = (x ^ ((1 : ℝ) / 6))⁻¹ := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ x) ((1 : ℝ) / 6)]
    rwa [← hxneg'] at hinv
  have hx13 : x ^ ((1 : ℝ) / 3) = Real.sqrt x * x ^ (-((1 : ℝ) / 6)) := by
    have h : (1 : ℝ) / 2 - 1 / 6 = (1 : ℝ) / 3 := by norm_num
    rw [← h]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_add hx0]
    congr 1
  rw [hx13]
  have hsqpos : 0 ≤ Real.sqrt x := by positivity
  nlinarith

/-- `x^(1/5) ≤ x/8` for `x ≥ 128`. -/
lemma rpow_fifth_le_div_eight {x : ℝ} (hx : 128 ≤ x) : x ^ ((1 : ℝ) / 5) ≤ x / 8 := by
  refine rpow_le_self_div (by linarith : 0 < x) ((1 : ℝ) / 5) 8 (by norm_num) ?_
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hx (by norm_num : (0 : ℝ) ≤ 1 - (1 : ℝ) / 5)
  have h128 : (128 : ℝ) ^ (1 - (1 : ℝ) / 5) = 2 ^ ((28 : ℝ) / 5) := by
    have he : 1 - (1 : ℝ) / 5 = (4 : ℝ) / 5 := by norm_num
    rw [he]
    rw [show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h8 : (8 : ℝ) ≤ 2 ^ ((28 : ℝ) / 5) := by
    have hsum : (28 : ℝ) / 5 = 5 + (3 : ℝ) / 5 := by norm_num
    rw [hsum, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h5 : (2 : ℝ) ^ (5 : ℝ) = 32 := by
      norm_num [Real.rpow_natCast]
    rw [h5]
    have h35 : (1 : ℝ) ≤ 2 ^ ((3 : ℝ) / 5) := by
      have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 5)
      rwa [Real.one_rpow] at hp
    nlinarith
  have hxr : 2 ^ ((28 : ℝ) / 5) ≤ x ^ (1 - (1 : ℝ) / 5) := by rwa [h128] at hpow
  exact le_trans h8 hxr

/-- `u^(a-2) = u^a/u^2` for `0 < u`. -/
lemma rpow_sub_two_div {u a : ℝ} (hu : 0 < u) : u ^ (a - (2 : ℝ)) = u ^ a / u ^ 2 := by
  calc
    u ^ (a - (2 : ℝ)) = u ^ a / u ^ (2 : ℝ) := by rw [Real.rpow_sub hu]
    _ = u ^ a / u ^ 2 := by
      congr 1
      exact Real.rpow_natCast (x := u) (n := 2)

/-- `farD2(K,u) < 0` on `[16K, K²]` for `K ≥ 128`: `farG` is strictly concave there. -/
lemma deriv2_farG_neg {K u : ℝ} (hK128 : 128 ≤ K) (h16 : 16 * K ≤ u) (hu2 : u ≤ K * K) :
    deriv^[2] (fun x : ℝ => farG K x) u < 0 := by
  have hK : 0 < K := by linarith
  have hu : 0 < u := by linarith
  have hKpos : 0 ≤ K := hK.le
  have hupos : 0 ≤ u := hu.le
  have hu2pos : 0 < u ^ 2 := by positivity
  have h64 : 64 ≤ K := by linarith
  have h125 : 125 ≤ K := by linarith
  have hlg : Real.log K ≤ (2 / 3 : ℝ) * Real.sqrt K := far_log_le_two_thirds_sqrt hK128
  have hlg2 : 2 * Real.log K ≤ (4 / 3 : ℝ) * Real.sqrt K := by nlinarith
  have hlg_nonneg : 0 ≤ Real.log K := Real.log_nonneg (by linarith : 1 ≤ K)
  have hlogu_nonneg : 0 ≤ Real.log u := Real.log_nonneg (by linarith : 1 ≤ u)
  have hlnu : Real.log u ≤ 2 * Real.log K := by
    have hle : Real.log u ≤ Real.log (K * K) := Real.log_le_log (by linarith : 0 < u) hu2
    have hKK : Real.log (K * K) = 2 * Real.log K := by
      rw [Real.log_mul (ne_of_gt hK) (ne_of_gt hK)]
      ring
    rwa [hKK] at hle
  -- u-powers bounded by K-powers (u ≤ K²)
  have h12 : u ^ ((1 : ℝ) / 2) ≤ K := by
    have h' : u ^ ((1 : ℝ) / 2) ≤ (K * K) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    have hKK : (K * K) ^ ((1 : ℝ) / 2) = K := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  have h14 : u ^ ((1 : ℝ) / 4) ≤ K ^ ((1 : ℝ) / 2) := by
    have h' : u ^ ((1 : ℝ) / 4) ≤ (K * K) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
    have hKK : (K * K) ^ ((1 : ℝ) / 4) = K ^ ((1 : ℝ) / 2) := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  have h16p : u ^ ((1 : ℝ) / 6) ≤ K ^ ((1 : ℝ) / 3) := by
    have h' : u ^ ((1 : ℝ) / 6) ≤ (K * K) ^ ((1 : ℝ) / 6) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 6)
    have hKK : (K * K) ^ ((1 : ℝ) / 6) = K ^ ((1 : ℝ) / 3) := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  have h110 : u ^ ((1 : ℝ) / 10) ≤ K ^ ((1 : ℝ) / 5) := by
    have h' : u ^ ((1 : ℝ) / 10) ≤ (K * K) ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
    have hKK : (K * K) ^ ((1 : ℝ) / 10) = K ^ ((1 : ℝ) / 5) := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  have h13 : u ^ ((1 : ℝ) / 3) ≤ K ^ ((2 : ℝ) / 3) := by
    have h' : u ^ ((1 : ℝ) / 3) ≤ (K * K) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
    have hKK : (K * K) ^ ((1 : ℝ) / 3) = K ^ ((2 : ℝ) / 3) := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  have h15 : u ^ ((1 : ℝ) / 5) ≤ K ^ ((2 : ℝ) / 5) := by
    have h' : u ^ ((1 : ℝ) / 5) ≤ (K * K) ^ ((1 : ℝ) / 5) :=
      Real.rpow_le_rpow hupos hu2 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 5)
    have hKK : (K * K) ^ ((1 : ℝ) / 5) = K ^ ((2 : ℝ) / 5) := by
      rw [show K * K = K ^ 2 by ring, ← Real.rpow_natCast, ← Real.rpow_mul hKpos]
      norm_num
    rwa [hKK] at h'
  -- K-power bounds
  have hK12_le : K ^ ((1 : ℝ) / 2) ≤ K / 8 := by
    have h := sqrt_le_eighth_self h64
    rwa [Real.sqrt_eq_rpow] at h
  have hK13_half : K ^ ((1 : ℝ) / 3) ≤ (1 / 2) * Real.sqrt K := rpow_third_le_half_sqrt h64
  have hK12_sqrt : Real.sqrt K ≤ K / 8 := sqrt_le_eighth_self h64
  have hK13_sixteenth : K ^ ((1 : ℝ) / 3) ≤ K / 16 := by
    calc
      K ^ ((1 : ℝ) / 3) ≤ (1 / 2) * Real.sqrt K := hK13_half
      _ ≤ (1 / 2) * (K / 8) := by
        exact mul_le_mul_of_nonneg_left hK12_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = K / 16 := by norm_num; ring
  have hK15_eighth : K ^ ((1 : ℝ) / 5) ≤ K / 8 := rpow_fifth_le_div_eight hK128
  have hK13_log : K ^ ((1 : ℝ) / 3) * (2 * Real.log K) ≤ (2 / 3 : ℝ) * K := by
    calc
      K ^ ((1 : ℝ) / 3) * (2 * Real.log K) ≤ ((1 / 2) * Real.sqrt K) * (2 * Real.log K) := by
        exact mul_le_mul_of_nonneg_right hK13_half (by nlinarith)
      _ ≤ ((1 / 2) * Real.sqrt K) * ((4 / 3 : ℝ) * Real.sqrt K) := by
        exact mul_le_mul_of_nonneg_left hlg2 (by positivity : 0 ≤ (1 / 2) * Real.sqrt K)
      _ = (2 / 3 : ℝ) * K := by
        ring_nf
        rw [Real.sq_sqrt hKpos]
  have hK15_log : K ^ ((1 : ℝ) / 5) * (2 * Real.log K) ≤ (1 / 3 : ℝ) * K := by
    have h1 : K ^ ((1 : ℝ) / 5) * (2 * Real.log K) ≤ K ^ ((1 : ℝ) / 5) * ((4 / 3 : ℝ) * Real.sqrt K) := by
      exact mul_le_mul_of_nonneg_left hlg2 (by positivity : 0 ≤ K ^ ((1 : ℝ) / 5))
    have h2 : K ^ ((1 : ℝ) / 5) * ((4 / 3 : ℝ) * Real.sqrt K) ≤ (1 / 3 : ℝ) * K := by
      have hdec : K ^ ((1 : ℝ) / 5) * Real.sqrt K = K ^ ((7 : ℝ) / 10) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hK]
        congr 1
        norm_num
      have h710 : K ^ ((7 : ℝ) / 10) ≤ K / 4 := by
        refine rpow_le_self_div (by linarith : 0 < K) ((7 : ℝ) / 10) 4 (by norm_num) ?_
        have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 128) hK128 (by norm_num : (0 : ℝ) ≤ 1 - (7 : ℝ) / 10)
        have he : 1 - (7 : ℝ) / 10 = (3 : ℝ) / 10 := by norm_num
        have h128 : (128 : ℝ) ^ (1 - (7 : ℝ) / 10) = 2 ^ ((21 : ℝ) / 10) := by
          rw [he]
          rw [show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num]
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        have h4 : (4 : ℝ) ≤ 2 ^ ((21 : ℝ) / 10) := by
          have hsum : (21 : ℝ) / 10 = 2 + (1 : ℝ) / 10 := by norm_num
          rw [hsum, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          have h4' : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
          rw [h4']
          have h110' : (1 : ℝ) ≤ 2 ^ ((1 : ℝ) / 10) := by
            have hp1 := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
              (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 10)
            rwa [Real.one_rpow ((1 : ℝ) / 10)] at hp1
          nlinarith
        have hxr : 2 ^ ((21 : ℝ) / 10) ≤ K ^ (1 - (7 : ℝ) / 10) := by rwa [h128] at hp
        exact le_trans h4 hxr
      calc
        K ^ ((1 : ℝ) / 5) * ((4 / 3 : ℝ) * Real.sqrt K) = (4 / 3 : ℝ) * (K ^ ((1 : ℝ) / 5) * Real.sqrt K) := by ring
        _ = (4 / 3 : ℝ) * K ^ ((7 : ℝ) / 10) := by rw [hdec]
        _ ≤ (4 / 3 : ℝ) * (K / 4) := by
          exact mul_le_mul_of_nonneg_left h710 (by norm_num : (0 : ℝ) ≤ 4 / 3)
        _ = (1 / 3 : ℝ) * K := by norm_num; ring
    exact h1.trans h2
  -- term bounds (each ≤ constant · K/u²)
  have hd32 : u ^ (-((3 : ℝ) / 2)) = u ^ ((1 : ℝ) / 2) / u ^ 2 := by
    have ha : -((3 : ℝ) / 2) = (1 : ℝ) / 2 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 2)) hu
  have hd53 : u ^ (-((5 : ℝ) / 3)) = u ^ ((1 : ℝ) / 3) / u ^ 2 := by
    have ha : -((5 : ℝ) / 3) = (1 : ℝ) / 3 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 3)) hu
  have hd95 : u ^ (-((9 : ℝ) / 5)) = u ^ ((1 : ℝ) / 5) / u ^ 2 := by
    have ha : -((9 : ℝ) / 5) = (1 : ℝ) / 5 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 5)) hu
  have hd74 : u ^ (-((7 : ℝ) / 4)) = u ^ ((1 : ℝ) / 4) / u ^ 2 := by
    have ha : -((7 : ℝ) / 4) = (1 : ℝ) / 4 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 4)) hu
  have hd116 : u ^ (-((11 : ℝ) / 6)) = u ^ ((1 : ℝ) / 6) / u ^ 2 := by
    have ha : -((11 : ℝ) / 6) = (1 : ℝ) / 6 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 6)) hu
  have hd1910 : u ^ (-((19 : ℝ) / 10)) = u ^ ((1 : ℝ) / 10) / u ^ 2 := by
    have ha : -((19 : ℝ) / 10) = (1 : ℝ) / 10 - (2 : ℝ) := by norm_num
    rw [ha]
    exact rpow_sub_two_div (u := u) (a := ((1 : ℝ) / 10)) hu
  have hdiv {a b : ℝ} (hab : a ≤ b) : a / u ^ 2 ≤ b / u ^ 2 := by
    exact div_le_div_of_nonneg_right hab (by positivity : 0 ≤ u ^ 2)
  rw [deriv2_farG hK hu]
  -- Now bound farD2 < 0
  have c1 : (1 / 4 : ℝ) * Real.log 4 * u ^ (-((3 : ℝ) / 2)) ≤ (1 / 4 : ℝ) * Real.log 4 * (K / u ^ 2) := by
    rw [hd32]
    exact mul_le_mul_of_nonneg_left (hdiv h12) (by positivity : 0 ≤ (1 / 4) * Real.log 4)
  have c2 : (2 / 9 : ℝ) * Real.log 4 * u ^ (-((5 : ℝ) / 3)) ≤ (2 / 45 : ℝ) * Real.log 4 * (K / u ^ 2) := by
    rw [hd53]
    have h : (2 / 9 : ℝ) * Real.log 4 * (u ^ ((1 : ℝ) / 3) / u ^ 2) ≤ (2 / 9 : ℝ) * Real.log 4 * (K / 5 / u ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hdiv (h13.trans (rpow_two_thirds_le_div_five h125)))
        (by positivity : 0 ≤ (2 / 9) * Real.log 4)
    have heq : (2 / 9 : ℝ) * Real.log 4 * (K / 5 / u ^ 2) = (2 / 45 : ℝ) * Real.log 4 * (K / u ^ 2) := by
      ring
    rwa [heq] at h
  have c3 : (4 / 25 : ℝ) * Real.log 4 * u ^ (-((9 : ℝ) / 5)) ≤ (1 / 100 : ℝ) * Real.log 4 * (K / u ^ 2) := by
    rw [hd95]
    have h : (4 / 25 : ℝ) * Real.log 4 * (u ^ ((1 : ℝ) / 5) / u ^ 2) ≤ (4 / 25 : ℝ) * Real.log 4 * (K / 16 / u ^ 2) := by
      exact mul_le_mul_of_nonneg_left (hdiv (h15.trans (rpow_two_fifths_le_div_sixteen hK128)))
        (by positivity : 0 ≤ (4 / 25) * Real.log 4)
    have heq : (4 / 25 : ℝ) * Real.log 4 * (K / 16 / u ^ 2) = (1 / 100 : ℝ) * Real.log 4 * (K / u ^ 2) := by
      ring
    rwa [heq] at h
  have c4 : (3 / 16 : ℝ) * u ^ (-((7 : ℝ) / 4)) * Real.log u ≤ (1 / 4 : ℝ) * (K / u ^ 2) := by
    rw [hd74]
    have hle : u ^ ((1 : ℝ) / 4) * Real.log u ≤ K ^ ((1 : ℝ) / 2) * (2 * Real.log K) := by
      calc
        u ^ ((1 : ℝ) / 4) * Real.log u ≤ K ^ ((1 : ℝ) / 2) * Real.log u := by
          exact mul_le_mul_of_nonneg_right h14 hlogu_nonneg
        _ ≤ K ^ ((1 : ℝ) / 2) * (2 * Real.log K) := by
          exact mul_le_mul_of_nonneg_left hlnu (by positivity : 0 ≤ K ^ ((1 : ℝ) / 2))
    have hK12_log : K ^ ((1 : ℝ) / 2) * (2 * Real.log K) ≤ (4 / 3 : ℝ) * K := by
      calc
        K ^ ((1 : ℝ) / 2) * (2 * Real.log K) = Real.sqrt K * (2 * Real.log K) := by rw [Real.sqrt_eq_rpow]
        _ ≤ Real.sqrt K * ((4 / 3 : ℝ) * Real.sqrt K) := by
          exact mul_le_mul_of_nonneg_left hlg2 (by positivity : 0 ≤ Real.sqrt K)
        _ = (4 / 3 : ℝ) * K := by
          ring_nf
          rw [Real.sq_sqrt hKpos]
    have hmain : (3 / 16 : ℝ) * (u ^ ((1 : ℝ) / 4) / u ^ 2) * Real.log u ≤ (1 / 4 : ℝ) * (K / u ^ 2) := by
      have hnum : u ^ ((1 : ℝ) / 4) * Real.log u ≤ (4 / 3 : ℝ) * K := hle.trans hK12_log
      have hdiv' : (u ^ ((1 : ℝ) / 4) * Real.log u) / u ^ 2 ≤ ((4 / 3 : ℝ) * K) / u ^ 2 := hdiv hnum
      have h2 : (3 / 16 : ℝ) * (((4 / 3 : ℝ) * K) / u ^ 2) = (1 / 4 : ℝ) * (K / u ^ 2) := by ring
      calc
        (3 / 16 : ℝ) * (u ^ ((1 : ℝ) / 4) / u ^ 2) * Real.log u = (3 / 16 : ℝ) * ((u ^ ((1 : ℝ) / 4) * Real.log u) / u ^ 2) := by ring
        _ ≤ (3 / 16 : ℝ) * (((4 / 3 : ℝ) * K) / u ^ 2) := by
          exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 3 / 16)
        _ = (1 / 4 : ℝ) * (K / u ^ 2) := h2
    exact hmain
  have c5 : (5 / 54 : ℝ) * u ^ (-((11 : ℝ) / 6)) * Real.log u ≤ (5 / 81 : ℝ) * (K / u ^ 2) := by
    rw [hd116]
    have hnum : u ^ ((1 : ℝ) / 6) * Real.log u ≤ K ^ ((1 : ℝ) / 3) * (2 * Real.log K) := by
      calc
        u ^ ((1 : ℝ) / 6) * Real.log u ≤ K ^ ((1 : ℝ) / 3) * Real.log u := by
          exact mul_le_mul_of_nonneg_right h16p hlogu_nonneg
        _ ≤ K ^ ((1 : ℝ) / 3) * (2 * Real.log K) := by
          exact mul_le_mul_of_nonneg_left hlnu (by positivity : 0 ≤ K ^ ((1 : ℝ) / 3))
    have hK13l : K ^ ((1 : ℝ) / 3) * (2 * Real.log K) ≤ (2 / 3 : ℝ) * K := hK13_log
    have hdiv' : (u ^ ((1 : ℝ) / 6) * Real.log u) / u ^ 2 ≤ ((2 / 3 : ℝ) * K) / u ^ 2 := hdiv (hnum.trans hK13l)
    have heq : (5 / 54 : ℝ) * (((2 / 3 : ℝ) * K) / u ^ 2) = (5 / 81 : ℝ) * (K / u ^ 2) := by ring
    calc
      (5 / 54 : ℝ) * (u ^ ((1 : ℝ) / 6) / u ^ 2) * Real.log u = (5 / 54 : ℝ) * ((u ^ ((1 : ℝ) / 6) * Real.log u) / u ^ 2) := by ring
      _ ≤ (5 / 54 : ℝ) * (((2 / 3 : ℝ) * K) / u ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 5 / 54)
      _ = (5 / 81 : ℝ) * (K / u ^ 2) := heq
  have c6 : (9 / 250 : ℝ) * u ^ (-((19 : ℝ) / 10)) * Real.log u ≤ (3 / 250 : ℝ) * (K / u ^ 2) := by
    rw [hd1910]
    have hnum : u ^ ((1 : ℝ) / 10) * Real.log u ≤ K ^ ((1 : ℝ) / 5) * (2 * Real.log K) := by
      calc
        u ^ ((1 : ℝ) / 10) * Real.log u ≤ K ^ ((1 : ℝ) / 5) * Real.log u := by
          exact mul_le_mul_of_nonneg_right h110 hlogu_nonneg
        _ ≤ K ^ ((1 : ℝ) / 5) * (2 * Real.log K) := by
          exact mul_le_mul_of_nonneg_left hlnu (by positivity : 0 ≤ K ^ ((1 : ℝ) / 5))
    have hK15l : K ^ ((1 : ℝ) / 5) * (2 * Real.log K) ≤ (1 / 3 : ℝ) * K := hK15_log
    have hdiv' : (u ^ ((1 : ℝ) / 10) * Real.log u) / u ^ 2 ≤ ((1 / 3 : ℝ) * K) / u ^ 2 := hdiv (hnum.trans hK15l)
    have heq : (9 / 250 : ℝ) * (((1 / 3 : ℝ) * K) / u ^ 2) = (3 / 250 : ℝ) * (K / u ^ 2) := by ring
    calc
      (9 / 250 : ℝ) * (u ^ ((1 : ℝ) / 10) / u ^ 2) * Real.log u = (9 / 250 : ℝ) * ((u ^ ((1 : ℝ) / 10) * Real.log u) / u ^ 2) := by ring
      _ ≤ (9 / 250 : ℝ) * (((1 / 3 : ℝ) * K) / u ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 9 / 250)
      _ = (3 / 250 : ℝ) * (K / u ^ 2) := heq
  have c7 : (1 / 2 : ℝ) * u ^ (-((7 : ℝ) / 4)) ≤ (1 / 16 : ℝ) * (K / u ^ 2) := by
    rw [hd74]
    have hdiv' : u ^ ((1 : ℝ) / 4) / u ^ 2 ≤ (K / 8) / u ^ 2 := hdiv (h14.trans hK12_le)
    have heq : (1 / 2 : ℝ) * ((K / 8) / u ^ 2) = (1 / 16 : ℝ) * (K / u ^ 2) := by ring
    calc
      (1 / 2 : ℝ) * (u ^ ((1 : ℝ) / 4) / u ^ 2) ≤ (1 / 2 : ℝ) * ((K / 8) / u ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = (1 / 16 : ℝ) * (K / u ^ 2) := heq
  have c8 : (4 / 9 : ℝ) * u ^ (-((11 : ℝ) / 6)) ≤ (1 / 36 : ℝ) * (K / u ^ 2) := by
    rw [hd116]
    have hdiv' : u ^ ((1 : ℝ) / 6) / u ^ 2 ≤ (K / 16) / u ^ 2 := hdiv (h16p.trans hK13_sixteenth)
    have heq : (4 / 9 : ℝ) * ((K / 16) / u ^ 2) = (1 / 36 : ℝ) * (K / u ^ 2) := by ring
    calc
      (4 / 9 : ℝ) * (u ^ ((1 : ℝ) / 6) / u ^ 2) ≤ (4 / 9 : ℝ) * ((K / 16) / u ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 4 / 9)
      _ = (1 / 36 : ℝ) * (K / u ^ 2) := heq
  have c9 : (8 / 25 : ℝ) * u ^ (-((19 : ℝ) / 10)) ≤ (1 / 25 : ℝ) * (K / u ^ 2) := by
    rw [hd1910]
    have hdiv' : u ^ ((1 : ℝ) / 10) / u ^ 2 ≤ (K / 8) / u ^ 2 := hdiv (h110.trans hK15_eighth)
    have heq : (8 / 25 : ℝ) * ((K / 8) / u ^ 2) = (1 / 25 : ℝ) * (K / u ^ 2) := by ring
    calc
      (8 / 25 : ℝ) * (u ^ ((1 : ℝ) / 10) / u ^ 2) ≤ (8 / 25 : ℝ) * ((K / 8) / u ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiv' (by norm_num : (0 : ℝ) ≤ 8 / 25)
      _ = (1 / 25 : ℝ) * (K / u ^ 2) := heq
  -- sum: farD2 ≤ -K/u² + [sum of constants]·K/u² < 0
  have hcoeff : (1 / 4 + 2 / 45 + 1 / 100 : ℝ) * Real.log 4 + (1 / 4 + 5 / 81 + 3 / 250 + 1 / 16 + 1 / 36 + 1 / 25) < 1 := by
    have h4 : Real.log 4 ≤ (3 : ℝ) / 2 := log_four_le_three_halves
    norm_num at h4 ⊢
    nlinarith
  have hposK : 0 < K / u ^ 2 := by positivity
  dsimp [farD2]
  ring_nf at *
  nlinarith [c1, c2, c3, c4, c5, c6, c7, c8, c9, hcoeff, hposK]

/-- `(2/3)·x^{1/3} - log x` is strictly increasing on `[4096, ∞)`. -/
lemma strictMonoOn_two_thirds_cuberoot_sub_log :
    StrictMonoOn (fun x : ℝ => (2 / 3 : ℝ) * x ^ ((3 : ℝ)⁻¹) - Real.log x) (Set.Ici (4096 : ℝ)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici (4096 : ℝ)) ?_ ?_
  · have hcont : ContinuousOn (fun x : ℝ => (2 / 3 : ℝ) * x ^ ((3 : ℝ)⁻¹) - Real.log x)
        (Set.Ioi (0 : ℝ)) := by
      intro x hx
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hpow : ContinuousAt (fun y : ℝ => y ^ ((3 : ℝ)⁻¹)) x := by
        fun_prop
      exact ((hpow.const_mul (2 / 3 : ℝ)).sub (Real.continuousAt_log hx0)).continuousWithinAt
    refine hcont.mono ?_
    intro x hx
    rw [mem_Ici] at hx
    exact (by norm_num : (0 : ℝ) < 4096).trans_le hx
  · intro x hx
    have hx4096 : 4096 < x := by simpa [Set.mem_Ici, interior_Ici] using hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hr : HasDerivAt (fun y : ℝ => y ^ ((3 : ℝ)⁻¹))
        (((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1)) x :=
      Real.hasDerivAt_rpow_const (x := x) (p := (3 : ℝ)⁻¹) (Or.inl (ne_of_gt hx0))
    have hg : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * y ^ ((3 : ℝ)⁻¹) - Real.log y)
        ((2 / 3 : ℝ) * (((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1)) - x⁻¹) x :=
      (hr.const_mul (2 / 3 : ℝ)).sub (Real.hasDerivAt_log (ne_of_gt hx0))
    rw [hg.deriv]
    have hx16 : (16 : ℝ) < x ^ ((3 : ℝ)⁻¹) := by
      have hpow := Real.rpow_lt_rpow (by norm_num : (0 : ℝ) ≤ 4096) hx4096 (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
      have h4096 : (4096 : ℝ) ^ ((3 : ℝ)⁻¹) = 16 := by
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rwa [h4096] at hpow
    have hxdec : x ^ (-((2 : ℝ) / 3)) = x⁻¹ * x ^ ((3 : ℝ)⁻¹) := by
      have h : -((2 : ℝ) / 3) = -1 + (3 : ℝ)⁻¹ := by norm_num
      rw [h, Real.rpow_add hx0]
      congr 1
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ x) (1 : ℝ)]
      rw [Real.rpow_one]
    have hcalc : (2 / 3 : ℝ) * (((3 : ℝ)⁻¹) * x ^ (((3 : ℝ)⁻¹) - 1)) - x⁻¹
        = x⁻¹ * ((2 / 9 : ℝ) * x ^ ((3 : ℝ)⁻¹) - 1) := by
      have h1 : ((3 : ℝ)⁻¹) - 1 = -((2 : ℝ) / 3) := by norm_num
      rw [h1, hxdec]
      field_simp [hx0.ne']
      ring
    rw [hcalc]
    have hpos : 0 < (2 / 9 : ℝ) * x ^ ((3 : ℝ)⁻¹) - 1 := by
      have h1 : (9 : ℝ) / 2 < x ^ ((3 : ℝ)⁻¹) := by nlinarith [hx16]
      have hmul : (2 / 9 : ℝ) * (9 / 2) < (2 / 9 : ℝ) * x ^ ((3 : ℝ)⁻¹) := by
        exact mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 2 / 9)
      nlinarith
    have hxinv : 0 < x⁻¹ := by positivity
    nlinarith

/-- `ln x ≤ (2/3)·x^{1/3}` for `x ≥ 4096`. -/
lemma far_log_le_two_thirds_cuberoot {x : ℝ} (hx : 4096 ≤ x) :
    Real.log x ≤ (2 / 3 : ℝ) * x ^ ((3 : ℝ)⁻¹) := by
  by_cases hxeq : x = 4096
  · subst x
    have hbase : (0 : ℝ) ≤ (2 / 3 : ℝ) * (4096 : ℝ) ^ ((3 : ℝ)⁻¹) - Real.log 4096 := by
      have h4096 : (4096 : ℝ) ^ ((3 : ℝ)⁻¹) = 16 := by
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [h4096]
      have hlog : Real.log 4096 ≤ 9 := by
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num, Real.log_pow]
        calc
          12 * Real.log 2 ≤ 12 * (3 / 4 : ℝ) := by gcongr; exact log_two_le_three_fourths
          _ = 9 := by norm_num
      have h16 : (9 : ℝ) ≤ (2 / 3 : ℝ) * 16 := by norm_num
      nlinarith
    simpa using hbase
  · have hxlt : (4096 : ℝ) < x := lt_of_le_of_ne hx (Ne.symm hxeq)
    have hg := strictMonoOn_two_thirds_cuberoot_sub_log
    have h4096i : (4096 : ℝ) ∈ Set.Ici 4096 := by simp
    have hxI : x ∈ Set.Ici 4096 := by simp [hx]
    have hmono : (2 / 3 : ℝ) * (4096 : ℝ) ^ ((3 : ℝ)⁻¹) - Real.log 4096
        ≤ (2 / 3 : ℝ) * x ^ ((3 : ℝ)⁻¹) - Real.log x := (hg h4096i hxI hxlt).le
    have hbase : (0 : ℝ) ≤ (2 / 3 : ℝ) * (4096 : ℝ) ^ ((3 : ℝ)⁻¹) - Real.log 4096 := by
      have h4096 : (4096 : ℝ) ^ ((3 : ℝ)⁻¹) = 16 := by
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [h4096]
      have hlog : Real.log 4096 ≤ 9 := by
        rw [show (4096 : ℝ) = (2 : ℝ) ^ (12 : ℕ) by norm_num, Real.log_pow]
        calc
          12 * Real.log 2 ≤ 12 * (3 / 4 : ℝ) := by gcongr; exact log_two_le_three_fourths
          _ = 9 := by norm_num
      have h16 : (9 : ℝ) ≤ (2 / 3 : ℝ) * 16 := by norm_num
      nlinarith
    linarith

/-! Endpoint lemmas `farG_sixteenK_pos` / `farG_sqK_pos` and `farG_pos` are the next step.
See `NEXT_SESSION_PROMPT.md` / `SYLVESTER_CONTINUE.md`. -/

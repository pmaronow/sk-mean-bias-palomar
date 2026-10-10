module
public import HexagonPaper.CriticalClosure
public import QuantitativeFollowup.Absorption

@[expose] public section

/-! The revised proof's normalization and sublinear absorption.  The
real inequalities below are applied to the actual SK trial error, whose
input is proved in `critical_trial_error_input`. -/

noncomputable section
namespace HexagonPaper
open QuantitativeFollowup
open Set Filter QuantitativePaper
open scoped Topology

theorem lower_rpow_le_one_add {x : ℝ} (hx : 0 ≤ x) :
    x ^ (1 / 21 : ℝ) ≤ 1 + x ^ (1 / 7 : ℝ) := by
  by_cases h : 1 ≤ x
  · have hpow := Real.rpow_le_rpow_of_exponent_le h
      (by norm_num : (1 / 21 : ℝ) ≤ 1 / 7)
    linarith
  · have hpow := Real.rpow_le_one hx (le_of_not_ge h)
      (by norm_num : (0 : ℝ) ≤ 1 / 21)
    have hnonneg := Real.rpow_nonneg hx (1 / 7 : ℝ)
    linarith

theorem sublinear_seventh_absorption {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C)
    (hbound : x ≤ C * (1 + x ^ (1 / 7 : ℝ))) :
    x ≤ 2 * C + (12 / 7 : ℝ) * C ^ (7 / 6 : ℝ) *
      (7 / 2 : ℝ) ^ (-(1 / 6 : ℝ)) := by
  have hy := scaled_young_rpow hC hx
    (by norm_num : (0 : ℝ) < 1 / 7)
    (by norm_num : (1 / 7 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 7 / 2)
  norm_num at hy
  nlinarith

theorem critical_input_normalization {N e C L : ℝ}
    (hN : 2 ≤ N) (he : 0 ≤ e) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hinput : e ≤
      C * N ^ (-(19 / 25 : ℝ)) * (Real.log (2 + N)) ^ 3 +
      C * N ^ (-(2 / 3 : ℝ)) *
        (e + L * (followupScale N) ^ 5) ^ (1 / 21 : ℝ) +
      C * N ^ (-(2 / 3 : ℝ)) * (followupScale N) ^ (-(1 / 3 : ℝ)) *
        (e + L * (followupScale N) ^ 5) ^ (1 / 7 : ℝ)) :
    let r := N ^ (-(7 / 10 : ℝ))
    let x := e / r + L
    1 ≤ x ∧ x ≤ L + C *
      (N ^ (-(3 / 50 : ℝ)) * (Real.log (2 + N)) ^ 3 +
        x ^ (1 / 21 : ℝ) + N ^ (-(1 / 50 : ℝ)) * x ^ (1 / 7 : ℝ)) := by
  dsimp only
  have hNp : 0 < N := by linarith
  let r := N ^ (-(7 / 10 : ℝ))
  let x := e / r + L
  have hr : 0 < r := Real.rpow_pos_of_pos hNp _
  have hx : 1 ≤ x := by dsimp only [x]; exact le_add_of_nonneg_left (div_nonneg he hr.le) |>.trans' hL
  have heta : e + L * (followupScale N) ^ 5 = r * x := by
    rw [followupScale_pow_five hNp]
    dsimp only [x, r]
    field_simp
    <;> ring
  have hfirst : N ^ (-(19 / 25 : ℝ)) = r * N ^ (-(3 / 50 : ℝ)) := by
    dsimp only [r]
    rw [← Real.rpow_add hNp]
    congr 1
    norm_num
  rw [heta] at hinput
  have hcrit := normalized_critical_budget hNp (show 0 ≤ x by linarith)
  have hloc := normalized_localization_budget hNp (show 0 ≤ x by linarith)
  change N ^ (-(2 / 3 : ℝ)) * (r * x) ^ (1 / 21 : ℝ) =
    r * x ^ (1 / 21 : ℝ) at hcrit
  change N ^ (-(2 / 3 : ℝ)) * followupScale N ^ (-(1 / 3 : ℝ)) *
    (r * x) ^ (1 / 7 : ℝ) = r * N ^ (-(1 / 50 : ℝ)) *
      x ^ (1 / 7 : ℝ) at hloc
  have hrewrite : e ≤ r * C *
      (N ^ (-(3 / 50 : ℝ)) * (Real.log (2 + N)) ^ 3 +
        x ^ (1 / 21 : ℝ) + N ^ (-(1 / 50 : ℝ)) * x ^ (1 / 7 : ℝ)) := by
    calc
      e ≤ _ := hinput
      _ = _ := by
        rw [hfirst]
        have hcrit' := congrArg (C * ·) hcrit
        have hloc' := congrArg (C * ·) hloc
        nlinarith
  refine ⟨hx, ?_⟩
  change x ≤ _
  dsimp only [x]
  have hdiv : e / r ≤ C *
      (N ^ (-(3 / 50 : ℝ)) * (Real.log (2 + N)) ^ 3 +
        x ^ (1 / 21 : ℝ) + N ^ (-(1 / 50 : ℝ)) * x ^ (1 / 7 : ℝ)) := by
    apply (div_le_iff₀ hr).2
    convert hrewrite using 1 <;> ring
  nlinarith

theorem critical_normalized_budget_bounded {N e C L : ℝ}
    (hN : 2 ≤ N) (he : 0 ≤ e) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hinput : e ≤
      C * N ^ (-(19 / 25 : ℝ)) * (Real.log (2 + N)) ^ 3 +
      C * N ^ (-(2 / 3 : ℝ)) *
        (e + L * (followupScale N) ^ 5) ^ (1 / 21 : ℝ) +
      C * N ^ (-(2 / 3 : ℝ)) * (followupScale N) ^ (-(1 / 3 : ℝ)) *
        (e + L * (followupScale N) ^ 5) ^ (1 / 7 : ℝ)) :
    let B := L + C * ((Real.log 2 + 50) ^ 3 + 2)
    e ≤ (2 * B + (12 / 7 : ℝ) * B ^ (7 / 6 : ℝ) *
      (7 / 2 : ℝ) ^ (-(1 / 6 : ℝ))) * N ^ (-(7 / 10 : ℝ)) := by
  let r := N ^ (-(7 / 10 : ℝ))
  let x := e / r + L
  let B := L + C * ((Real.log 2 + 50) ^ 3 + 2)
  have hr : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hx, hnorm⟩ := critical_input_normalization hN he hC hL hinput
  change 1 ≤ x at hx
  change x ≤ L + C *
    (N ^ (-(3 / 50 : ℝ)) * (Real.log (2 + N)) ^ 3 +
      x ^ (1 / 21 : ℝ) + N ^ (-(1 / 50 : ℝ)) * x ^ (1 / 7 : ℝ)) at hnorm
  have hlog := normalized_log_cube_bounded hN
  have hp := lower_rpow_le_one_add (show 0 ≤ x by linarith)
  have hNpow : N ^ (-(1 / 50 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hxn : 0 ≤ x ^ (1 / 7 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_right hNpow hxn
  have hlogn : 0 ≤ (Real.log 2 + 50) ^ 3 := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hbound : x ≤ B * (1 + x ^ (1 / 7 : ℝ)) := by
    have hb : x ≤ L + C * ((Real.log 2 + 50) ^ 3 + 1 +
        2 * x ^ (1 / 7 : ℝ)) := by
      have hsum := add_le_add (add_le_add hlog hp) hmul
      have hm := mul_le_mul_of_nonneg_left hsum hC
      nlinarith
    have hconstant : L + C * ((Real.log 2 + 50) ^ 3 + 1) ≤ B := by
      dsimp only [B]
      nlinarith
    have hcoefficient : 2 * C ≤ B := by
      dsimp only [B]
      nlinarith [mul_nonneg hC hlogn]
    have hm := mul_le_mul_of_nonneg_right hcoefficient hxn
    nlinarith
  have habs := sublinear_seventh_absorption (show 0 ≤ x by linarith) hB hbound
  have heDiv : e / r ≤ x := by dsimp only [x]; linarith
  have hscaled := (div_le_iff₀ hr).1 (heDiv.trans habs)
  simpa only [B, r] using hscaled

/-- Apply the revised normalization and absorption to the genuine native
SK comparison error. No trial-budget or stable-interval hypothesis is
left for the caller to prove. -/
theorem critical_trial_error_bound (β : ℝ) (hβ : 1 < β) :
    ∃ B : ℝ, ∃ N₁ : ℕ, 0 < B ∧ 2 ≤ N₁ ∧
      ∀ N : ℕ, N₁ ≤ N →
        energyComparisonError N β (followupScale (N : ℝ)) ≤
          B * (N : ℝ) ^ (-(7 / 10 : ℝ)) := by
  obtain ⟨C, L, N₀, hC, hL, hN₀, hinput⟩ := critical_trial_error_input β hβ
  have hβp : 0 < β := zero_lt_one.trans hβ
  have hsmall : ∀ᶠ N : ℕ in atTop, followupScale (N : ℝ) ≤ β / 2 := by
    simpa only [followupScale, neg_div, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7 / 50)).comp
        tendsto_natCast_atTop_atTop).eventually_le_const (by positivity : 0 < β / 2)
  obtain ⟨Nt, hNt⟩ := eventually_atTop.1 hsmall
  let B := L + C * ((Real.log 2 + 50) ^ 3 + 2)
  have hB : 0 < B := by
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [B]
    positivity
  refine ⟨2 * B + (12 / 7 : ℝ) * B ^ (7 / 6 : ℝ) *
    (7 / 2 : ℝ) ^ (-(1 / 6 : ℝ)), max N₀ Nt, by positivity,
    hN₀.trans (le_max_left _ _), ?_⟩
  intro N hN
  have hn₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hn : 2 ≤ N := hN₀.trans hn₀
  have hnpos : 0 < N := by omega
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hnpos
  have hlam := hNt N ((le_max_right _ _).trans hN)
  have hs : followupScale (N : ℝ) / β ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (followupScale_pos hNp) hβp,
      (div_lt_one hβp).2 (by linarith)⟩
  have he := energyComparisonError_nonneg N hnpos β hβp
    (followupScale (N : ℝ)) hs
  exact critical_normalized_budget_bounded (by exact_mod_cast hn) he hC.le hL
    (hinput N hn₀)

end HexagonPaper

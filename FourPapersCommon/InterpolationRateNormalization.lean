module
public import FourPapersCommon.InterpolationQuantileRate

@[expose] public section

/-! Exact normalization of the three interpolation rates. Positive beta
is essential when simplifying its squared fractional powers. -/
noncomputable section
open Set
namespace FourPapersCommon
set_option maxHeartbeats 700000

theorem interpolation_power_normalization (N β p : ℝ) (hN : 0 < N) (hβ : 0 < β) :
    β^2 * (N * β^2)^p = β^(2+2*p) * N^p := by
  rw [Real.mul_rpow hN.le (sq_nonneg β)]
  calc
    β^2 * (N^p * (β^2)^p) = (β^(2 : ℝ) * (β^(2 : ℝ))^p) * N^p := by
      rw [Real.rpow_two]
      ring
    _ = β^(2+2*p) * N^p := by
      rw [←Real.rpow_mul hβ.le, ←Real.rpow_add hβ]

theorem interpolation_half_power_normalization (N β : ℝ) (hN : 0 < N) (hβ : 0 < β) :
    β^2 * (N * β^2)^(-(1/2 : ℝ)) = β * N^(-(1/2 : ℝ)) := by
  rw [interpolation_power_normalization N β _ hN hβ]
  norm_num

theorem interpolation_third_power_normalization (N β s : ℝ)
    (hN : 0 < N) (hβ : 0 < β) :
    β^2 * ((N * β^2)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ))) =
      β^(2/3 : ℝ) * N^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)) := by
  rw [←mul_assoc, interpolation_power_normalization N β _ hN hβ]
  norm_num

theorem interpolation_min_rate_normalization (N β s : ℝ) (hN : 0 < N) (hβ : 0 < β) :
    β^2 * min 1 (min ((N * β^2)^(-(1/2 : ℝ)))
      ((N * β^2)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)))) =
      min (β^2) (min (β * N^(-(1/2 : ℝ)))
        (β^(2/3 : ℝ) * N^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)))) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg β),
    mul_min_of_nonneg _ _ (sq_nonneg β), mul_one,
    interpolation_half_power_normalization N β hN hβ,
    interpolation_third_power_normalization N β s hN hβ]

end FourPapersCommon

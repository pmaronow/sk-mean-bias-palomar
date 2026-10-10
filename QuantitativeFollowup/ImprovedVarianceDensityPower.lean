module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The actual variance scale divided by system size gives the negative
fractional-moment exponent printed in the concentration corollary. -/
noncomputable section
namespace QuantitativeFollowup

theorem improved_variance_density_power (N : ℝ) (hN : 0<N) :
    N^(11/25:ℝ)/N=N^(-(14/25:ℝ)) := by
  rw [div_eq_mul_inv,←Real.rpow_neg_one N,←Real.rpow_add hN]
  norm_num

end QuantitativeFollowup

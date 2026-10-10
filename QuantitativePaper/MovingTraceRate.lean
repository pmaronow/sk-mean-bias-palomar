module
public import QuantitativePaper.FreeTraceCutoff
public import QuantitativePaper.VectorInterpolationDefect
public import FourPapersCommon.MovingCutoffChoice

@[expose] public section

/-! The literal actual trace error has all three moving-cutoff rates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem vectorInterpolationTraceError_le_one (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hβ : β ≠ 0) (ht : t < 1) :
    vectorInterpolationTraceError (n := n) μ s β t ht.le ≤ 1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := integral_mono (integrable_vectorInterpolationTraceError hn μ s β t hβ ht)
    (integrable_const (1 : ℝ)) (fun q => by
      exact (div_le_one (sq_pos_of_pos hn0)).mpr
        (integral_vectorMeasureSpinCovariance_trace_square_le_dimension μ β t s hβ ht q))
  rw [integral_const] at h
  simp only [smul_eq_mul, mul_one, Measure.real, parisiFreeMeasure_univ,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2)] at h
  exact h.trans (by linarith [hs.1])

theorem vectorInterpolationTraceError_moving_rate (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hβ : β ≠ 0) (ht : t < 1)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) :
    vectorInterpolationTraceError (n := n) μ s β t ht.le ≤
      2*min 1 (min (((n : ℝ)*((1-t)*β^2))^(-(1/2 : ℝ)))
        (((n : ℝ)*((1-t)*β^2))^(-(2/3 : ℝ))*s^(-(1/3 : ℝ)))) := by
  let M := (n : ℝ)*((1-t)*β^2)
  have hM : 0 < M := mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  have h1 := vectorInterpolationTraceError_le_one hn μ s β t ⟨hs.1.le, hs.2.le⟩ hβ ht
  by_cases hbig : M ≤ 1
  · rw [moving_rate_subcritical M s ⟨hM, hbig⟩ ⟨hs.1, hs.2.le⟩]
    linarith
  have hlarge : 1 < M := lt_of_not_ge hbig
  let u := movingQuantileCutoff M s
  have hu : u ∈ Icc s 1 := ⟨le_max_left _ _, (movingQuantileCutoff_below_one M s hlarge hs.2).le⟩
  have hU := movingQuantileCutoff_supercritical M s hM hs.1
  have hA := vector_free_trace_cutoff hn μ s β t hβ ht hs hμ hmin u hu
  change vectorInterpolationTraceError (n := n) μ s β t ht.le ≤ (u-s)+1/(M*u) at hA
  have hl := movingQuantileCutoff_initial_length M s hM hs.1.le
  have hr := moving_shell_reciprocal_dominance M u hM hU.1 hU.2
  have hbd : vectorInterpolationTraceError (n := n) μ s β t ht.le ≤
      2*(M^(-(2/3 : ℝ))*u^(-(1/3 : ℝ))) := by linarith
  rw [movingQuantileCutoff_rate_eq_min M s hM hs.1] at hbd
  have hsmall : min (M^(-(1/2 : ℝ))) (M^(-(2/3 : ℝ))*s^(-(1/3 : ℝ))) ≤ 1 :=
    (min_le_left _ _).trans (Real.rpow_lt_one_of_one_lt_of_neg hlarge (by norm_num)).le
  rw [min_eq_right hsmall]
  exact hbd

end QuantitativePaper

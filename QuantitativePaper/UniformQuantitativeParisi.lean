module
public import QuantitativePaper.InterpolationEnvelope
public import QuantitativePaper.MovingCutoffComplete
public import QuantitativePaper.PressureZeroTiltPassage
public import FourPapersCommon.InterpolationRateNormalization

@[expose] public section

/-! The complete quantitative Parisi formula with one numerical constant
for all positive temperatures, system sizes, and source moment parameters.
The expectation estimate uses the genuine zero-tilt pressure limit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128

def quantitativeParisiConstant : ℝ := 3 * movingCutoffDefectConstant / 4

theorem quantitativeParisiConstant_pos : 0 < quantitativeParisiConstant := by
  unfold quantitativeParisiConstant
  positivity [movingCutoffDefectConstant_pos]

theorem optimizedVectorInterpolationDefect_moving_rate (n : ℕ) (hn : 0 < n)
    (β s : ℝ) (hβ : β ≠ 0) (hs : s ∈ Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hf : DifferentiableAt ℝ (vectorInterpolationMinimum n β s) t) :
    optimizedVectorInterpolationDefect n β s t ≤ movingCutoffDefectConstant *
      interpolationQuantileRate ((n : ℝ) * β^2) s t := by
  let μ := vectorMeasureMinimizer n hn β t s ht.2.le hs.2.le
  have hμ : μ ∈ scalarFloor s := vectorMeasureMinimizer_mem n hn β t s ht.2.le hs.2.le
  have hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤
      vectorMeasureFunctional n ν β t s := fun ν hν =>
    vectorMeasureMinimizer_minimal n hn β t s ht.2.le hs.2.le ν hν
  rw [optimizedVectorInterpolationDefect_eq_of_minimizer hn μ β s hs hμ hβ t ht hmin hf]
  have h := vector_moving_cutoff hn μ s β t hβ ht.2 hs hμ hmin
  have hM : (n : ℝ) * ((1-t)*β^2) = ((n : ℝ)*β^2)*(1-t) := by ring
  simpa only [hM, interpolationQuantileRate] using h

theorem uniform_quantitative_parisi_fractional (n : ℕ) (hn : 0 < n)
    (β s : ℝ) (hβ : 0 < β) (hs : s ∈ Ioc (0 : ℝ) (1/2)) :
    0 ≤ constrainedParisiValue β s - completedFractionalPressure n β s ∧
      constrainedParisiValue β s - completedFractionalPressure n β s ≤
        quantitativeParisiConstant * min (β^2) (min (β * (n : ℝ)^(-(1/2 : ℝ)))
          (β^(2/3 : ℝ) * (n : ℝ)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)))) := by
  have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 0 < (n : ℝ) * β^2 := mul_pos hnR (sq_pos_of_pos hβ)
  obtain ⟨hi, hgap⟩ := vectorInterpolationMinimum_integral n hn β s hs1 hβ.ne'
  have hr := interpolationQuantileRate_intervalIntegrable ((n : ℝ)*β^2) s hA hs.1
  have hb : (optimizedVectorInterpolationDefect n β s) ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun t => movingCutoffDefectConstant * interpolationQuantileRate ((n : ℝ)*β^2) s t := by
    filter_upwards [(vectorInterpolationMinimum_ae_differentiable n hn β s hs1 hβ.ne').filter_mono
        (ae_mono Measure.restrict_le_self),
      (volume.ae_ne (0 : ℝ)).filter_mono (ae_mono Measure.restrict_le_self),
      (volume.ae_ne (1 : ℝ)).filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Icc] with t hdiff ht0 ht1 ht
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩
    exact optimizedVectorInterpolationDefect_moving_rate n hn β s hβ.ne' hs1 t hti (hdiff ht)
  have hInt := intervalIntegral.integral_mono_ae_restrict zero_le_one hi
    (hr.const_mul movingCutoffDefectConstant) hb
  rw [intervalIntegral.integral_const_mul] at hInt
  have hRate := integral_interpolationQuantileRate_le ((n : ℝ)*β^2) s hA hs.1
  refine ⟨constrainedParisiValue_sub_completedFractionalPressure_nonneg n hn β s hs1 hβ.ne', ?_⟩
  rw [hgap]
  calc
    _ ≤ β^2/4 * (movingCutoffDefectConstant *
        (3 * min 1 (min (((n : ℝ)*β^2)^(-(1/2 : ℝ)))
          (((n : ℝ)*β^2)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)))))) :=
      mul_le_mul_of_nonneg_left (hInt.trans (mul_le_mul_of_nonneg_left hRate
        movingCutoffDefectConstant_pos.le)) (by positivity)
    _ = quantitativeParisiConstant * (β^2 * min 1
        (min (((n : ℝ)*β^2)^(-(1/2 : ℝ)))
          (((n : ℝ)*β^2)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ))))) := by
      unfold quantitativeParisiConstant
      ring
    _ = _ := by rw [interpolation_min_rate_normalization (n : ℝ) β s hnR hβ]

theorem uniform_quantitative_parisi_pressure (n : ℕ) (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) :
    0 ≤ Paper.parisiPDEValue β 0 - pressure n β ∧
      Paper.parisiPDEValue β 0 - pressure n β ≤
        quantitativeParisiConstant * β * (n : ℝ)^(-(1/2 : ℝ)) := by
  apply pressure_gap_of_fractional_bounds n β _
  intro s hs
  have h := uniform_quantitative_parisi_fractional n hn β s hβ hs
  refine ⟨h.1, h.2.trans ?_⟩
  have hm : min (β^2) (min (β * (n : ℝ)^(-(1/2 : ℝ)))
      (β^(2/3 : ℝ) * (n : ℝ)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ)))) ≤
      β * (n : ℝ)^(-(1/2 : ℝ)) := (min_le_right _ _).trans (min_le_left _ _)
  convert mul_le_mul_of_nonneg_left hm quantitativeParisiConstant_pos.le using 1 <;> ring

theorem uniform_quantitative_parisi : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ β : ℝ, 0 < β →
    (∀ s ∈ Ioc (0 : ℝ) (1/2), 0 ≤ constrainedParisiValue β s - completedFractionalPressure n β s ∧
      constrainedParisiValue β s - completedFractionalPressure n β s ≤ C *
        min (β^2) (min (β * (n : ℝ)^(-(1/2 : ℝ)))
          (β^(2/3 : ℝ) * (n : ℝ)^(-(2/3 : ℝ)) * s^(-(1/3 : ℝ))))) ∧
    (0 ≤ Paper.parisiPDEValue β 0 - pressure n β ∧
      Paper.parisiPDEValue β 0 - pressure n β ≤ C * β * (n : ℝ)^(-(1/2 : ℝ))) :=
  ⟨quantitativeParisiConstant, quantitativeParisiConstant_pos, fun n hn β hβ =>
    ⟨fun s hs => uniform_quantitative_parisi_fractional n hn β s hβ hs,
      uniform_quantitative_parisi_pressure n hn β hβ⟩⟩

end QuantitativePaper

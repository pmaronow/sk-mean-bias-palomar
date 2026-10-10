module
public import QuantitativePaper.VectorStateExponentialTime

@[expose] public section

/-! Closed space-time exponential localization for both actual fractional
finite-profile laws and the actual arbitrary-measure fractional law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_exp_vectorOuterLaw_norm (s : SpinGlass.Targets.RSBScheme k)
    (β t outer K : ℝ) :
    Integrable (fun p : Couplings n×ℝ=>Real.exp (K*‖p‖))
      (vectorOuterLaw s β t outer) := by
  have hp (p : Couplings n×ℝ) : 0≤vectorOuterWeight s β t outer p:=
    div_nonneg (Real.exp_pos _).le (vectorOuterPartition_pos s β t outer).le
  rw [vectorOuterLaw]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_vectorOuterWeight s β t outer).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hp _),smul_eq_mul] using
    integrable_exp_vectorOuterWeight_norm (n := n) s β t outer K

theorem integrable_exp_vectorMeasureOuterLaw_norm (μ : Paper.ParisiMeasure)
    (β t outer K : ℝ) (ht : t≤1) :
    Integrable (fun p : Couplings n×ℝ=>Real.exp (K*‖p‖))
      (vectorMeasureOuterLaw μ β t outer) := by
  have hp (p : Couplings n×ℝ) : 0≤vectorMeasureOuterWeight μ β t outer p:=
    div_nonneg (Real.exp_pos _).le (vectorMeasureOuterPartition_pos μ β t outer ht).le
  rw [vectorMeasureOuterLaw]
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_vectorMeasureOuterWeight μ β t outer ht).ennreal_ofReal
    (.of_forall fun _=>ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hp _),smul_eq_mul] using
    integrable_exp_vectorMeasureOuterWeight_norm (n := n) μ β t outer K ht

theorem vectorFiniteDisorderTilt_eq_prod (s : SpinGlass.Targets.RSBScheme k)
    (β t outer : ℝ) :
    vectorFiniteDisorderTilt (n := n) s β t outer=
      (vectorOuterLaw s β t outer).prod (vectorBrownianMeasure n) := by
  unfold vectorFiniteDisorderTilt vectorOuterLaw vectorDisorderBrownianMeasure
  exact (prod_withDensity_left
    (measurable_vectorOuterWeight s β t outer).ennreal_ofReal).symm

theorem integrable_time_exp_vectorFiniteState_and_disorder (s : SpinGlass.Targets.RSBScheme k)
    (β t outer K : ℝ) (ht : t≤1) :
    Integrable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      Real.exp (K*(‖z.2.1‖+‖vectorFiniteState s β t ht z.1 z.2‖)))
      ((nonnegativeLebesgueMeasure.restrict (Ioc 0 1)).prod
        (vectorFiniteDisorderTilt s β t outer)) := by
  rw [vectorFiniteDisorderTilt_eq_prod]
  letI := vectorOuterLaw_probability (n := n) s β t outer
  exact integrable_time_exp_bounded_vectorState (vectorOuterLaw s β t outer)
    (vectorFiniteState s β t ht) (measurable_uncurry_vectorFiniteState s β t ht)
    (((1-t)*β^2)*Real.sqrt n) (Real.sqrt ((1-t)*β^2)) K (Real.sqrt_nonneg _)
    (integrable_exp_vectorOuterLaw_norm s β t outer |K|)
    (fun r hr sample=>norm_vectorFiniteState_le s β t ht r hr sample)

theorem integrable_time_exp_vectorMeasureState_and_disorder (μ : Paper.ParisiMeasure)
    (β t outer K : ℝ) (ht : t≤1) :
    Integrable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      Real.exp (K*(‖z.2.1‖+‖vectorMeasureState μ β t ht z.1 z.2‖)))
      ((nonnegativeLebesgueMeasure.restrict (Ioc 0 1)).prod
        (vectorMeasureDisorderTilt μ β t outer)) := by
  rw [vectorMeasureDisorderTilt_eq_prod μ β t outer ht]
  letI := vectorMeasureOuterLaw_probability (n := n) μ β t outer ht
  exact integrable_time_exp_bounded_vectorState (vectorMeasureOuterLaw μ β t outer)
    (vectorMeasureState μ β t ht) (measurable_uncurry_vectorMeasureState μ β t ht)
    (((1-t)*β^2)*Real.sqrt n) (Real.sqrt ((1-t)*β^2)) K (Real.sqrt_nonneg _)
    (integrable_exp_vectorMeasureOuterLaw_norm μ β t outer |K| ht)
    (fun r hr sample=>norm_vectorMeasureState_le μ β t ht r hr sample)

end QuantitativePaper

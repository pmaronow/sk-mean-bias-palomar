module
public import QuantitativePaper.VectorTemperatureStateContinuity
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityLaw

@[expose] public section

/-! True same-sample continuity of the terminal Gibbs observables and
the mean products used by conditional covariance on the fixed Wiener space. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem continuous_vectorTerminalMean_temperature_field (β : ℝ)
    (p : Couplings n × ℝ) (d : Configuration n → ℝ) :
    Continuous (fun z : ℝ × Field n => terminalMean (vectorTerminalExponent n β z.1 p z.2) d) := by
  have hE (σ : Configuration n) : Continuous (fun z : ℝ × Field n =>
      vectorTerminalExponent n β z.1 p z.2 σ) := by
    unfold vectorTerminalExponent fieldDot
    fun_prop
  have hZ : Continuous (fun z : ℝ × Field n => terminalPartition (vectorTerminalExponent n β z.1 p z.2)) :=
    continuous_finsetSum _ (fun σ _ => Real.continuous_exp.comp (hE σ))
  unfold terminalMean
  apply continuous_finsetSum
  intro σ _
  unfold terminalWeight
  exact ((Real.continuous_exp.comp (hE σ)).div hZ (fun z => (terminalPartition_pos _).ne')).mul continuous_const

theorem continuous_vectorMeasureTerminalObservable_temperature (μ : Paper.ParisiMeasure)
    (β : ℝ) (d : Configuration n → ℝ) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorMeasureTerminalObservable μ β t t.property.le d sample) :=
  (continuous_vectorTerminalMean_temperature_field β sample.1 d).comp
    (continuous_subtype_val.prodMk (continuous_vectorMeasureState_temperature μ β 1 le_rfl sample))

theorem continuous_vectorMeasureSpinMean_temperature (μ : Paper.ParisiMeasure)
    (β : ℝ) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorMeasureSpinMean μ β t t.property.le q sample) := by
  have hr : (q : ℝ).toNNReal ≤ 1 := by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hi : Continuous (fun t : Iio (1 : ℝ) =>
      (t,vectorMeasureState μ β t t.property.le (q : ℝ).toNNReal sample)) :=
    continuous_id.prodMk (continuous_vectorMeasureState_temperature (n := n) μ β _ hr sample)
  have h := (continuous_vectorMeasureGradient_temperature_field (n := n) μ β q sample.1).comp hi
  simpa only [Function.comp_def,vectorMeasureSpinMean] using h

theorem continuous_vectorBasePairObservable_temperature (μ : Paper.ParisiMeasure)
    (β : ℝ) (i j : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorBasePairObservable μ β t t.property.le i j sample) :=
  continuous_vectorMeasureTerminalObservable_temperature μ β _ sample

theorem continuous_vectorBaseMeanProduct_temperature (μ : Paper.ParisiMeasure)
    (β : ℝ) (q : Paper.Overlap) (i j : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun t : Iio (1 : ℝ) => vectorBaseMeanProduct μ β t t.property.le q i j sample) := by
  have h := ((EuclideanSpace.proj i).continuous.comp (continuous_vectorMeasureSpinMean_temperature μ β q sample)).mul
    ((EuclideanSpace.proj j).continuous.comp (continuous_vectorMeasureSpinMean_temperature μ β q sample))
  simpa only [Function.comp_def,Pi.mul_def,EuclideanSpace.proj,PiLp.proj_apply,vectorBaseMeanProduct] using h

end QuantitativePaper

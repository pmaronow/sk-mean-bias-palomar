module
public import QuantitativePaper.VectorTemperatureObservableContinuity
public import QuantitativePaper.VectorTemperatureDensityContinuity
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityTransfer

@[expose] public section

/-! Genuine continuity of actual conditional spin-covariance moments.
Every L² input is obtained from the constructed state, bounded spin
observables, and proved Gaussian density domination on the fixed Wiener law. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorTemperaturePairObservableL2 (μ : Paper.ParisiMeasure) (β : ℝ) (i j : Fin n)
    (t : Iio (1 : ℝ)) : Lp ℝ 2 (vectorDisorderBrownianMeasure n) :=
  (memLp_vectorBasePairObservable μ β t t.property.le i j).toLp
    (vectorBasePairObservable μ β t t.property.le i j)

def vectorTemperatureMeanProductL2 (μ : Paper.ParisiMeasure) (β : ℝ) (q : Paper.Overlap)
    (i j : Fin n) (t : Iio (1 : ℝ)) : Lp ℝ 2 (vectorDisorderBrownianMeasure n) :=
  (memLp_vectorBaseMeanProduct μ β t t.property.le q i j).toLp
    (vectorBaseMeanProduct μ β t t.property.le q i j)

theorem continuous_vectorTemperaturePairObservableL2 (μ : Paper.ParisiMeasure)
    (β : ℝ) (i j : Fin n) : Continuous (vectorTemperaturePairObservableL2 μ β i j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun u : Iio (1 : ℝ) => vectorBasePairObservable μ β u u.property.le i j)
    (vectorBasePairObservable μ β t t.property.le i j)
    (fun u => memLp_vectorBasePairObservable μ β u u.property.le i j)
    (memLp_vectorBasePairObservable μ β t t.property.le i j)
    (fun _ => 1) (by simpa using integrable_const (1 : ℝ))
    (.of_forall fun u => .of_forall (vectorBasePairObservable_bound μ β u u.property.le i j))
    (.of_forall (vectorBasePairObservable_bound μ β t t.property.le i j))
    (.of_forall fun sample => (continuous_vectorBasePairObservable_temperature μ β i j sample).tendsto t)

theorem continuous_vectorTemperatureMeanProductL2 (μ : Paper.ParisiMeasure)
    (β : ℝ) (q : Paper.Overlap) (i j : Fin n) : Continuous (vectorTemperatureMeanProductL2 μ β q i j) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun u : Iio (1 : ℝ) => vectorBaseMeanProduct μ β u u.property.le q i j)
    (vectorBaseMeanProduct μ β t t.property.le q i j)
    (fun u => memLp_vectorBaseMeanProduct μ β u u.property.le q i j)
    (memLp_vectorBaseMeanProduct μ β t t.property.le q i j)
    (fun _ => 1) (by simpa using integrable_const (1 : ℝ))
    (.of_forall fun u => .of_forall (vectorBaseMeanProduct_bound μ β u u.property.le q i j))
    (.of_forall (vectorBaseMeanProduct_bound μ β t t.property.le q i j))
    (.of_forall fun sample => (continuous_vectorBaseMeanProduct_temperature μ β q i j sample).tendsto t)

theorem continuous_integral_vectorMeasureSpinCovariance_entry_square_temperature
    (μ : Paper.ParisiMeasure) (β a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    Continuous (fun t : Iio (1 : ℝ) => ∫ sample,
      (vectorMeasureSpinCovariance μ β t a t.property.le q sample i j)^2
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact tendsto_vectorMeasureSpinCovariance_entry_square_of_base_L2
    (fun _ : Iio (1 : ℝ) => μ) μ β (fun u => (u : ℝ)) (fun _ => a) t a
    (fun u => u.property.le) t.property.le q i j
    ((continuous_vectorTemperaturePairObservableL2 μ β i j).tendsto t)
    ((continuous_vectorTemperatureMeanProductL2 μ β q i j).tendsto t)
    ((continuous_vectorTemperatureOuterWeightL2 μ β a).tendsto t)

theorem continuous_integral_vectorMeasureSpinCovariance_trace_square_temperature
    (μ : Paper.ParisiMeasure) (β a : ℝ) (q : Paper.Overlap) :
    Continuous (fun t : Iio (1 : ℝ) => ∫ sample,
      Matrix.trace (vectorMeasureSpinCovariance μ β t a t.property.le q sample *
        vectorMeasureSpinCovariance μ β t a t.property.le q sample)
        ∂vectorMeasureDisorderTilt (n := n) μ β t a) := by
  simp_rw [integral_vectorMeasureSpinCovariance_trace_square_eq_sum]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_integral_vectorMeasureSpinCovariance_entry_square_temperature μ β a q i j

end QuantitativePaper

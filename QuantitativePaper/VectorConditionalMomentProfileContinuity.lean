module
public import QuantitativePaper.VectorConditionalMomentProfileDensity
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityTransfer

@[expose] public section

/-! Actual conditional covariance-square moments converge under weak
profile convergence. All fixed-base L² inputs are proved from the true
state, terminal Gibbs law and normalized initial-disorder density. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n:ℕ} {J:Type*} {l:Filter J} [l.IsCountablyGenerated]
variable {ν:J→Paper.ParisiMeasure} {μ:Paper.ParisiMeasure}

theorem tendsto_vectorBasePairObservable_toLp_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (i k:Fin n) :
    Tendsto (fun j=>(memLp_vectorBasePairObservable (ν j) β t ht i k).toLp
      (vectorBasePairObservable (ν j) β t ht i k)) l
      (𝓝 ((memLp_vectorBasePairObservable μ β t ht i k).toLp
        (vectorBasePairObservable μ β t ht i k))):=by
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun j=>vectorBasePairObservable (ν j) β t ht i k)
    (vectorBasePairObservable μ β t ht i k)
    (fun j=>memLp_vectorBasePairObservable (ν j) β t ht i k)
    (memLp_vectorBasePairObservable μ β t ht i k) (fun _=>1)
    (by simpa using (integrable_const (1:ℝ) (μ:=vectorDisorderBrownianMeasure n)))
    (.of_forall fun j=>.of_forall (vectorBasePairObservable_bound (ν j) β t ht i k))
    (.of_forall (vectorBasePairObservable_bound μ β t ht i k))
    (.of_forall fun sample=>tendsto_vectorBasePairObservable_of_weak β t ht hν i k sample)

theorem tendsto_vectorBaseMeanProduct_toLp_of_weak (β t:ℝ) (ht:t≤1)
    (hν:Tendsto ν l (𝓝 μ)) (q:Paper.Overlap) (i k:Fin n) :
    Tendsto (fun j=>(memLp_vectorBaseMeanProduct (ν j) β t ht q i k).toLp
      (vectorBaseMeanProduct (ν j) β t ht q i k)) l
      (𝓝 ((memLp_vectorBaseMeanProduct μ β t ht q i k).toLp
        (vectorBaseMeanProduct μ β t ht q i k))):=by
  exact temperatureDensity_toLp_tendsto_of_dominated
    (fun j=>vectorBaseMeanProduct (ν j) β t ht q i k)
    (vectorBaseMeanProduct μ β t ht q i k)
    (fun j=>memLp_vectorBaseMeanProduct (ν j) β t ht q i k)
    (memLp_vectorBaseMeanProduct μ β t ht q i k) (fun _=>1)
    (by simpa using (integrable_const (1:ℝ) (μ:=vectorDisorderBrownianMeasure n)))
    (.of_forall fun j=>.of_forall (vectorBaseMeanProduct_bound (ν j) β t ht q i k))
    (.of_forall (vectorBaseMeanProduct_bound μ β t ht q i k))
    (.of_forall fun sample=>tendsto_vectorBaseMeanProduct_of_weak β t ht hν q i k sample)

theorem tendsto_vectorMeasureSpinCovariance_entry_square_of_weak (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) (q:Paper.Overlap) (i k:Fin n) :
    Tendsto (fun j=>∫sample,(vectorMeasureSpinCovariance (ν j) β t a ht.le q sample i k)^2
      ∂vectorMeasureDisorderTilt (n:=n) (ν j) β t a) l
      (𝓝 (∫sample,(vectorMeasureSpinCovariance μ β t a ht.le q sample i k)^2
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a)):=
  tendsto_vectorMeasureSpinCovariance_entry_square_of_base_L2 ν μ β
    (fun _=>t) (fun _=>a) t a (fun _=>ht.le) ht.le q i k
    (tendsto_vectorBasePairObservable_toLp_of_weak β t ht.le hν i k)
    (tendsto_vectorBaseMeanProduct_toLp_of_weak β t ht.le hν q i k)
    (tendsto_vectorBaseOuterWeight_toLp_of_weak β t a ht hν)

theorem tendsto_vectorMeasureSpinCovariance_trace_square_of_weak (β t a:ℝ) (ht:t<1)
    (hν:Tendsto ν l (𝓝 μ)) (q:Paper.Overlap) :
    Tendsto (fun j=>∫sample,Matrix.trace (vectorMeasureSpinCovariance (ν j) β t a ht.le q sample*
      vectorMeasureSpinCovariance (ν j) β t a ht.le q sample)
      ∂vectorMeasureDisorderTilt (n:=n) (ν j) β t a) l
      (𝓝 (∫sample,Matrix.trace (vectorMeasureSpinCovariance μ β t a ht.le q sample*
        vectorMeasureSpinCovariance μ β t a ht.le q sample)
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a)):=by
  simp_rw [integral_vectorMeasureSpinCovariance_trace_square_eq_sum]
  exact tendsto_finsetSum Finset.univ fun i _=>tendsto_finsetSum Finset.univ
    fun k _=>tendsto_vectorMeasureSpinCovariance_entry_square_of_weak β t a ht hν q i k

end QuantitativePaper

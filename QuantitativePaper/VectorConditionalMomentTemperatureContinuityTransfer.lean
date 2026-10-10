module
public import QuantitativePaper.VectorConditionalMomentTemperatureContinuityLaw
public import QuantitativePaper.VectorMeasureRandomReaction
public import QuantitativePaper.SpinMatrixDefectAlgebra

@[expose] public section

/-! Actual posterior covariance-square moments inherit convergence from
honest fixed-base L² convergence of the terminal observable, adapted mean
product and initial disorder weight. These are transfer lemmas; the actual
parameter-continuity inputs are proved in the temperature/state modules. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal ENNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendsto_vectorMeasureSpinCovariance_entry_square_of_base_L2
    {J : Type*} {l : Filter J} (μj : J→Paper.ParisiMeasure) (μ : Paper.ParisiMeasure)
    (β : ℝ) (tj aj : J→ℝ) (t a : ℝ) (htj : ∀j,tj j≤1) (ht : t≤1)
    (q : Paper.Overlap) (i k : Fin n)
    (hf : Tendsto (fun j=>(memLp_vectorBasePairObservable (n:=n) (μj j) β (tj j) (htj j) i k).toLp
      (vectorBasePairObservable (μj j) β (tj j) (htj j) i k)) l
      (𝓝 ((memLp_vectorBasePairObservable (n:=n) μ β t ht i k).toLp
        (vectorBasePairObservable μ β t ht i k))))
    (hg : Tendsto (fun j=>(memLp_vectorBaseMeanProduct (n:=n) (μj j) β (tj j) (htj j) q i k).toLp
      (vectorBaseMeanProduct (μj j) β (tj j) (htj j) q i k)) l
      (𝓝 ((memLp_vectorBaseMeanProduct (n:=n) μ β t ht q i k).toLp
        (vectorBaseMeanProduct μ β t ht q i k))))
    (hw : Tendsto (fun j=>(memLp_vectorBaseOuterWeight (n:=n) (μj j) β (tj j) (aj j) (htj j)).toLp
      (vectorBaseOuterWeight (μj j) β (tj j) (aj j))) l
      (𝓝 ((memLp_vectorBaseOuterWeight (n:=n) μ β t a ht).toLp
        (vectorBaseOuterWeight μ β t a)))) :
    Tendsto (fun j=>∫sample,(vectorMeasureSpinCovariance (μj j) β (tj j) (aj j) (htj j) q sample i k)^2
      ∂vectorMeasureDisorderTilt (n:=n) (μj j) β (tj j) (aj j)) l
      (𝓝 (∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i k)^2
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a)) := by
  simp_rw [vectorMeasureSpinCovariance_entry_square_eq_base]
  exact tendsto_weighted_conditional_covariance_square
    (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _)
    _ _ _ _ _ _
    (fun j=>memLp_vectorBasePairObservable (μj j) β (tj j) (htj j) i k)
    (fun j=>memLp_vectorBaseMeanProduct (μj j) β (tj j) (htj j) q i k)
    (fun j=>memLp_vectorBaseOuterWeight (μj j) β (tj j) (aj j) (htj j))
    (memLp_vectorBasePairObservable μ β t ht i k)
    (memLp_vectorBaseMeanProduct μ β t ht q i k)
    (memLp_vectorBaseOuterWeight μ β t a ht) hf hg hw
    (fun j=>.of_forall (vectorBasePairObservable_bound (μj j) β (tj j) (htj j) i k))
    (fun j=>.of_forall (vectorBaseMeanProduct_bound (μj j) β (tj j) (htj j) q i k))
    (.of_forall (vectorBasePairObservable_bound μ β t ht i k))
    (.of_forall (vectorBaseMeanProduct_bound μ β t ht q i k))

theorem integrable_vectorMeasureSpinCovariance_entry_square (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (i j : Fin n) :
    Integrable (fun sample=>(vectorMeasureSpinCovariance μ β t a ht q sample i j)^2)
      (vectorMeasureDisorderTilt (n:=n) μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply (integrable_const (4:ℝ)).mono'
    ((measurable_vectorMeasureSpinCovariance_entry μ β t a ht q i j).pow_const 2).aestronglyMeasurable
  filter_upwards [vectorMeasureSpinCovariance_entry_bound (n:=n) μ β t a ht q] with sample hs
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (vectorMeasureSpinCovariance μ β t a ht q sample i j),abs_le.mp (hs i j)]

theorem integral_vectorMeasureSpinCovariance_trace_square_eq_sum
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    (∫sample,Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
      vectorMeasureSpinCovariance μ β t a ht q sample)∂vectorMeasureDisorderTilt (n:=n) μ β t a)=
    ∑i : Fin n,∑j : Fin n,∫sample,(vectorMeasureSpinCovariance μ β t a ht q sample i j)^2
      ∂vectorMeasureDisorderTilt μ β t a := by
  simp_rw [symmetric_matrix_square_trace _ (vectorMeasureSpinCovariance_symmetric μ β t a ht q _)]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=>
    integrable_vectorMeasureSpinCovariance_entry_square μ β t a ht q i j)]
  exact Finset.sum_congr rfl fun i _=>integral_finsetSum _ fun j _=>
    integrable_vectorMeasureSpinCovariance_entry_square μ β t a ht q i j

end QuantitativePaper

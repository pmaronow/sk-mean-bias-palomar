module
public import QuantitativePaper.VectorScoreVarianceSignedL2
public import QuantitativePaper.VectorSupportCovarianceSquare

@[expose] public section

/-! The complete integrated variance proposition on the actual normalized
disorder, Wiener-path, and terminal-spin law. The kernel class is the full
real L2 class of the actual free measure, with both signs and a.e. versions. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_free_support_physical_trace_covariance_square_bound
    (hn : 0<n) (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Ioo (0:ℝ) 1)
    (hμ : μ∈scalarFloor s) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫p : VectorDisorderBrownianSample n×Configuration n,
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q p.1*
        vectorMeasureSpinCovariance μ β t s ht.le q p.1)
      ∂vectorMeasureSpinPathLaw μ β t s ht.le)≤
        (n:ℝ)/(((1-t)*β^2)*(Paper.parisiCDF μ q)^2) := by
  have hm : Measurable (fun sample : VectorDisorderBrownianSample n=>
      Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)) := by
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (measurable_vectorMeasureSpinCovariance_entry μ β t s ht.le q i j).mul
        (measurable_vectorMeasureSpinCovariance_entry μ β t s ht.le q j i)
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t s ht.le _ hm]
  exact vector_free_support_trace_covariance_square_bound hn μ s hs hμ β t hβ ht hmin q hq

/-- Main Proposition 2.2, with its literal standing ranges, every free
support point including zero, and every signed deterministic L2 kernel. -/
theorem integrated_variance_proposition (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Ico (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    (∀q∈(parisiFreeMeasure μ s).support,
      (∫p : VectorDisorderBrownianSample n×Configuration n,
        Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.2.le q p.1*
          vectorMeasureSpinCovariance μ β t s ht.2.le q p.1)
        ∂vectorMeasureSpinPathLaw μ β t s ht.2.le)≤
          (n:ℝ)/(((1-t)*β^2)*(Paper.parisiCDF μ q)^2)) ∧
    (∀κ : Paper.Overlap→ℝ,MemLp κ 2 (parisiFreeMeasure μ s)→
      variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.2.le κ)
        (vectorMeasureSpinPathLaw μ β t s ht.2.le)≤
        (1/((n:ℝ)*((1-t)*β^2)))*
          (∫q,κ q^2/Paper.parisiCDF μ q ∂parisiFreeMeasure μ s)) := by
  have hs' : s∈Ioo (0:ℝ) 1 := ⟨hs.1,by linarith [hs.2]⟩
  exact ⟨fun q hq=>vector_free_support_physical_trace_covariance_square_bound
      hn μ s hs' hμ β t hβ.ne' ht.2 hmin q hq,
    fun κ hκ=>vector_weighted_score_variance_memLp hn μ s β t hβ.ne' ht.2 hs' hμ hmin κ hκ⟩

end QuantitativePaper

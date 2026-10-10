module
public import QuantitativeFollowup.FoundationDecomposition
public import QuantitativeFollowup.MeanDirectionCovariance
public import QuantitativePaper.VectorInterpolationDefect
public import QuantitativePaper.ScoreQuantileVarianceDecomposition

@[expose] public section

/-! The exact native A+2J+V decomposition, integrated against the true
free Stieltjes measure and identified with the actual quantile variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2000000
variable {n : ℕ}

theorem smallInterval_mean_covariance_eq (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    foundationMeanCovariance (n:=n) μ β t a ht.le q=
      vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q := by
  have h1:=(foundation_overlap_decomposition hn μ β t a hβ ht q).1
  have h2:=variance_vectorMeasureOverlapScore_eq_mean_covariance (n:=n) μ β t a hβ ht q
  linarith

theorem smallInterval_defect_decomposition (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) :
    vectorInterpolationDefect (n:=n) μ s β t ht.le=
      vectorInterpolationTraceError (n:=n) μ s β t ht.le+
        2*vectorMeanDirectionCovarianceIntegral (n:=n) μ s β t s ht.le+
          vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht.le := by
  let V:=fun q : Paper.Overlap=>variance (vectorSelfOverlap (n:=n) μ β t ht.le q)
    (vectorMeasureSpinPathLaw μ β t s ht.le)
  have hA:=integrable_vectorInterpolationTraceError hn μ s β t hβ ht
  have hJ:=integrable_vectorMeanDirectionCovariance hn μ s β t s hβ ht
  have hW:=integrable_vectorInterpolationScoreVariance (n:=n) μ s β t ht.le
  have hV : Integrable V (parisiFreeMeasure μ s) := by
    apply ((hW.sub hJ).const_mul 4).congr
    filter_upwards with q
    have hh:=variance_vectorMeasureOverlapScore_eq_mean_covariance (n:=n) μ β t s hβ ht q
    change 4*(variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q)
      (vectorMeasureSpinPathLaw μ β t s ht.le)-vectorMeanDirectionCovariance (n:=n) μ β t s ht.le q)=V q
    dsimp only [V]
    linarith
  have heq : vectorConditionalReplicaDefect (n:=n) μ β t s ht.le=ᵐ[parisiFreeMeasure μ s]
      (fun q=>foundationThermalTrace (n:=n) μ β t s ht.le q+
        2*vectorMeanDirectionCovariance (n:=n) μ β t s ht.le q+V q) := by
    filter_upwards [(parisiFreeMeasure μ s).support_mem_ae] with q hq
    have hh:=(foundation_overlap_decomposition hn μ β t s hβ ht q).2 s hs hμ rfl hmin hq
    rw [smallInterval_mean_covariance_eq hn μ β t s hβ ht q] at hh
    exact hh
  unfold vectorInterpolationDefect
  rw [integral_congr_ae heq]
  unfold foundationThermalTrace
  have hadd:=integral_add (hA.add (hJ.const_mul 2)) hV
  simp only [Pi.add_apply] at hadd
  rw [hadd]
  have hbase:=integral_add hA (hJ.const_mul 2)
  rw [hbase,integral_const_mul,
    vectorIntegratedSelfOverlapVariance_eq_free_integral hn μ s β t ht.le]
  rfl

end QuantitativeFollowup

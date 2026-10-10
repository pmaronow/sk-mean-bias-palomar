module
public import QuantitativePaper.VectorReplicaDefectDecomposition
public import QuantitativeFollowup.VectorSelfOverlapMoments

@[expose] public section

/-! Follow-up Lemma 2.4 for the genuine spin-path law and conditional
two-replica observable. The only contact premise is actual minimization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def foundationThermalTrace (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  (∫sample : VectorDisorderBrownianSample n,Matrix.trace
    (vectorMeasureSpinCovariance μ β t a ht q sample*
      vectorMeasureSpinCovariance μ β t a ht q sample)∂vectorMeasureDisorderTilt μ β t a)/(n:ℝ)^2

def foundationMeanCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) : ℝ :=
  ∫z : VectorMarkedSample n,vectorMeasureCovarianceQuadratic μ β t a ht q z.1
    (vectorMeasureSpinMean μ β t ht q z.1)/(n:ℝ)^2∂vectorMeasureSpinPathLaw μ β t a ht

theorem foundation_overlap_decomposition (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=
      foundationMeanCovariance (n:=n) μ β t a ht.le q+
        (1/4)*variance (vectorSelfOverlap (n:=n) μ β t ht.le q)
          (vectorMeasureSpinPathLaw μ β t a ht.le) ∧
    (∀s∈Ioo (0:ℝ) 1,μ∈scalarFloor s→a=s→
      (∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)→
      q∈(parisiFreeMeasure μ s).support→
      vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q=
        foundationThermalTrace (n:=n) μ β t s ht.le q+
        2*foundationMeanCovariance (n:=n) μ β t s ht.le q+
        variance (vectorSelfOverlap (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t s ht.le)) := by
  refine ⟨variance_vectorMeasureOverlapScore_total μ β t a hβ ht q,?_⟩
  intro s hs hμ ha hmin hq
  have hm:=vectorSelfOverlap_mean_on_free_support hn μ s β t hs hμ hβ ht hmin q hq
  have hv:=variance_eq_integral (μ:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le)
    (measurable_vectorSelfOverlap (n:=n) μ β t ht.le q).aemeasurable
  rw [hm] at hv
  have he:=vectorConditionalReplicaDefect_decomposition hn μ β t s hβ ht q
  rw [←hv] at he
  exact he

end QuantitativeFollowup

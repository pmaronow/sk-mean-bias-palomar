module
public import QuantitativeFollowup.FoundationDecomposition
public import QuantitativePaper.IntegratedVarianceProposition
public import QuantitativePaper.MovingQuantileTraceIntegral

@[expose] public section

/-! Follow-up Proposition 2.3, including the integrated thermal trace
bound and the full signed deterministic L2 class. Endpoint atoms are kept. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem foundation_integrated_variance (hn : 0<n) (β : ℝ) (hβ : 0<β)
    (s : ℝ) (hs : s∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Ico (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    (∫q,foundationThermalTrace (n:=n) μ β t s ht.2.le q∂parisiFreeMeasure μ s)≤
      1/(((n:ℝ)*((1-t)*β^2))*s) ∧
    (∀κ : Paper.Overlap→ℝ,MemLp κ 2 (parisiFreeMeasure μ s)→
      variance (vectorMeasureWeightedOverlapScore (n:=n) μ s β t ht.2.le κ)
        (vectorMeasureSpinPathLaw μ β t s ht.2.le)≤
        (1/((n:ℝ)*((1-t)*β^2)))*
          (∫q,κ q^2/Paper.parisiCDF μ q∂parisiFreeMeasure μ s)) := by
  have hs':s∈Ioo (0:ℝ) 1:=⟨hs.1,by linarith [hs.2]⟩
  refine ⟨?_,(integrated_variance_proposition hn β hβ s hs t ht μ hμ hmin).2⟩
  have hm:Measurable (foundationThermalTrace (n:=n) μ β t s ht.2.le):=
    (measurable_integral_vectorMeasureSpinCovariance_trace_square μ β t s ht.2.le).div_const _
  rw [integral_parisiFreeMeasure μ s _ hm,integral_Ioc_eq_integral_Ioo]
  have hb:=vector_moving_quantile_trace_integral hn μ s β t hβ.ne' ht.2 hs' hμ hmin s
    ⟨le_rfl,hs'.2.le⟩
  simpa only [sub_self,zero_add,foundationThermalTrace] using hb

end QuantitativeFollowup

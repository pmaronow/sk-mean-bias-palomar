module
public import HexagonPaper.MomentsCubicMoment
public import QuantitativeFollowup.VectorCubicFreeMeasure

@[expose] public section

/-! Exact free Stieltjes-measure versions of the revised stronger cubic proof.
The genuine quantile map retains all free atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
variable {n : ℕ}

theorem vector_cubic_self_overlap_moment_free_170_log_one (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) 1) :
    (∫q,∫sample,|vectorCenteredSelfOverlap (n:=n) μ β t ht.le q sample|^3
      ∂ vectorMeasureSpinPathLaw μ β t s ht.le ∂ parisiFreeMeasure μ s)≤
      z*(∫q,variance (vectorSelfOverlap (n:=n) μ β t ht.le q)
        (vectorMeasureSpinPathLaw μ β t s ht.le) ∂ parisiFreeMeasure μ s)+
      (170/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (1/z) :=by
  rw [←vectorIntegratedSelfOverlapCubic_eq_free_integral,
    ←vectorIntegratedSelfOverlapVariance_eq_free_integral hn]
  exact vector_cubic_self_overlap_moment_170_log_one hn μ s β t hβ ht hs hμ hmin hM z hz


theorem vector_cubic_self_overlap_moment_free_170 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) 1) :
    (∫q,∫sample,|vectorCenteredSelfOverlap (n:=n) μ β t ht.le q sample|^3
      ∂ vectorMeasureSpinPathLaw μ β t s ht.le ∂ parisiFreeMeasure μ s)≤
      z*(∫q,variance (vectorSelfOverlap (n:=n) μ β t ht.le q)
        (vectorMeasureSpinPathLaw μ β t s ht.le) ∂ parisiFreeMeasure μ s)+
      (170/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (2/z) :=by
  rw [←vectorIntegratedSelfOverlapCubic_eq_free_integral,
    ←vectorIntegratedSelfOverlapVariance_eq_free_integral hn]
  exact vector_cubic_self_overlap_moment_170 hn μ s β t hβ ht hs hμ hmin hM z hz


theorem vector_cubic_self_overlap_moment_free_425_from_full_layercake (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioc (0:ℝ) (1/2)) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (hM : 1≤(n:ℝ)*((1-t)*β^2)) (z : ℝ) (hz : z∈Ioc (0:ℝ) (1/4)) :
    (∫q,∫sample,|vectorCenteredSelfOverlap (n:=n) μ β t ht.le q sample|^3
      ∂ vectorMeasureSpinPathLaw μ β t s ht.le ∂ parisiFreeMeasure μ s)≤
      z*(∫q,variance (vectorSelfOverlap (n:=n) μ β t ht.le q)
        (vectorMeasureSpinPathLaw μ β t s ht.le) ∂ parisiFreeMeasure μ s)+
      (425/((n:ℝ)*((1-t)*β^2)*s))*Real.log (2*((n:ℝ)*((1-t)*β^2)))*Real.log (2/z) :=by
  rw [←vectorIntegratedSelfOverlapCubic_eq_free_integral,
    ←vectorIntegratedSelfOverlapVariance_eq_free_integral hn]
  exact vector_cubic_self_overlap_moment_425_from_full_layercake hn μ s β t hβ ht hs hμ hmin hM z hz


end HexagonPaper

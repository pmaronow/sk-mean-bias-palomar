module
public import QuantitativeFollowup.VectorCubicMoment

@[expose] public section

/-! Exact change-of-variables identification with the paper's free
Stieltjes measure integrals, including all atom masses. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem measurable_uncurry_vectorSelfOverlap (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (Function.uncurry (vectorSelfOverlap (n:=n) μ β t ht)):=by
  have hf:=measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht
  have hq : Measurable (fun p : Paper.Overlap×(VectorDisorderBrownianSample n×Configuration n)=>(p.1:ℝ)):=
    measurable_subtype_coe.comp measurable_fst
  convert hf.add hq using 1
  funext p
  simp only [Pi.add_apply,Function.uncurry,vectorCenteredSelfOverlap,sub_add_cancel]

theorem measurable_variance_vectorSelfOverlap (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    Measurable (fun q=>variance (vectorSelfOverlap (n:=n) μ β t ht q)
      (vectorMeasureSpinPathLaw μ β t a ht)):=by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  let : IsProbabilityMeasure J:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hf:=measurable_uncurry_vectorSelfOverlap (n:=n) μ β t ht
  have hmean : Measurable (fun q=>∫z,vectorSelfOverlap (n:=n) μ β t ht q z ∂J):=
    hf.stronglyMeasurable.integral_prod_right.measurable
  have hf2 : Measurable (Function.uncurry fun q z=>vectorSelfOverlap (n:=n) μ β t ht q z^2):=hf.pow_const 2
  have hsq : Measurable (fun q=>∫z,vectorSelfOverlap (n:=n) μ β t ht q z^2 ∂J):=
    hf2.stronglyMeasurable.integral_prod_right.measurable
  convert hsq.sub (hmean.pow_const 2) using 1
  funext q
  have hS : MemLp (vectorSelfOverlap (n:=n) μ β t ht q) 2 J:=
    MemLp.of_bound (measurable_vectorSelfOverlap μ β t ht q).aestronglyMeasurable 1
      (.of_forall fun z=>by rw [Real.norm_of_nonneg (vectorSelfOverlap_bounds hn μ β t ht q z).1];exact (vectorSelfOverlap_bounds hn μ β t ht q z).2)
  simpa only [Pi.pow_apply,Pi.sub_apply] using variance_eq_sub hS

theorem vectorIntegratedSelfOverlapCubic_eq_free_integral (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) :
    vectorIntegratedSelfOverlapCubic (n:=n) μ s β t ht=
      ∫q,∫z,|vectorCenteredSelfOverlap (n:=n) μ β t ht q z|^3
        ∂vectorMeasureSpinPathLaw μ β t s ht ∂parisiFreeMeasure μ s :=by
  let : IsProbabilityMeasure (vectorMeasureSpinPathLaw (n:=n) μ β t s ht):=
    vectorMeasureSpinPathLaw_probability (n:=n) μ β t s ht
  have hf : Measurable (Function.uncurry fun q z=>|vectorCenteredSelfOverlap (n:=n) μ β t ht q z|^3):=
    (measurable_uncurry_vectorCenteredSelfOverlap (n:=n) μ β t ht).abs.pow_const 3
  have hm : Measurable (fun q=>∫z,|vectorCenteredSelfOverlap (n:=n) μ β t ht q z|^3
      ∂ vectorMeasureSpinPathLaw μ β t s ht):=hf.stronglyMeasurable.integral_prod_right.measurable
  rw [integral_parisiFreeMeasure μ s _ hm,integral_Ioc_eq_integral_Ioo]
  rfl

theorem vectorIntegratedSelfOverlapVariance_eq_free_integral (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) :
    vectorIntegratedSelfOverlapVariance (n:=n) μ s β t ht=
      ∫q,variance (vectorSelfOverlap (n:=n) μ β t ht q)
        (vectorMeasureSpinPathLaw μ β t s ht) ∂parisiFreeMeasure μ s :=by
  rw [integral_parisiFreeMeasure μ s _ (measurable_variance_vectorSelfOverlap hn μ β t s ht),
    integral_Ioc_eq_integral_Ioo]
  rfl

theorem vector_cubic_self_overlap_moment_free (hn : 0<n) (μ : Paper.ParisiMeasure)
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
  exact vector_cubic_self_overlap_moment hn μ s β t hβ ht hs hμ hmin hM z hz

end QuantitativeFollowup

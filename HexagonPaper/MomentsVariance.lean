module
public import HexagonPaper.MomentsVarianceRange
public import QuantitativeFollowup.VectorQuantileIntervalVariance
public import FourPapersCommon.MonotoneEssentialDiameter

@[expose] public section

/-! Proposition 3.2 with its literal essential image diameter. The genuine
pair essential supremum supplies an interior range, and actual minimizing
contact turns the centered second moment into the physical variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper QuantitativeFollowup FourPapersCommon
open scoped NNReal ENNReal BigOperators
namespace HexagonPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_quantile_interval_variance_128 (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (I : Set ℝ) (hI : I.OrdConnected) (hDom : I⊆Ioo (0:ℝ) (1-s))
    (h u : ℝ) (hh : 0<h) (hlen : volume.real I=h) (hu : 0<u)
    (hThreshold : ∀ᵐw ∂volume.restrict I,u≤Paper.parisiCDF μ (parisiFreeQuantile μ s w)) :
    (∫v in I,variance (vectorSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
      (vectorMeasureSpinPathLaw μ β t s ht.le))≤
      128*(min h ((1/((n:ℝ)*((1-t)*β^2)*u))*(1+max (Real.log (h/(1/((n:ℝ)*((1-t)*β^2)*u)))) 0))+
        ((1/((n:ℝ)*((1-t)*β^2)*u))*parisiQuantileImageDiameter μ s I)^(2/3:ℝ)*h^(1/3:ℝ)) := by
  let f : ℝ→ℝ:=fun v=>(parisiFreeQuantile μ s v:ℝ)
  have hb : BddBelow I:=⟨0,fun v hv=>(hDom hv).1.le⟩
  have ha : BddAbove I:=⟨1-s,fun v hv=>(hDom hv).2.le⟩
  have hv : 0<volume.real I:=hlen.symm ▸hh
  obtain ⟨hell,a,hRange⟩:=monotone_essential_diameter_range f
    (fun _ _ h=>parisiFreeQuantile_monotone μ s h)
    (fun v=>(parisiFreeQuantile μ s v).property) I hI hb ha hv
  let J:=Ioo (sInf I) (sSup I)
  have hne : I.Nonempty:=by
    by_contra h
    have he : I=∅:=not_nonempty_iff_eq_empty.mp h
    simp only [he,measureReal_empty] at hv
    exact (lt_irrefl _ hv)
  have hin : J⊆I :=
    (show IsConnected I from ⟨hne,hI.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  have heq:=ordConnected_ae_eq_open_interval I hI hb ha
  have hJlen : volume.real J=h:=by
    rw [Measure.real,←measure_congr heq]
    exact hlen
  have hT:=hThreshold.filter_mono (ae_mono (Measure.restrict_mono_set volume hin))
  have h:=vector_quantile_second_range_bound_128 hn μ s β t hβ ht hs hμ hmin J ordConnected_Ioo
    (hin.trans hDom|>.trans Ioo_subset_Ioc_self) h a (intervalEssentialDiameter f I) u hh hJlen hell hu hRange hT
  have hContact : (∫v in I,variance (vectorSelfOverlap (n:=n) μ β t ht.le (parisiFreeQuantile μ s v))
      (vectorMeasureSpinPathLaw μ β t s ht.le))=
      ∫v in I,vectorCenteredSelfOverlapSecond (n:=n) μ β t s ht.le (parisiFreeQuantile μ s v) :=by
    apply setIntegral_congr_fun hI.measurableSet
    intro v hv
    exact (vectorCenteredSelfOverlapSecond_free_quantile_variance hn μ s β t hβ ht hs hμ hmin (hDom hv)).symm
  rw [hContact,setIntegral_congr_set heq]
  exact h

end HexagonPaper

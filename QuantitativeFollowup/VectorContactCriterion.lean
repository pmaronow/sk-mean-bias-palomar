module
public import QuantitativeFollowup.FreeMeasureContact
public import QuantitativeFollowup.VectorDeficitFirstVariation
public import QuantitativePaper.VectorMeasureMinimizer

@[expose] public section

/-! The actual vector functional is minimized on the root floor precisely
when its actual free measure is supported on global minima of its deficit.
Both directions use the proved actual first variation and convexity. -/
noncomputable section
open Set Filter MeasureTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
variable {n : ℕ}

theorem vector_minimum_iff_deficit_integral_minimum (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hμ : μ∈scalarFloor s)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a) :
    (∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a) ↔
    (∀ν∈scalarFloor s,
      (∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q∂(μ:Measure Paper.Overlap))≤
      ∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q∂(ν:Measure Paper.Overlap)) := by
  have hc : 0<((1-t)*β^2)/2:=by positivity
  constructor
  · intro hmin ν hν
    have hd:=hasDerivWithinAt_vectorMeasureFunctional_mix_deficit hn μ ν β t a hβ ht
    have hloc : Icc (0:ℝ) 1∈nhdsWithin 0 (Ioi (0:ℝ)) := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hr.le,hr1.le⟩
    have hpos:0≤((1-t)*β^2)/2*
        ((∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q∂(ν:Measure Paper.Overlap))-
          ∫q : Paper.Overlap,vectorOverlapDeficit (n:=n) μ β t a ht.le q∂(μ:Measure Paper.Overlap)) := by
      apply (Paper.convex_minimum_iff_right_deriv_nonneg
        (convexOn_vectorMeasureFunctional_mix n μ ν β t ht.le a ha)
        (hd.mono_of_mem_nhdsWithin hloc)).mp
      intro r hr
      simpa only [Paper.parisiMix_zero] using hmin _ (parisiMix_mem_scalarFloor hμ hν hr)
    nlinarith
  · intro hlinear ν hν
    have hh:=vectorMeasureFunctional_convex_deficit_bound hn μ ν β t a hβ ht ha
    have hb:=hlinear ν hν
    nlinarith

theorem vector_minimum_iff_free_support_argmin (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hs1 : s<1)
    (hμ : μ∈scalarFloor s) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (ha : 0≤a) :
    (∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t a≤vectorMeasureFunctional n ν β t a) ↔
      (parisiFreeMeasure μ s).support⊆
        Paper.overlapArgmin (fun q : Paper.Overlap=>vectorOverlapDeficit (n:=n) μ β t a ht.le q) := by
  rw [vector_minimum_iff_deficit_integral_minimum hn μ s hμ β t a hβ ht ha]
  exact constrained_integral_minimum_iff_free_support_argmin μ s hs hs1 hμ _
    ((continuous_vectorOverlapDeficit μ β t a ht.le).comp continuous_subtype_val)

theorem vector_minimizer_free_support_argmin (hn : 0<n) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (ha : a∈Ico (0:ℝ) 1) :
    (parisiFreeMeasure (vectorMeasureMinimizer n hn β t a ht.le ha.2.le) a).support⊆
      Paper.overlapArgmin (fun q : Paper.Overlap=>vectorOverlapDeficit (n:=n)
        (vectorMeasureMinimizer n hn β t a ht.le ha.2.le) β t a ht.le q) :=
  (vector_minimum_iff_free_support_argmin hn _ a ⟨ha.1,ha.2.le⟩ ha.2
    (vectorMeasureMinimizer_mem n hn β t a ht.le ha.2.le) β t a hβ ht ha.1).mp
      (vectorMeasureMinimizer_minimal n hn β t a ht.le ha.2.le)

end QuantitativeFollowup

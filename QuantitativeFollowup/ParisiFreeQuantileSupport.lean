module
public import QuantitativeFollowup.QuantileWindowSupport
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-! Every positive free-quantile level is in the genuine free-measure
support.  A positive interval of earlier quantile levels is mapped into
every neighborhood, so no atom-free or strict-CDF assumption is used. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem parisiFreeQuantile_nearby_level (μ : ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) {v : ℝ} (hv : v∈Ioc (0:ℝ) (1-s))
    {ε : ℝ} (hε : 0<ε) :
    ∃w₀ : ℝ,0≤w₀ ∧ w₀<v ∧ ∀w∈Ioc w₀ v,
      dist (parisiFreeQuantile μ s w) (parisiFreeQuantile μ s v)<ε := by
  let q:=parisiFreeQuantile μ s v
  by_cases hzero : (q:ℝ)=0
  · refine ⟨0,le_rfl,hv.1,?_⟩
    intro w hw
    have hle:=parisiFreeQuantile_monotone μ s hw.2
    have heq : parisiFreeQuantile μ s w=q := by
      apply Subtype.ext
      change (parisiFreeQuantile μ s w:ℝ)≤(q:ℝ) at hle
      rw [hzero] at hle
      exact le_antisymm (hle.trans (by rw [hzero])) (by rw [hzero];exact (parisiFreeQuantile μ s w).property.1)
    rw [heq,dist_self]
    exact hε
  · have hq : 0<(q:ℝ):=lt_of_le_of_ne q.property.1 (Ne.symm hzero)
    let y:=max 0 ((q:ℝ)-ε/2)
    have hyq : y<(q:ℝ):=max_lt hq (by linarith)
    have hy : y∈Icc (0:ℝ) 1:=⟨le_max_left _ _,hyq.le.trans q.property.2⟩
    have hlevel : s+v∈Icc (0:ℝ) 1:=⟨by linarith [hs.1,hv.1],by linarith [hv.2]⟩
    have hc : parisiCDF μ y<s+v := by
      apply lt_of_not_ge
      intro h
      have hle:=(parisiQuantile_le_iff μ (s+v) y hy).mpr (by
        simpa only [quantileLevel_eq hlevel] using h)
      exact (not_le.mpr hyq) hle
    let w₀:=max 0 (parisiCDF μ y-s)
    have hw₀ : w₀<v:=max_lt hv.1 (by linarith)
    refine ⟨w₀,le_max_left _ _,hw₀,?_⟩
    intro w hw
    have hwpos : 0<w:=(le_max_left (0:ℝ) (parisiCDF μ y-s)).trans_lt hw.1
    have hwlevel : s+w∈Icc (0:ℝ) 1:=⟨by linarith [hs.1],by linarith [hw.2,hv.2]⟩
    have hyw : y<(parisiFreeQuantile μ s w:ℝ) := by
      apply lt_of_not_ge
      intro h
      have hle:=(parisiQuantile_le_iff μ (s+w) y hy).mp h
      rw [quantileLevel_eq hwlevel] at hle
      have h:=le_max_right (0:ℝ) (parisiCDF μ y-s)
      have hlow:=hw.1
      dsimp only [w₀] at hlow
      linarith
    have hwq:=parisiFreeQuantile_monotone μ s hw.2
    have hwq' : (parisiFreeQuantile μ s w:ℝ)≤(q:ℝ):=hwq
    rw [Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hwq')]
    have h:=le_max_right (0:ℝ) ((q:ℝ)-ε/2)
    change -((parisiFreeQuantile μ s w:ℝ)-(q:ℝ))<ε
    linarith

theorem parisiFreeQuantile_mem_support (μ : ParisiMeasure) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) {v : ℝ} (hv : v∈Ioc (0:ℝ) (1-s)) :
    parisiFreeQuantile μ s v∈(parisiFreeMeasure μ s).support := by
  apply ((parisiFreeMeasure μ s).mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨ε,hε,hsub⟩:=Metric.mem_nhds_iff.mp hU
  obtain ⟨w₀,hw₀,hlt,hnear⟩:=parisiFreeQuantile_nearby_level μ s hs hv hε
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [←parisiFreeQuantile_map μ s,Measure.map_apply (parisiFreeQuantile_measurable μ s)
    Metric.isOpen_ball.measurableSet,
    Measure.restrict_apply ((parisiFreeQuantile_measurable μ s) Metric.isOpen_ball.measurableSet)]
  have hpositive : 0<volume (Ioc w₀ v) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt)
  apply lt_of_lt_of_le hpositive (measure_mono _)
  intro w hw
  exact ⟨hnear w hw,⟨hw₀.trans_lt hw.1,hw.2.trans hv.2⟩⟩

end QuantitativeFollowup

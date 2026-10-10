module
public import FourPapersCommon.WeakTimeRecovery
public import QuantitativeFollowup.ScalarTrialMeasure
public import FRSB.SupportDensityFormula

@[expose] public section

/-! The actual Parisi solution and all of its spatial derivatives satisfy
the pointwise time equation wherever the actual CDF is continuous. This is
recovered from its genuine distributional equation. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB
open scoped Topology ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 500000

theorem continuousAt_parisiTimeField_of_cdf (β : ℝ) (μ : Paper.ParisiMeasure)
    (j : ℕ) (t x : ℝ) (hc : ContinuousAt (parisiCDF μ) t) :
    ContinuousAt (parisiTimeField β μ j) (t,x) := by
  unfold parisiTimeField
  have hcF : ContinuousAt (fun p : ℝ×ℝ=>parisiCDF μ p.1) (t,x) :=
    ContinuousAt.comp (f:=Prod.fst) (g:=parisiCDF μ) (x:=(t,x))
      hc (continuous_fst.continuousAt (x:=(t,x)))
  exact continuousAt_const.mul ((continuous_parisiSpatialField β μ (j+2)).continuousAt.add
    (hcF.mul
      (continuous_parisiSquareSpatialField β μ j).continuousAt))

theorem hasDerivAt_parisiSpatialField_time_of_cdf (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (j : ℕ) (t x : ℝ) (ht : t∈Ioo (0:ℝ) 1)
    (hc : ContinuousAt (parisiCDF μ) t) :
    HasDerivAt (fun s=>parisiSpatialField β μ j (s,x)) (parisiTimeField β μ j (t,x)) t :=
  FourPapersCommon.hasDerivAt_time_of_weak_continuousAt _ _
    (continuous_parisiSpatialField β μ j)
    (isParisiWeakTimeDerivative_spatialField β hβ μ j)
    (measurable_parisiTimeField β μ j) t x ht
    (continuousAt_parisiTimeField_of_cdf β μ j t x hc)

theorem parisiTimeField_interval_integral (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (j : ℕ) (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hc : ∀t∈Ioo a b,ContinuousAt (parisiCDF μ) t) (x : ℝ) :
    (∫s in a..b,parisiTimeField β μ j (s,x))=
      parisiSpatialField β μ j (b,x)-parisiSpatialField β μ j (a,x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
  · exact ((continuous_parisiSpatialField β μ j).comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro s hs
    exact hasDerivAt_parisiSpatialField_time_of_cdf β hβ μ j s x
      ⟨ha.trans_lt hs.1,hs.2.trans_le hb⟩ (hc s hs)
  · obtain ⟨M,hM⟩:=parisiTimeField_bounded β μ j
    apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (a:=a) (b:=b) (c:=M))
      ((measurable_parisiTimeField β μ j).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact .of_forall fun s=>hM (s,x)

theorem continuousAt_minimizer_cdf_on_support (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) q) : ContinuousAt (parisiCDF μ) t := by
  have he : parisiCDF μ=ᶠ[𝓝 t] momentQuotient β μ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq.1
      hq.2.le hsupp s ⟨hs.1.le,hs.2⟩
  exact ((moments_contDiffOn_on_support_interval β hβ μ hmin q hq.1 hq.2.le hsupp).2.continuousOn
    |>.continuousAt (Icc_mem_nhds ht.1 ht.2)).congr he.symm

theorem continuousAt_clipped_cdf_on_support (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (t : ℝ) (ht : t∈Ioo (0:ℝ) q) :
    ContinuousAt (parisiCDF (scalarClippedTrialMeasure s hs μ)) t := by
  have he : parisiCDF (scalarClippedTrialMeasure s hs μ)=ᶠ[𝓝 t]
      (fun r=>max s (parisiCDF μ r)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact scalarClippedTrialMeasure_cdf s hs μ r ⟨hr.1.le,hr.2.le.trans hq.2.le⟩
  have hh : ContinuousAt (fun r=>max s (parisiCDF μ r)) t :=
    continuousAt_const.max (continuousAt_minimizer_cdf_on_support β hβ μ hmin q hq hsupp t ht)
  exact hh.congr_of_eventuallyEq he

end QuantitativeFollowup

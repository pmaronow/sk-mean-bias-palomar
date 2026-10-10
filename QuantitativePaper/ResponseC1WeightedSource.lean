module
public import QuantitativePaper.ResponseMidpointGreen

@[expose] public section

/-! A genuine closed-interval product rule for integrable sources with
continuous interior values. It permits C¹ time tests, including quartic
localization bumps, without replacing them by polynomial tests. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem response_hasDerivAt_of_interval_source (R H : ℝ→ℝ) (a b : ℝ)
    (hab : a≤b) (hH : IntervalIntegrable H volume a b)
    (hc : ContinuousOn H (Ioo a b))
    (he : ∀q∈Icc a b,R q-R a=∫r in a..q,H r)
    (q : ℝ) (hq : q∈Ioo a b) : HasDerivAt R (H q) q:=by
  have hi : IntervalIntegrable H volume a q:=hH.mono_set (by
    rw [uIcc_of_le hab,uIcc_of_le hq.1.le]
    exact Icc_subset_Icc_right hq.2.le)
  have hm : StronglyMeasurableAtFilter H (nhds q) volume:=by
    have hh:=hc.stronglyMeasurableAtFilter_nhdsWithin (μ:=volume) measurableSet_Ioo q
    rwa [nhdsWithin_eq_nhds.2 (isOpen_Ioo.mem_nhds hq)] at hh
  have hd:=(intervalIntegral.integral_hasDerivAt_right hi hm
    (hc.continuousAt (isOpen_Ioo.mem_nhds hq))).const_add (R a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hq] with r hr
  linarith [he r ⟨hr.1.le,hr.2.le⟩]

theorem response_C1_tested_interval (R H w w₁ : ℝ→ℝ) (a b : ℝ)
    (hab : a≤b) (hR : ContinuousOn R (Icc a b))
    (hH : IntervalIntegrable H volume a b) (hc : ContinuousOn H (Ioo a b))
    (he : ∀q∈Icc a b,R q-R a=∫r in a..q,H r)
    (hw : ContinuousOn w (Icc a b)) (hw₁ : ContinuousOn w₁ (Icc a b))
    (hwd : ∀q∈Ioo a b,HasDerivAt w (w₁ q) q) :
    w b*R b-w a*R a=∫q in a..b,w₁ q*R q+w q*H q:=by
  have hi : IntervalIntegrable (fun q=>w₁ q*R q+w q*H q) volume a b:=by
    exact ((show ContinuousOn (fun q=>w₁ q*R q) (uIcc a b) by
      rw [uIcc_of_le hab]
      intro q hq
      exact (hw₁ q hq).mul (hR q hq)).intervalIntegrable).add
      (hH.continuousOn_mul (by simpa only [uIcc_of_le hab] using hw))
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hw.mul hR) _ hi
  intro q hq
  exact (hwd q hq).mul (response_hasDerivAt_of_interval_source R H a b hab hH hc he q hq)

end QuantitativePaper

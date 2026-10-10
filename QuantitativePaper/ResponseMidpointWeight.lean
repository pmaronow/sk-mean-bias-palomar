module
public import QuantitativePaper.ResponseFatou
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Exact midpoint Green weight on the full interval and on its middle
part. All endpoint and indicator conversions use the actual Lebesgue measure. -/
noncomputable section
open MeasureTheory Set
namespace QuantitativePaper
set_option maxHeartbeats 1400000

def responseMidpointLowerDensity (a C : ℝ) : ℝ→ℝ:=
  (Ioo a (1-a)).indicator (fun θ=>min θ (1-θ)*C)

theorem response_midpoint_weight_integral_cropped (a : ℝ) (ha : 0≤a) (ham : a≤1/2) :
    (∫θ in a..(1-a),min θ (1-θ))=1/4-a^2:=by
  have hr : 1/2≤1-a:=by linarith
  have hw : Continuous (fun θ : ℝ=>min θ (1-θ)):=
    continuous_id.min (continuous_const.sub continuous_id)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hw.intervalIntegrable a (1/2))
    (hw.intervalIntegrable (1/2) (1-a))]
  have hL : (∫θ in a..(1/2),min θ (1-θ))=∫θ in a..(1/2),θ:=by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)=θ
    rw [uIcc_of_le ham] at hθ
    exact min_eq_left (by linarith [hθ.2])
  have hR : (∫θ in (1/2)..(1-a),min θ (1-θ))=∫θ in (1/2)..(1-a),1-θ:=by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change min θ (1-θ)=1-θ
    rw [uIcc_of_le hr] at hθ
    exact min_eq_right (by linarith [hθ.1])
  rw [hL,hR]
  have he : (∫θ in (1/2)..(1-a),(1:ℝ)-θ)=
      (∫θ in (1/2)..(1-a),(1:ℝ))-(∫θ in (1/2)..(1-a),θ):=
    intervalIntegral.integral_sub (f:=fun _:ℝ=>1) (g:=fun θ:ℝ=>θ)
      intervalIntegrable_const (continuous_id.intervalIntegrable _ _)
  rw [he]
  rw [integral_id,integral_id,intervalIntegral.integral_const]
  simp only [smul_eq_mul,mul_one]
  ring

theorem integrable_responseMidpointLowerDensity (a C : ℝ) (ha : 0≤a) :
    Integrable (responseMidpointLowerDensity a C) (volume.restrict (Ioc (0:ℝ) 1)):=by
  have hbase : Integrable (fun θ : ℝ=>min θ (1-θ)*C) (volume.restrict (Ioc (0:ℝ) 1)):=
    ((continuous_id.min (continuous_const.sub continuous_id)).mul continuous_const).continuousOn.integrableOn_Icc.mono_set
      (show Ioc (0:ℝ) 1⊆Icc (0:ℝ) 1 from Ioc_subset_Icc_self)
  exact hbase.indicator measurableSet_Ioo

theorem integral_responseMidpointLowerDensity (a C : ℝ) (ha : 0≤a) (ham : a≤1/2) :
    (∫θ,responseMidpointLowerDensity a C θ∂volume.restrict (Ioc (0:ℝ) 1))=
      C*(1/4-a^2):=by
  have hsub : Ioo a (1-a)⊆Ioc (0:ℝ) 1:=by
    intro θ hθ
    exact ⟨ha.trans_lt hθ.1,by linarith [hθ.2]⟩
  unfold responseMidpointLowerDensity
  rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr hsub,Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : a≤1-a),intervalIntegral.integral_mul_const,
    response_midpoint_weight_integral_cropped a ha ham]
  ring

end QuantitativePaper
